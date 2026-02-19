import Lean.Compiler.LCNF.ToLCNF
import Lean.Meta

import LeanToLambdaBox.Basic
import LeanToLambdaBox.Printing
import Std.Data

open Lean
open Lean.Compiler.LCNF

namespace Erasure

inductive ConstructorArgRelevance where
  | erase
  | keep
deriving Repr, BEq

/-- Used to reindex constructor arguments for removal of irrelevant fields. -/
abbrev ConstructorArgMask := Array ConstructorArgRelevance
abbrev InductiveArgMasks := List ConstructorArgMask

def filter (mask: ConstructorArgMask) (arr: Array α): Array α :=
  mask.zip arr |>.filterMap (fun (r, a) => match r with | .erase => .none | .keep => .some a)
/--
State carried by EraseM to handle constants and inductive types registered in the global environment.
-/
structure ErasureState: Type where
  inductives: Std.HashMap Name (InductiveId × InductiveArgMasks) := ∅
  constants: Std.HashMap Name Kername := ∅
  /-- This field is only updated, not read. -/
  gdecls: GlobalDeclarations := []
  inlinings: List Kername := []

namespace Config

/--
How to handle functions with the @[extern] attribute.
Notably, this includes `Nat.add` et al., but also some constructors such as those of `Int`.
-/
inductive Extern where
  /-- If a Lean definition is present, use that one. -/
  | preferLogical
  /-- Ignore any Lean definitions and always treat as an axiom to be provided OCaml-side. -/
  | preferAxiom
deriving BEq

/-- How to handle literals and constructors of `Nat`. -/
inductive Nat
  /-- Keep Nat as an inductive type and represent literals by using constructors. -/
  | peano
  /--
  Turn Nat literals into lambdabox primitive i63 (panic on overflow),
  translate .zero into literal 0 and .succ x into x + literal 1.
  For this to work, config.extern must be set to .preferAxiom, so that
  the usual functions on `Nat` (addition, multiplication etc) are treated as axioms
  (and implemented by Zarith functions linked with the .cmx file from extraction),
  instead of using the logical implementation in Lean.
  -/
  | machine

end Config

structure ErasureConfig: Type where
  extern: Config.Extern := .preferAxiom
  nat: Config.Nat := .machine
  /-- Whether to perform csimp replacements before erasure. -/
  csimp: Bool := true
  /-- Whether to remove irrelevant arguments from constructors. -/
  remove_irrel_constr_args: Bool := false

structure ErasureContext: Type where
  lctx: LocalContext := {}
  fixvars: Option (Std.HashMap Name FVarId) := .none
  config: ErasureConfig

/-- The monad in ToLCNF has caches, a local context and toAny as a set of fvars, all as mutable state for some reason.
    Here I just have a read-only local context, in order to be able to use MetaM's type inference, and keep the code complexity low.
    If this is much too slow, try caching stuff again.

    Above the local context there is also a state handling the global environment of the extracted program.
    -/
abbrev EraseM := StateT ErasureState <| ReaderT ErasureContext CoreM

def run (x : EraseM α) (config: ErasureConfig): CoreM (α × ErasureState) :=
  x |>.run {} |>.run { config }

/-- Run an action of MetaM in EraseM using EraseM's local context of Lean types. -/
@[inline] def liftMetaM (x : MetaM α) : EraseM α := do
  x.run' { lctx := (← read).lctx }

/--
TODO: The function ToLCNF.isTypeFormerType has an auxiliary function "quick"
which I removed here because I didn't understand why it was correct.
Maybe putting it back makes things faster.
-/
def isErasable (e : Expr) : MetaM Bool := do
    let type ← Meta.inferType e
    -- Erase evidence of propositions
    -- ToLCNF includes an explicit check for isLcProof, but I think the type information should be enough to erase those here.
    if (← Meta.isProp type) then
      return true
    -- Erase types and type formers
    if (← Meta.isTypeFormerType type) then
      return true
    return false

def addAxiom (name: Name): EraseM Unit := do
  if (← get).constants.contains name then panic! s!"Constant {name} is already defined, cannot add axiom."
  let kn := toKername name
  modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .constantDecl ⟨.none⟩) })

/--
Get information about the inductive type, adding all its mutually-defined buddies to the context if necessary.
-/
def register_inductive (indinfo: InductiveVal): EraseM (InductiveId × InductiveArgMasks) := do
  if let .some iid := (← get).inductives.get? indinfo.name then
    return iid
  else
    let names := indinfo.all
    let mutualBlockName := indinfo.all |>.map toString |> String.join |> rootKername
    -- Iterate through all the inductive types in the mutual definition
    let ind_bodies: List OneInductiveBody ← names.zipIdx.mapM fun (ind_name, idx) => do
      let .inductInfo inf ← getConstInfo ind_name | unreachable!
      -- Iterate through all the constructors
      let (ind_ctors, ind_argmasks) := List.unzip (← inf.ctors.mapM fun ctor_name => do
        if isExtern (← getEnv) ctor_name && (← read).config.extern == .preferAxiom then
          logInfo "Constructor {ctor_name} of type {ind_name} is marked @[extern], emitting axiom."
          addAxiom ctor_name
        let .ctorInfo ci ← getConstInfo ctor_name | unreachable!
        -- Get an argmask to remember which fields are irrelevant.
        let argmask: ConstructorArgMask ← if (← read).config.remove_irrel_constr_args
        then
          liftMetaM <| Meta.forallBoundedTelescope ci.type (.some <| ci.numParams + ci.numFields) fun vars _ =>
            let fields := vars[ci.numParams:].toArray
            let fields := if fields.size != ci.numFields
            then panic! "unexpected field count"
            else fields
            do
            let mask: ConstructorArgMask ← fields.mapM fun v => do
              if ← isErasable v then pure .erase else pure .keep
            if (mask.any (· == .erase)) then logInfo s!"Argmask for constructor {ctor_name}: {repr mask}"
            pure mask
        else
          pure <| Array.replicate ci.numFields .keep
        let nargs := Array.count .keep argmask
        pure ({ name := toString ctor_name, nargs }, argmask)
      )
      -- If the type is a structure, add definitions for projections.
      let is_struct := names.length == 1 && inf.ctors.length == 1 && !inf.isRec
      let projs: List projection_body ←
        if is_struct then
          -- only generate projections for relevant fields
          let _ := Expr
          let num_fields := ind_argmasks[0]!.count .keep
          -- These dummy names aren't semantically important, so it doesn't actually matter whether the index refers to
          -- the field's position before or after removing irrelevant fields. Here, I chose the latter, because it was easier.
          pure (List.range num_fields |>.map toString |>.map ProjectionBody.mk)
        else
          pure []

      let ind_id: InductiveId := { mutualBlockName, idx }
      modify (fun s => { s with inductives := s.inductives.insert ind_name (ind_id, ind_argmasks)})
      pure { name := toString ind_name, ctors := ind_ctors, projs }
    let mutual_body := { npars := indinfo.numParams, bodies := ind_bodies }
    modify (fun s => { s with gdecls := s.gdecls.cons (mutualBlockName, .inductiveDecl mutual_body) })
    return (← get).inductives[indinfo.name]!

def fvar_to_name (x: FVarId): EraseM BinderName := do
  let n := (← read).lctx.fvarIdToDecl |>.find! x |>.userName
  let s: String := n.toString
  -- check if s is ASCII graphic, otherwise the λbox parser will complain
  if s.all (fun c => 33 <= c.toNat /\ c.toNat < 127) then
    return .named n.toString
  else
    return .anon

def mkLambda (x: FVarId) (body: LBTerm): EraseM LBTerm := do return .lambda (← fvar_to_name x) (abstract x body)

def mkLetIn (x: FVarId) (val body: LBTerm): EraseM LBTerm := do return .letIn (← fvar_to_name x) val (abstract x body)

/-- The order of variables here is what it is because the other way around led to segfaults. -/
def mkAlt (xs: List FVarId) (body: LBTerm): EraseM (List BinderName × LBTerm) := do
  let mut body := body
  let names ← xs.mapM fvar_to_name
  for (fvarid, i) in xs.reverse.zipIdx do
    body := toBvar fvarid i body
  return (names, body)

/-
def mkCase (indInfo: InductiveVal) (discr: LBTerm) (alts: List (List ppname × LBTerm)): EraseM LBTerm := do
  let (indid, _) ←  register_inductive indInfo
  return .case (indid, indInfo.numParams) discr alts
-/

/-- Check binding order here as well, may be wrong. -/
def mkDef (name: Name) (fixvarnames: List Name) (body: LBTerm): EraseM (@FixDef LBTerm) := do
  let mut body := body
  for (n, i) in fixvarnames.reverse.zipIdx do
    body := toBvar ((← read).fixvars.get![n]!) i body
  return { name := .named name.toString, body }

/-- Similar to Meta.withLocalDecl, but in EraseM.
    k will be passed some fresh FVarId and run in a context in which it is bound. -/
def withLocalDecl (n: Name) (type: Expr) (bi: BinderInfo) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLocalDecl fvarid n type bi }) (k fvarid)

/-- Like Meta.withLetDecl. -/
def withLocalDef (n: Name) (type val: Expr) (nd: Bool) (k: FVarId -> EraseM α): EraseM α := do
  let fvarid <- mkFreshFVarId;
  withReader (fun ctx => { ctx with lctx := ctx.lctx.mkLetDecl fvarid n type val nd }) (k fvarid)

/--
A version of Meta.lambdaTelescope that
- unpacks exactly one layer of lambda-abstraction (ie does not telescope)
- works in EraseM instead of (any monad from which we can control) MetaM.
- yields an FVarId instead of an Expr for the bound variable
Panics if applied to something which is not of the form .lambda ..
-/
def lambdaMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> EraseM α): EraseM α := do
  let .lam binderName type body bi := e | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate1 (.fvar fvarid))

/--
Destructures a let-expression for handling by a continuation in an appropriate context.
The continuation gets an FVarId for the bound variable and bound value and body as expressions.
Panics if applied to an expression which is not of the form .letE ..
-/
def letMonocular {α} [Inhabited α] (e: Expr) (k: FVarId -> Expr -> Expr -> EraseM α): EraseM α := do
  let .letE binderName type val body nd := e | unreachable!
  withLocalDef binderName type val nd (fun fvarid => k fvarid val (body.instantiate1 (.fvar fvarid)))

/--
Destructures a type expression of the form `∀ a: A, B`,
running the continuation on the body B (with DB variable 0 suitably instantiated with some fvar `a`) and the bound fvar,
in a context with `a: A`.
Panics if applied to an expression which is not of the form .forallE ..
-/
def forallMonocular {α} [Inhabited α] (t: Expr) (k: FVarId -> Expr -> EraseM α) := do
  let Expr.forallE binderName type body bi := t | unreachable!
  withLocalDecl binderName type bi (fun fvarid => k fvarid <| body.instantiate1 <| .fvar fvarid)

/--
Given an expression `e` and its type, which is assumed to be of the form `∀ a:A, B`,
run a continuation `k` in a context where a fvar `a` has type `A`.
- if `e` is `fun a: A => body`, `k` will be run on the expression `body` directly.
- if `e` is not of this form, `k` will be run on the expression `.app e (.fvar a)`, behaving as if `e` had been eta-expanded to `fun a => e a`.
In both cases the second argument to `k` is `B`, the type of the first argument in the new context.
Assumes that `type` is the type of `e` in the context where it is called.
Panics if `type` is not a function type.
-/
def lambdaMonocularOrIntro {α} [Inhabited α] (e type: Expr) (k: Expr -> Expr -> FVarId -> EraseM α): EraseM α :=
  forallMonocular type fun fvarid bodytype => do
    if let .lam _ _ body _ := e then
      /-
      Here I use the binder name and info from the type-level forall binder we are under.
      It might be better to get it from the lambda binder.
      -/
      k (body.instantiate1 <| .fvar fvarid) bodytype fvarid
    else
      -- Here in any case I must use the binder name and info from the forall binder.
      k (.app e (.fvar fvarid)) bodytype fvarid

/--
Given an expression `e` and its type, which is assumed to start with at least `arity` `∀` quantifiers,
get the body of `e` after application to `arity` arguments.
For example, if `e` is `fun a b => asdf` with type `A -> B -> C -> D`, applying `lambdaOrIntroToArity 3`
will run the continuation in the context `a: A, b: B, c: C` on the expression `.app asdf (.fvar c)`
with the fvars `#[a, b, c]`.
I think I got the order of fvars right but thinking about continuations is hard.
Writing the code in this way is suboptimal; there is a first phase in which we only descend through lambdas
and a second phase in which we descend the remaining distance through the type by appending fvars,
but here we check whether there is a lambda to go under each time.
This is probably easily fixable using something like lambdaBoundedTelescope.
-/
def lambdaOrIntroToArity {α} [Inhabited α] (e type: Expr) (arity: Nat) (k: Expr -> List FVarId -> EraseM α): EraseM α :=
  match arity with
  | 0 => k e []
  | n+1 => lambdaMonocularOrIntro e type fun body bodytype fvarid =>
      lambdaOrIntroToArity body bodytype n (fun e fvarids => k e (.cons fvarid fvarids))

/--
Given an expression, deconstruct it into an application to at least arity arguments,
then build a LBTerm from it given the continuation.
This will eta-expand if necessary, and close the lambdas after running `k`.
For example: withAppEtaToMinArity "Nat.add 42" 2 k = mkLambda "y" (k "Nat.add" ["42", "y"])
Panics if the type of e does not start with at least arity .forallE constructors.
-/
partial def withAppEtaToMinArity (e: Expr) (arity: Nat) (k: Expr -> Array Expr -> EraseM LBTerm): EraseM LBTerm := do
  let type ← liftMetaM do Meta.inferType e
  e.withApp (fun f args => go type f args)
where
  -- Invariant: type is the type of f *args.
  go (type f: Expr) (args: Array Expr): EraseM LBTerm :=
    if args.size >= arity then
      k f args
    else
      forallMonocular type fun fvarid bodytype => do
        let res ← go bodytype f (args.push (.fvar fvarid))
        mkLambda fvarid res

/-- Remove the ._unsafe_rec suffix from a Name if it is present. -/
def remove_unsafe_rec (n: Name): Name := Compiler.isUnsafeRecName? n |>.getD n

/--
This is used to detect if a definition is recursive.
Occurrences of `name` in types may or may not be detected, but I don't think this matters in practice.
-/
def name_occurs (name: Name) (e: Expr): Bool :=
  match e with
  | .const n' .. => name == remove_unsafe_rec n'
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .forallE .. /- these are types, so ignoring -/ | .lit .. => .false
  | .lam _ _ e _ | .mdata _ e | .proj _ _ e => name_occurs name e
  | .app a b | .letE _ _ a b _ => name_occurs name a || name_occurs name b

/--
Replace nested occurrences of `unsafeRec` names with the safe ones.
Copied over from ToDecl.lean because it is private there.
I think this doesn't actually need to be in CoreM and could just use `Expr.replace`.
-/
def replaceUnsafeRecNames (value : Expr) : CoreM Expr :=
  Core.transform value fun e =>
    match e with
    | .const declName us =>
      if let some safeDeclName := Compiler.isUnsafeRecName? declName then
        return .done (.const safeDeclName us)
      else
        return .done e
    | _ => return .continue

/--
Honor @[macro_inline] directives, inline auxiliary matchers, remove _unsafe_rec suffixes and perform csimp replacements.
This is lifted from LCNF/ToDecl.lean .
It processes the whole expression tree, so the code here doesn't have to be at the start of visitExpr,
and it is sufficient to run it before entering the "toplevel" expression and the definition of a dependency in the environment.

This may make the expression ill-typed if some dependent type relies on the implementation of functions affected by csimp.
-/
def prepare_erasure (e: Expr): EraseM Expr := do
  let mut e := e
  e ← replaceUnsafeRecNames e
  e ← macroInline e
  e ← inlineMatchers e
  -- According to the comment in ToDecl.lean, inlined matchers might contain occurrences of `ite` and `dite`.
  -- I'm sort of assuming that inlining matchers doesn't expose arbitrary macro_inline stuff which might itself contain more matchers etc.
  -- Just `ite` and `dite` are fine, their bodies are just a Decidable.casesOn.
  -- It's important to inline them because otherwise both arms of the conditional will be strictly evaluated.
  e ← macroInline e
  if (← read).config.csimp then
    -- This has to be done after _unsafe_rec name replacement.
    e := Compiler.CSimp.replaceConstants (← getEnv) e
  pure e

/--
Copied over from toLCNF, then quite heavily pruned and modified.

This not only erases the expression but also gives a context with all necessary global declarations of inductive types and top-level constants.
-/
partial def erase (e : Expr) (config: ErasureConfig): CoreM (Program × List Kername) := do
  let (t, s) ← run (do visitExpr (← prepare_erasure e)) config
  return (.untyped s.gdecls (.some t), s.inlinings)

where
  /- Proofs (terms whose type is of type Prop) and type formers/predicates are all erased. -/
  visitExpr (e : Expr) : EraseM LBTerm := do
    if (← liftMetaM <| isErasable e) then
      return .box
    match e with
    | .app ..      => visitApp e
    | .const ..    => visitApp e -- treat as an application to zero args to handle special constants
    | .proj s i e  => visitProj s i e
    | .mdata _ e   => visitExpr e -- metadata is ignored
    | .lam ..      => visitLambda e
    | .letE ..     => visitLet e
    | .lit l     => visitLiteral l
    | .fvar fvarId => pure (.fvar fvarId)
    | .forallE .. | .mvar .. | .bvar .. | .sort ..  => unreachable!

  visitLiteral (l: Literal): EraseM LBTerm := do
    match (← read).config.nat, l with
    | .peano, .natVal 0 => visitConstructor ``Nat.zero #[]
    | .peano, .natVal (n+1) => visitConstructor ``Nat.succ #[.lit (.natVal n)]
    | .machine, .natVal n =>
      if n <= BitVec.intMax 63 then
        pure <| .prim ⟨.primInt, n⟩
      else
        panic! "Nat literal not representable as a 63-bit signed integer."
    | _, .strVal _ => panic! "String literals not supported."

  /-
  The original in ToLCNF also handles eta-reduction of implicit lambdas introduced by the elaborator.
  This is beyond the scope of what I want to do here for the moment.
  -/
  visitLambda (e : Expr) : EraseM LBTerm :=
    lambdaMonocular e (fun fvarid body => do mkLambda fvarid (← visitExpr body))

  visitLet (e : Expr): EraseM LBTerm :=
    /-
    In the original ToLCNF, if the bound value is erasable then the let-binding is not generated,
    since all occurrences of the variable must be erased anyway.
    Keep this optimization?
    -/
    letMonocular e (fun fvarid val body => do mkLetIn fvarid (← visitExpr val) (← visitExpr body))

  visitProj (s : Name) (i : Nat) (e : Expr) : EraseM LBTerm := do
    let .inductInfo indinfo ← getConstInfo s | unreachable!
    let (indid, argmasks) ← register_inductive indinfo
    -- i is the index among all fields, but some are erased
    let fieldIdx := argmasks[0]![:i].toArray.count .keep
    let projinfo: ProjectionInfo := { indType := indid, paramCount := indinfo.numParams, fieldIdx }
    return .proj projinfo (← visitExpr e)

  /--
  When visiting expressions of the form f g, it is not sufficient to just recurse on f and g.
  visitApp will explore an expression "in depth" to get the leftmost applicand,
  then handle the case where it is a constant specially; otherwise, straightforward recursion is correct.
  Contrary to the original ToLCNF, I have removed CSimp.replaceConstants here and assume it will just be run once before erasure.
  -/
  visitApp (e : Expr) : EraseM LBTerm :=
    -- The applicand is a constant, check for special cases
    if let .const .. := e.getAppFn then
      visitConstApp e
    -- The applicand is not a constant, so we just normally recurse.
    else
      e.withApp fun f args => do visitAppArgs (← visitExpr f) args

  /-- A constant which is being defined in the current mutual block will be replaced with a free variable (to be bound by mkDef later).
  Other constants should previously have been added to the (λbox-side) context and will just be translated to Rocq kernames. -/
  visitConst (e: Expr): EraseM LBTerm := do
    let .const declName _ := e | unreachable!
    if let .some id := (← read).fixvars.bind (fun hmap => hmap[declName]?) then
      return .fvar id
    return .const (← get_constant_kername declName)

  /--
  Special handling of
  - casesOn (will be eta-expanded)
  - constructors (will be eta-expanded)
  -/
  visitConstApp (e: Expr): EraseM LBTerm :=
    e.withApp fun f args => do
      let .const declName _ := f | unreachable!
      if let some casesInfo ← getCasesInfo? declName then
        /-
        I have removed the check for whether there is an [implemented_by] annotation.
        This is only relevant for the implementation of computed fields, such as for hash consing in the `Expr` type.
        -/
        withAppEtaToMinArity e casesInfo.arity (fun _ args => visitCases casesInfo args)
      else if let some arity ← getCtorArity? declName then
        withAppEtaToMinArity e arity (fun _ args => visitConstructor declName args)
      /-
      Removed special check for automatically defined projection functions out of structures.
      In toLCNF these are inlined and β-reduced, unless the projection is out of a builtin type of the runtime.
      The definition seems to just be def spam.egg := fun s: spam => s.1,
      so after β-reduction this becomes a primitive projection.
      Left these to be inlined by Malfunction.
      -/
      else
        visitAppArgs (← visitConst f) args

  visitConstructor (ctorname: Name) (args: Array Expr): EraseM LBTerm := do
    let .ctorInfo info ← getConstInfo ctorname | unreachable!
    let cidx := info.cidx
    let .inductInfo indinfo ← getConstInfo info.induct | unreachable!
    let (indid, argmasks) ← register_inductive indinfo
    let argmask := argmasks[cidx]!

    if isExtern (← getEnv) ctorname && (← read).config.extern == .preferAxiom then
      -- Axiom has been added by register_inductive.
      return ← visitAppArgs (.const <| toKername ctorname) args

    match (← read).config.nat, ctorname with
    | .machine, ``Nat.zero =>
      unless args.size == 0 do
        panic s!"Nat.zero applied to {args.size} arguments."
      return ← visitLiteral (.natVal 0)
    | .machine, ``Nat.succ =>
      unless args.size == 1 do
        panic s!"Nat.succ applied to {args.size} arguments."
      let nat_add ← visitConst (.const ``Nat.add [])
      return ← visitAppArgs nat_add #[args[0]!, .lit (.natVal 1)]
    | .machine, _
    | .peano, _ => pure ()

    let param_args := args[:info.numParams]
    let field_args := args[info.numParams:info.numParams + info.numFields]
    let extra_args := args[info.numParams + info.numFields:]
    let filtered_args := param_args.toArray ++ (filter argmask field_args) ++ extra_args.toArray
    -- Instead of making this a "real" use of .construct, in the stage of λbox I am targeting constructor application is function application
    visitAppArgs (.construct indid cidx []) filtered_args

  /-- Normal application of a function to some arguments. -/
  visitAppArgs (f : LBTerm) (args : Array Expr) : EraseM LBTerm := do
      args.foldlM (fun e arg => do return LBTerm.app e (← visitExpr arg)) f

  visitCases (casesInfo : CasesInfo) (args: Array Expr) : EraseM LBTerm := do
    let discr_nt ← visitExpr args[casesInfo.discrPos]!
    let typeName := casesInfo.declName.getPrefix

    -- If we are using machine Nats then the inductive casesOn will not work.
    let mut ret: LBTerm ← (match typeName, (← read).config.nat with
    | ``Nat, .machine => do
      /-
      Compile this to "let n = discr in Bool.casesOn (Nat.beq n 0) (succ_case (n - 1)) zero_case".
      The let-binding is necessary to avoid double evaluation of the discriminee.
      I'm doing part of this this on LBTerms instead of constructing Exprs because visitExpr
      assumes expressions are well-typed, which wouldn't be the case naïvely as (n - 1).succ is not defeq to n.
      Using casts to make the dependent types typecheck would be an option now that Eq.rec is added to the axioms.
      -/
      let zero_arm := args[casesInfo.altsRange.start]!
      let zero_nt ← visitExpr zero_arm
      let succ_arm := args[casesInfo.altsRange.start + 1]! -- a function with one argument of type Nat
      let bool_indval := (← getConstInfo ``Bool).inductiveVal!
      let (bool_indid, _) ← register_inductive bool_indval
      withLocalDecl `n (.const ``Nat []) .default (fun n_fvar => do
        let gtz_arm := Expr.app succ_arm <| mkAppN (.const ``Nat.sub []) #[.fvar n_fvar, .lit (.natVal 1)] -- no longer takes an argument, n_fvar is free here
        let gtz_nt: LBTerm ← visitExpr gtz_arm
        let condition: LBTerm ← visitExpr <| mkAppN (.const ``Nat.beq []) #[.fvar n_fvar, .lit (.natVal 0)]
        let case_nt: LBTerm := .case (bool_indid, 0) condition [← mkAlt [] gtz_nt, ← mkAlt [] zero_nt]
        mkLetIn n_fvar discr_nt case_nt
      )
    | ``Int, .machine => do
      /-
      Compile this to "let n = discr in Bool.casesOn (Nat.ble 0 n) (negsucc_case (-(n+1))) (ofnat_case n)".
      The use of Nat.ble instead of using Int.decLE and Decidable.casesOn is possible because Int and Nat both become Z.t,
      and Nat.ble becomes Z.leq.
      We build `LBTerm`s directly instead of building expressions and using visitExpr because visitExpr assumes typability.
      In effect, we can silently cast between Int and Nat.
      -/
      let ofnat_fun := args[casesInfo.altsRange.start]!
      let negsucc_fun := args[casesInfo.altsRange.start + 1]!
      let bool_indval := (← getConstInfo ``Bool).inductiveVal!
      let (bool_indid, _) ← register_inductive bool_indval
      withLocalDecl `n (.const ``Nat []) .default (fun n_fvar => do
        let ofnat_nt: LBTerm := .app (← visitExpr ofnat_fun) (.fvar n_fvar)
        let negsucc_nt: LBTerm :=
          .app (← visitExpr negsucc_fun)
          <| .app (← visitExpr (.const ``Int.neg []))
          <| .app (← visitExpr (.const ``Nat.succ [])) (.fvar n_fvar)
        let condition: LBTerm ← visitExpr <| mkAppN (.const ``Nat.ble []) #[.lit (.natVal 0), .fvar n_fvar]
        let case_nt: LBTerm := .case (bool_indid, 0) condition [← mkAlt [] negsucc_nt, ← mkAlt [] ofnat_nt]
        mkLetIn n_fvar discr_nt case_nt
      )
    | _, _ => do
      let .inductInfo indVal ← getConstInfo typeName | unreachable!
      let (indid, argmasks) ← register_inductive indVal
      let mut alts := #[]
      for i in casesInfo.altsRange, numFields in casesInfo.altNumParams /- which should proobably be called altNumFields -/, argmask in argmasks do
        let alt ← visitAlt numFields argmask args[i]!
        alts := alts.push alt
      pure <| LBTerm.case (indid, indVal.numParams) discr_nt alts.toList
    )

    -- The casesOn function may be overapplied, so handle the extra arguments.
    for arg in args[casesInfo.arity:] do
      ret := .app ret (← visitExpr arg)
    return ret

  /--
  Visit a `matcher`/`casesOn` alternative.
  On the Lean side, e should be a function taking numFields arguments.
  For λbox, I think we only need the body, as the LBTerm.cases constructor handles the bindings.
  -/
  visitAlt (numFields : Nat) (argmask: ConstructorArgMask) (e : Expr) : EraseM (List BinderName × LBTerm) := do
    lambdaOrIntroToArity e (← liftMetaM <| Meta.inferType e) numFields fun e fvarids => do
      mkAlt (filter argmask fvarids.toArray).toList (← visitExpr e)

  get_constant_kername (n: Name): EraseM Kername := do
    if let .some kn := (← get).constants.get? n then
      return kn
    else
     visitMutual n
     return (← get).constants[n]!

  /--
  Add all the declarations in the Lean-side mutual block of `name` to the global_declarations,
  and add their mappings to kernames to the erasure state.
  -/
  visitMutual (name: Name): EraseM Unit := do
    -- Use original recursive definition, not the elaborated one with recursors, if available.
    let ci := (← Compiler.LCNF.getDeclInfo? name).get!
    let names := ci.all -- possibly these are ._unsafe_rec
    let single_decl := names.length == 1
    -- A single declaration may have to be output as an axiom.
    if single_decl then
      match Compiler.getInlineAttribute? (← getEnv) name with
      | .some inl => match inl with
                     | .inline | .alwaysInline => logInfo s!"Name {name} is marked as inline."
                                                  modify (fun s => { s with inlinings := s.inlinings.cons (toKername name) })
                     | _ => pure ()
      | .none => pure ()
      match ci.value? (allowOpaque := true), isExtern (← getEnv) name, (← read).config.extern with
      | .none, _, _ =>
        logInfo s!"No value found for name {name}, emitting axiom."
        return ← addAxiom name
      | .some _, false, _ => pure ()
      | .some _, true, .preferAxiom =>
        logInfo s!"Name {name} has a value but is tagged @[extern], emitting axiom."
        return ← addAxiom name
      | .some _, true, .preferLogical =>
        logInfo s!"Name {name} is tagged @[extern] but has a value, using value."
        pure ()

    let nonrecursive: Bool := single_decl && !(name_occurs name (ci.value! (allowOpaque := true)))
    if nonrecursive
    then -- translate into a single nonrecursive constant declaration
      let e: Expr := ci.value! (allowOpaque := true)
      let t ← withReader (fun env => { env with fixvars := .none }) do
        pure (← visitExpr (← prepare_erasure e))
      let kn := toKername name
      modify (fun s => { s with constants := s.constants.insert name kn, gdecls := s.gdecls.cons (kn, .constantDecl <| ⟨.some t⟩) })
    else -- translate into a mutual fixpoint declaration
      let ids ← names.mapM (fun _ => mkFreshFVarId)
      let fixvarnames := names.map remove_unsafe_rec
      withReader (fun env => { env with fixvars := fixvarnames |>.zip ids |> Std.HashMap.ofList |> .some }) do
        let defs: List FixDef ← names.mapM (fun n => do
          let ci ← getConstInfo n -- here n is directly from the above ci.all, possibly _unsafe_rec
          let e: Expr := ci.value! (allowOpaque := true)
          -- TODO: eta-expand fixpoints? (I think this must be done, unsure how far)
          let t: LBTerm ← visitExpr (← prepare_erasure e)
          mkDef (remove_unsafe_rec n) fixvarnames t
        )
        for (n, i) in fixvarnames.zipIdx do
          let kn := toKername n
          modify (fun s => { s with constants := s.constants.insert n kn, gdecls := s.gdecls.cons (kn, .constantDecl ⟨.some <| .fix defs i⟩) })

inductive MLType: Type where
  | arrow (a b: MLType)
  | Z
  | unit
  | bool
  | list (a: MLType)
deriving Inhabited

def MLType.toString: MLType -> String
  | arrow a b => s!"{toStringProtected a} -> {b.toString}"
  | Z => "Z.t"
  | unit => "unit"
  | bool => "bool"
  | list a => s!"{a.toString} list"
where
  toStringProtected: MLType -> String
  | arrow a b => s!"({toStringProtected a} -> {b.toString})"
  | Z => "Z.t"
  | unit => "unit"
  | bool => "bool"
  | list a => s!"{a.toString} list"

instance : ToString MLType := ⟨MLType.toString⟩

partial def to_ml_type (ty: Expr): MetaM MLType :=
  Meta.forallTelescopeReducing ty fun vars body => do
    let vartypes ← vars.mapM Meta.inferType
    let varmltypes ← vartypes.mapM to_ml_type
    let bodymltype ← match (← Meta.whnf body) with
    | .const `Nat _ => pure .Z
    | .const `Unit _ | .const `PUnit _ => pure .unit
    | .const `Bool _ => pure .bool
    | .app (.const `List _) a => do pure <| .list (← to_ml_type a)
    | t => logWarning s!"failed to translate {t} into ML type, emitting unit instead." ; pure .unit
    return varmltypes.foldr .arrow bodymltype

def gen_mli (ty: Expr): MetaM String := do return s!"val main: {← to_ml_type ty}"

syntax (name := erasestx) "#erase" ppSpace term (ppSpace "config" term)? (ppSpace "to" ppSpace str)? (ppSpace "mli" ppSpace str)?: command

@[command_elab erasestx]
def eraseElab: Elab.Command.CommandElab
  | `(command| #erase $t:term $[config $cfg?:term]? $[to $path?:str]? $[mli $mli?:str]?) => Elab.Command.liftTermElabM do
    let e: Expr ← Elab.Term.elabTerm t (expectedType? := .none)
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e

    let cfg: ErasureConfig ← match cfg? with
    | .none => pure {}
    | .some cfg => unsafe Elab.Term.evalTerm ErasureConfig (.const ``Erasure.ErasureConfig []) cfg

    let (p, inls) ← erase e cfg
    let s: String := p |> Serialize.to_sexpr |>.toString
    -- logInfo s!"{repr p}"
    match path? with
    | .some path => do
        IO.FS.writeFile path.getString s
    | .none => logInfo s

    let c: AttributesConfig := { inlinings := inls, constRemappings := [], indRemappings := [], cstrReorders := [], customAttributes := [] }
    let c_s := c |> Serialize.to_sexpr |>.toString
    match path? with
    | .some path => do
        IO.FS.writeFile (path.getString ++ ".inlinings") c_s
    | .none => logInfo s

    let ty: Expr ← Meta.inferType e
    let mlistr ← gen_mli ty
    match mli? with
    | .none => logInfo mlistr
    | .some mlipath => IO.FS.writeFile mlipath.getString mlistr

  | _ => Elab.throwUnsupportedSyntax

end Erasure
