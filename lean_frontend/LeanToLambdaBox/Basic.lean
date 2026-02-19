import Lean

open Lean (Name FVarId InductiveVal)

abbrev Ident := String
abbrev DirPath := List String

inductive ModPath where
| MPfile  (dp : DirPath)
| MPdot   (mp : ModPath) (id : Ident)
-- MPBound is about functors (in the sense of ML module systems).
deriving Inhabited, Repr

structure Kername where
  mp: ModPath
  id: Ident
deriving Inhabited, Repr

def toModPath (n: Name): ModPath :=
  match n with
  | .str name s => .MPdot (toModPath name) s
  | .num name nb => .MPdot (toModPath name) (nb.repr)
  | .anonymous => .MPfile []

/-- Clean up a string potentially coming from Lean's very permissive grammar to only use characters valid in OCaml identifiers. -/
def cleanIdent (s : String) : String :=
  let escapeChar (c : Char) : String :=
    if c.isAlphanum || c == '_' then toString c
    else "_u" ++ toString c.toNat

  s.toList.map escapeChar |> String.join
/--
Ad hoc conversion function from `Name`s to MetaRocq kernames.
-/
def toKername (n: Name): Kername :=
  match n with
  | .str name s =>  { mp := toModPath name, id := cleanIdent s }
  | .num name nb =>  { mp := toModPath name, id := nb.repr }
  | .anonymous =>  panic! "Cannot convert empty name to kername." -- This should not happen.

def rootKername (s: String): Kername :=
  { mp := .MPfile [], id := cleanIdent s }

/-- A name used to pretty-print bound variables. -/
inductive BinderName: Type where
  | named (s: String)
  | anon
  deriving Inhabited, Repr

structure InductiveId where
  mutualBlockName: Kername
  /-- Which of the mutually inductive types defined in this block is used here? -/
  idx: Nat
  deriving Inhabited, Repr

structure ProjectionInfo where
  indType: InductiveId
  paramCount: Nat
  fieldIdx: Nat
  deriving Inhabited, Repr

structure FixDef {term: Type} where
  name: BinderName
  /-- The body typically (necessarily?) starts with a certain number (at least rarg + 1) of lambda constructor applications, one for each argument. -/
  body: term
  /-- Principal/structural argument for recursion. -/
  principalArgIdx: Nat := 0 -- this doesn't matter computationally and is just needed in the proof of correctness, so it's safe to let this be 0
  deriving Inhabited, Repr

inductive PrimTag where
  | primInt
  /- Rocq has these, but I'm not supporting them for the moment.
  | primFloat
  | primArray
  -/
deriving Repr

/--
In MetaRocq they need to do something fancy to keep positivity because there everything is parametrized by the type of terms.
Since I don't handle arrays for now there's no need for that.
--/
abbrev PrimModel: PrimTag -> Type
  | .primInt => BitVec 63

abbrev PrimVal: Type := Σ t: PrimTag, PrimModel t

/--
Basically `term` as defined in `MetaRocq/Erasure/EAst.v`, with an extra constructor `.fvar` to mimic Lean's locally nameless representation.
-/
inductive LBTerm where
  | box: LBTerm
  /-- A bound variable, accessed as a de Bruijn index. -/
  | bvar: Nat -> LBTerm
  | fvar: FVarId -> LBTerm
  | lambda: BinderName -> LBTerm -> LBTerm
  | letIn: BinderName -> LBTerm -> LBTerm -> LBTerm
  | app: LBTerm -> LBTerm -> LBTerm
  /-- A constant living in the environment. -/
  | const: Kername -> LBTerm
  | construct: InductiveId -> Nat /- index of the constructor used -/ -> List LBTerm -> LBTerm
  | case: (InductiveId × Nat /- number of parameters -/) -> LBTerm -> List (List BinderName × LBTerm) -> LBTerm
  | proj: ProjectionInfo -> LBTerm -> LBTerm
  /-- Define some number of mutually inductive functions, then access one. -/
  | fix: List (@FixDef LBTerm) -> Nat /- index of the one mutually defined function we want to access -/ -> LBTerm
  | prim: PrimVal -> LBTerm
  deriving Inhabited, Repr

/-- This is actually structurally recursive, I think, Lean just has trouble seeing it because of the inductive nesting. -/
partial def toBvar (x: FVarId) (lvl: Nat) (e: LBTerm): LBTerm :=
  match e with
  | .box => .box
  | .bvar i => .bvar i
  | .fvar y => if y == x then .bvar lvl else .fvar y
  | .lambda name body => .lambda name (toBvar x (lvl + 1) body)
  | .letIn name val body => .letIn name (toBvar x lvl val) (toBvar x (lvl + 1) body)
  | .app a b => .app (toBvar x lvl a) (toBvar x lvl b)
  | .const kn => .const kn
  | .construct indid n args => .construct indid n (args.map <| toBvar x lvl)
  | .case (indid, n) discr alts => .case (indid, n) (toBvar x lvl discr) (alts.map fun (names, alt) => (names, toBvar x (lvl + names.length) alt))
  | .proj pinfo e => .proj pinfo (toBvar x lvl e)
  | .fix defs i =>
    let def_count := defs.length;
    .fix (defs.map fun nd => { nd with body := toBvar x (lvl + def_count) nd.body }) i
  | .prim p => .prim p

def abstract (x: FVarId) (e: LBTerm): LBTerm := toBvar x 0 e

structure ConstructorBody where
  name: Ident
  nargs: Nat
deriving Inhabited, Repr

-- should be unused
structure ProjectionBody where
  name: Ident
deriving Repr

inductive AllowedEliminations where
  | IntoSProp
  | IntoPropSProp
  | IntoSetPropSProp
  | IntoAny
deriving Inhabited, Repr

structure OneInductiveBody where
  name : Ident
  /-- True iff the inductive lives in Prop. -/
  propositional : Bool := false -- I think, since erasure should remove anything which ends up in Prop
  kelim : AllowedEliminations := .IntoAny
  ctors : List ConstructorBody
  projs : List ProjectionBody -- This is only about giving user-visible names to projections, but `peregrine` complains about wellformedness if it is empty.
deriving Inhabited, Repr

inductive RecursivityKind where
  | finite
  | cofinite -- Lean doesn't have primitive coinductive types, but including this here anyway to match the MetaCoq side.
  | bifinite
deriving Repr

structure MutualInductiveBody where
  finite : RecursivityKind := .finite
  /-- Number of parameters to this family of mutually inductive types. -/
  npars : Nat
  bodies : List OneInductiveBody
deriving Repr

structure ConstantBody where
  cst_body: Option LBTerm
deriving Repr

inductive GlobalDecl where
  | constantDecl (body: ConstantBody)
  | inductiveDecl (body: MutualInductiveBody)
deriving Repr

-- The first declarations to be added to the context are the deepest/first-consed in the list.
abbrev GlobalDeclarations := List (Kername × GlobalDecl)

inductive ASTType where
  | untyped (body: GlobalDeclarations) (term: Option LBTerm)
deriving Repr
abbrev Program: Type := ASTType

structure RemappedInductive where
  reIndName: String
  reIndCtors: List String
  reIndMatch: Option String
deriving Inhabited, Repr

structure ExtractInductive where
  cstrs: List Kername
  elim: Kername
deriving Inhabited, Repr

structure RemappedConstant where
  reConstExt: Option String
  reConstArity: Nat
  reConstGC: Bool
  reConstInl: Bool
  reConstS: String
deriving Inhabited, Repr

inductive remapInductive where
  | knIndRemap (re: ExtractInductive)
  | stringIndRemap (re: RemappedInductive)
deriving Repr

structure InductiveMapping where
  indMapKn: Kername
  indMapS: String
  indMapN: List Nat
deriving Inhabited, Repr

structure AttributesConfig where
  inlinings: List Kername
  constRemappings: List (Kername × RemappedConstant)
  indRemappings: List (InductiveId × remapInductive)
  cstrReorders: List InductiveMapping
  customAttributes: List (Kername × String)
deriving Inhabited, Repr
