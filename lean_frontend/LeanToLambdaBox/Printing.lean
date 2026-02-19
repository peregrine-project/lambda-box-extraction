import LeanToLambdaBox.Basic

inductive sexpr: Type where
  | atom (a: String)
  | list (l: List sexpr)
deriving Inhabited

def sexpr.toString: sexpr -> String
  | atom a => a
  | list l => "(" ++ (l.map sexpr.toString |> String.intercalate " ") ++ ")"

instance : ToString sexpr where
  toString := sexpr.toString

class Serialize (α: Type): Type where
  to_sexpr: α → sexpr

open Serialize

def quote_atom (s: String): sexpr := "\"" ++ s ++ "\"" |> .atom

instance : Serialize Nat where
  to_sexpr | n => .atom n.repr

instance : Serialize BinderName where
  to_sexpr
  | .named name => .list [ .atom "nNamed", quote_atom name ]
  | .anon => .atom "nAnon"

instance : Serialize Ident where
  to_sexpr := quote_atom

instance [Serialize α]: Serialize (List α) where
  to_sexpr | l => l |>.map to_sexpr |> .list

def modpath.to_sexpr: ModPath -> sexpr
  | .MPfile dp => .list [ .atom "MPfile", Serialize.to_sexpr dp ]
  | .MPdot mp id => .list [ .atom "MPdot", to_sexpr mp, Serialize.to_sexpr id ]

instance : Serialize ModPath where to_sexpr := modpath.to_sexpr

instance : Serialize Kername where
  to_sexpr
  | ⟨mp, id⟩ => .list [ to_sexpr mp, to_sexpr id ]

instance: Serialize InductiveId where
  to_sexpr | ⟨kn, idx⟩  => .list [ .atom "inductive", to_sexpr kn, to_sexpr idx ]

instance [Serialize α] [Serialize β]: Serialize (α × β) where
  to_sexpr | (a, b)  => .list [ to_sexpr a, to_sexpr b ]

instance: Serialize ProjectionInfo where
  to_sexpr | ⟨indinfo, npars, idx⟩ => .list [ .atom "projection", to_sexpr indinfo, to_sexpr npars, to_sexpr idx ]

instance [Serialize α] [Serialize β]: Serialize (α × β) where
  to_sexpr | (a, b) => .list [ to_sexpr a, to_sexpr b ]

instance: Serialize PrimTag where
  to_sexpr | .primInt => .atom "primInt"

instance: Serialize (BitVec n) where
  to_sexpr b := let i := b.toFin.toNat; .atom ("\"" ++ i.repr ++ "\"")

instance: Serialize PrimVal where
  to_sexpr | ⟨.primInt, i⟩ => to_sexpr (PrimTag.primInt, (i: BitVec 63))

mutual
  partial def LBTerm.to_sexpr: LBTerm -> sexpr
    | .box => .atom "tBox"
    | .bvar n => .list [ .atom "tRel", to_sexpr n ]
    | .lambda na t => .list [ .atom "tLambda", to_sexpr na, LBTerm.to_sexpr t ]
    | .letIn na b t => .list [ .atom "tLetIn", to_sexpr na, LBTerm.to_sexpr b, LBTerm.to_sexpr t ]
    | .app u v => .list [ .atom "tApp", LBTerm.to_sexpr u, LBTerm.to_sexpr v ]
    | .const k => .list [ .atom "tConst", to_sexpr k ]
    | .construct ind n args => .list [ .atom "tConstruct", to_sexpr ind, to_sexpr n, .list (args.map LBTerm.to_sexpr)  ]
    | .case indn c brs => .list [
        .atom "tCase",
        to_sexpr indn,
        LBTerm.to_sexpr c,
        .list (brs.map fun (names, branch) => .list [ to_sexpr names, LBTerm.to_sexpr branch ])
        ]
    | .proj p c => .list [ .atom "tProj", to_sexpr p, LBTerm.to_sexpr c ]
    | .fix mfix idx => .list [ .atom "tFix", .list (mfix.map edef.to_sexpr), to_sexpr idx ]
    | .fvar .. => unreachable!
    | .prim p => .list [ .atom "tPrim", to_sexpr p]

  partial def edef.to_sexpr: @FixDef LBTerm -> sexpr
    | ⟨name, body, principal⟩ => .list [ .atom "def", to_sexpr name, LBTerm.to_sexpr body, to_sexpr principal ]
end

instance : Serialize LBTerm where to_sexpr := LBTerm.to_sexpr

instance : Serialize ConstructorBody where
  to_sexpr | ⟨name, nargs⟩  => .list [ .atom "constructor_body", to_sexpr name, to_sexpr nargs ]

instance : Serialize ProjectionBody where
  to_sexpr | ⟨proj_name⟩ => .list [ .atom "projection_body", to_sexpr proj_name ]

instance : Serialize AllowedEliminations where
  to_sexpr
  | .IntoSProp => .atom "IntoSProp"
  | .IntoPropSProp => .atom "IntoPropSProp"
  | .IntoSetPropSProp => .atom "IntoSetPropSProp"
  | .IntoAny => .atom "IntoAny"

instance : Serialize Bool where
  to_sexpr
  | .true => .atom "true"
  | .false => .atom "false"

instance : Serialize OneInductiveBody where
  to_sexpr | ⟨name, prop, kelim, ctors, projs⟩ => .list [ .atom "one_inductive_body", to_sexpr name, to_sexpr prop, to_sexpr kelim, to_sexpr ctors, to_sexpr projs ]

instance : Serialize RecursivityKind where
  to_sexpr
  | .finite => .atom "Finite"
  | .cofinite => .atom "CoFinite"
  | .bifinite => .atom "BiFinite"

instance : Serialize MutualInductiveBody where
  to_sexpr | ⟨reckind, nparams, bodies⟩ => .list [ .atom "mutual_inductive_body", to_sexpr reckind, to_sexpr nparams, to_sexpr bodies ]

instance : [Serialize α] -> Serialize (Option α) where
  to_sexpr
  | .none => .atom "None"
  | .some a => .list [.atom "Some", to_sexpr a]

instance : Serialize ConstantBody where
  to_sexpr | ⟨cb⟩ => .list [.atom "constant_body", to_sexpr cb]

instance : Serialize GlobalDecl where
  to_sexpr
  | .constantDecl cb => .list [ .atom "ConstantDecl", to_sexpr cb ]
  | .inductiveDecl mib => .list [ .atom "InductiveDecl", to_sexpr mib ]

instance : Serialize ASTType where
  to_sexpr
  | .untyped env t => .list [ .atom "Untyped", to_sexpr env, to_sexpr t ]

instance: Serialize RemappedInductive where
  to_sexpr | ⟨reIndName, reIndCtors, reIndMatch⟩ => .list [.atom "remapped_inductive", to_sexpr reIndName, to_sexpr reIndCtors, to_sexpr reIndMatch]

instance: Serialize ExtractInductive where
  to_sexpr | ⟨cstrs, elim⟩ => .list [.atom "extract_inductive", to_sexpr cstrs, to_sexpr elim]

instance: Serialize remapInductive where
  to_sexpr
  | .knIndRemap r => .list [ .atom "KnIndRemap", to_sexpr r ]
  | .stringIndRemap r => .list [ .atom "StringIndRemap", to_sexpr r ]

instance: Serialize InductiveMapping where
  to_sexpr | ⟨indMapKn, indMapS, indMapN⟩ => .list [.atom "inductive_mapping", to_sexpr indMapKn, to_sexpr indMapS, to_sexpr indMapN]

instance: Serialize RemappedConstant where
  to_sexpr | ⟨reExt, reArity, reGC, reInl, reS⟩ => .list [.atom "remapped_constant", to_sexpr reExt, to_sexpr reArity, to_sexpr reGC, to_sexpr reInl, to_sexpr reS ]

instance: Serialize AttributesConfig where
  to_sexpr | ⟨inls, c_rmps, i_rmps, cstrs, cattrs⟩ => .list [.atom "attributes_config", to_sexpr inls, to_sexpr c_rmps, to_sexpr i_rmps, to_sexpr cstrs, to_sexpr cattrs]

/-- The Rocq/Coq lexer expects `"` characters in string literals to be represented by the sequence `""`. This is cursed. -/
def rocq_escape (s: String): String :=
  s.toList |>.map (fun c: Char => if c = '"' then [c, c] else [c]) |>.flatten |>.asString

/-- Print with surrounding `"` characters and internal `"` characters doubled, for copy-pasting into Rocq. -/
def rocq_print (s: String): IO Unit := do
  IO.print '"'
  IO.print <| rocq_escape s
  IO.print '"'
