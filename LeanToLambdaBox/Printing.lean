import LeanToLambdaBox

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

instance : Serialize ppname where
  to_sexpr
  | .named name => .list [ .atom "nNamed", quote_atom name ]
  | .anon => .atom "nAnon"

instance : Serialize ident where
  to_sexpr := quote_atom

instance [Serialize α]: Serialize (List α) where
  to_sexpr | l => l |>.map to_sexpr |> .list

def modpath.to_sexpr: modpath -> sexpr
  | .MPfile dp => .list [ .atom "MPfile", Serialize.to_sexpr dp ]
  | .MPdot mp id => .list [ .atom "MPdot", to_sexpr mp, Serialize.to_sexpr id ]

instance : Serialize modpath where to_sexpr := modpath.to_sexpr

instance : Serialize kername where
  to_sexpr
  | ⟨mp, id⟩ => .list [ to_sexpr mp, to_sexpr id ] 

instance: Serialize inductive_id where
  to_sexpr | ⟨kn, idx⟩  => .list [ .atom "inductive", to_sexpr kn, to_sexpr idx ]

instance [Serialize α] [Serialize β]: Serialize (α × β) where
  to_sexpr | (a, b)  => .list [ to_sexpr a, to_sexpr b ]

instance: Serialize projectioninfo where
  to_sexpr | ⟨indinfo, npars, idx⟩ => .list [ .atom "projection", to_sexpr indinfo, to_sexpr npars, to_sexpr idx ]

mutual
  partial def neterm.to_sexpr: neterm -> sexpr
    | .box => .atom "tBox"
    | .bvar n => .list [ .atom "tRel", to_sexpr n ]
    | .lambda na t => .list [ .atom "tLambda", to_sexpr na, neterm.to_sexpr t ]
    | .letIn na b t => .list [ .atom "tLetIn", to_sexpr na, neterm.to_sexpr b, neterm.to_sexpr t ]
    | .app u v => .list [ .atom "tApp", neterm.to_sexpr u, neterm.to_sexpr v ]
    | .const k => .list [ .atom "tConst", to_sexpr k ]
    | .construct ind n args => .list [ .atom "tConstruct", to_sexpr ind, to_sexpr n, .list (args.map neterm.to_sexpr)  ]
    | .case indn c brs => .list [
        .atom "tCase",
        to_sexpr indn,
        neterm.to_sexpr c,
        .list (brs.map fun (names, branch) => .list [ to_sexpr names, neterm.to_sexpr branch ])
        ]
    | .proj p c => .list [ .atom "tProj", to_sexpr p, neterm.to_sexpr c ]
    | .fix mfix idx => .list [ .atom "tFix", .list (mfix.map edef.to_sexpr), to_sexpr idx ]
    | .fvar .. => unreachable!

  partial def edef.to_sexpr: @edef neterm -> sexpr
    | ⟨name, body, principal⟩ => .list [ .atom "def", to_sexpr name, neterm.to_sexpr body, to_sexpr principal ]
end

instance : Serialize neterm where to_sexpr := neterm.to_sexpr

/-- The Rocq/Coq lexer expects `"` characters in string literals to be represented by the sequence `""`. This is cursed. -/
def rocq_escape (s: String): String :=
  s.toList |>.map (fun c: Char => if c = '"' then [c, c] else [c]) |>.flatten |>.asString

/-- Print with surrounding `"` characters and internal `"` characters doubled, for copy-pasting into Rocq. -/
def rocq_print (s: String): IO Unit := do
  IO.print '"'
  IO.print <| rocq_escape s
  IO.print '"'
