import Cpa

section CountNames

def AExp.countNames (e : AExp) : Nat :=
  match e with
  | ident .. => 1
  | .bin lhs _ rhs => lhs.countNames + rhs.countNames
  | .const .. | .nondet => 0

def BExp.countNames (e : BExp) : Nat :=
  match e with
  | .const .. => 0
  | .not e => e.countNames
  | .bin lhs _ rhs => lhs.countNames + rhs.countNames

def Stmnt.countNames (s : Stmnt) : Nat :=
  match s with
  | .assign _ val => 1 + val.countNames
  | .seq lhs rhs => lhs.countNames + rhs.countNames
  | .ite discr pos neg => discr.countNames + pos.countNames + neg.countNames
  | .while discr body => discr.countNames + body.countNames
  | .break | .continue | .reachError => 0

#eval Stmnt.countNames [stmnt|
  i = 0
  j = nondet()
  while (i < 1000) {
    if (i == 47) {
      j = (j * 2) - 1
      reach_error()
      break
    } else {
      i = i + 1
      continue
    }
    i = i - 1
  }
]

end CountNames

#eval CFA.ofAST [stmnt|
  i = 0
  j = nondet()
  while (i < 1000) {
    if (i == 47) {
      j = (j * 2) - 1
      reach_error()
      break
    } else {
      i = i + 1
      continue
    }
    i = i - 1
  }
]

open Domain in
def main : IO Unit := do
  --let res := CFA.ofAST [stmnt|
  --  i = 0
  --  j = nondet()
  --  while (i < 1000) {
  --    if (i == 47) {
  --      j = (j * 2) - 1
  --      reach_error()
  --      break
  --    } else {
  --      i = i + 1
  --      continue
  --    }
  --    i = i - 1
  --  }
  --]
  let res := CFA.ofAST [stmnt|
    i = 0
    if (i == 0) {
      i = 1
    } else {
      j = 1
    }
    k = 1
  ]
  match res with
  | .ok cfa =>
    IO.println s!"Analyzing CFA:\n{repr cfa}"
    let res := Cpa.reachingDefinitions cfa
    IO.println s!"Reaching Definitions:\n{repr res}"
  | .error e => throw <| .userError s!"Error while constructing CFA: {e}"

#eval main
