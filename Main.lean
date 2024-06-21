import Cpa

def prog_1_1 : Stmnt := [stmnt|
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

#eval Stmnt.countNames prog_1_1

end CountNames

#eval CFA.ofAST prog_1_1

def prog_my_example : Stmnt := [stmnt|
  i = 0
  if (i == j) {
    i = 1
    j = 1
  } else {
    j = 1
  }

  if (j == 1) {
    k = 1
  } else {
    reach_error()
  }
]

open Domain in
def main : IO Unit := do
  let res := CFA.ofAST prog_my_example
  match res with
  | .ok cfa =>
    IO.println s!"Analyzing CFA:\n{repr cfa}\n"
    let res := Cpa.reachingDefinitions cfa
    IO.println s!"Reaching Definitions:\n{repr res}\n"
    let res := Cpa.valueDataFlowAnalysis cfa
    IO.println s!"Value DFA:\n{repr res}\n"
  | .error e => throw <| .userError s!"Error while constructing CFA: {e}"

#eval main
