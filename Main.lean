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

#eval toString <| CFA.ofAST prog_1_1

def prog_mc_example : Stmnt := [stmnt|
  if (i == 0) {
    i = 0
  } else {
    i = 1
  }

  if (i < 2) {
    i = 2
  } else {
    reach_error()
  }
]

open Domain in
def valueExample : IO Unit := do
  let res := CFA.ofAST prog_mc_example
  match res with
  | .ok cfa =>
    -- This is the program we are working on
    IO.println s!"# Analyzing CFA:\n{cfa}\n"

    -- This is data flow analysis with constant propagation
    let res := Cpa.valueDataFlowAnalysis cfa
    IO.println s!"## Value DFA:\n{res}\n"

    -- This is model checking analysis with constant propagation
    let res := Cpa.valueModelChecking cfa
    IO.println s!"## Value MC:\n{res}\n"
  | .error e => throw <| .userError s!"Error while constructing CFA: {e}"

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
def reachDefExample : IO Unit := do
  let res := CFA.ofAST prog_my_example
  match res with
  | .ok cfa =>
    -- This is the program we are working on
    IO.println s!"# Analyzing CFA:\n{cfa}\n"

    -- This is syntactic analysis of reachable variables
    let res := Cpa.reachingDefinitions cfa
    IO.println s!"## Reaching Definitions:\n{res}\n"

    -- This is value analysis with constant propagation
    let res := Cpa.valueDataFlowAnalysis cfa
    IO.println s!"## Value DFA:\n{res}\n"

    -- We can inform reaching definitions analysis using value analysis.
    -- This allows us to figure out that because certain locations are not reachable, they
    -- do not have reaching variable definitions
    let res := Cpa.dataFlowAnalysis (d := Combined ReachedDefinitions ValueAssignment) cfa ⟨{}, {}⟩
    IO.println s!"## Reaching Definitions + Value DFA:\n{res}\n"
  | .error e => throw <| .userError s!"Error while constructing CFA: {e}"


def main : IO Unit := do
  valueExample
  reachDefExample
