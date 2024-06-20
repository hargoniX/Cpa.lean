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
      j = j * 2 - 1
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

def main : IO Unit :=
  IO.println s!"Hello, world!"
