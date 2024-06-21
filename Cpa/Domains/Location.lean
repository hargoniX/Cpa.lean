import Cpa.Domains.Def
import Cpa.Cfa

namespace Domain

abbrev Location : Type := FlatLattice Nat

instance : Domain Location where
  meet lhs rhs := do
    let l ← lhs
    let r ← rhs
    if l = r then
      return l
    else
      .top

instance : Transfer Location where
  transfer l _ e :=
    match l with
    | .top => some .top
    | .val .. => some <| .val e.target

end Domain
