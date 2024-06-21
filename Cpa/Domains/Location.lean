import Cpa.Domains.Def
import Cpa.Cfa

namespace Domain

inductive Location where
| top
| loc (n : Nat)
deriving Repr, Hashable, DecidableEq

instance : LE Location where
  le lhs rhs :=
    match lhs, rhs with
    | .loc .., .top => True
    | .top, .loc .. => False
    | .top, .top => True
    | .loc l, .loc r => l ≤ r

instance : DecidableRel (@LE.le Location _) :=
  fun lhs rhs =>
    match lhs, rhs with
    | .loc .., .top => .isTrue (by simp [(· ≤ ·)])
    | .top, .loc .. => .isFalse (by simp [(· ≤ ·)])
    | .top, .top => .isTrue (by simp [(· ≤ ·)])
    | .loc l, .loc r => inferInstanceAs (Decidable (l ≤ r))

instance : Domain Location where
  meet lhs rhs :=
    match lhs, rhs with
    | .top, _ => .top
    | _, .top => .top
    | .loc l, .loc r =>
      if l = r then
        .loc l
      else
        .top

instance : Transfer Location where
  transfer l _ e :=
    match l with
    | .top => .top
    | .loc .. => .loc e.target

end Domain
