import Cpa.Cfa

class Domain (α : Type) [LE α] [DecidableRel (@LE.le α _)] where
  meet : α → α → α

class Transfer (α : Type) where
  transfer : α → Nat → Edge → Option α

inductive FlatLattice (α : Type) where
| top
| val (x : α)
deriving Repr, Hashable, DecidableEq

instance [LE α] : LE (FlatLattice α) where
  le lhs rhs :=
    match lhs, rhs with
    | .val .., .top => True
    | .top, .val .. => False
    | .top, .top => True
    | .val l, .val r => l ≤ r

instance [LE α] [DecidableRel (@LE.le α _)] : DecidableRel (@LE.le (FlatLattice α) _) :=
  fun lhs rhs =>
    match lhs, rhs with
    | .val .., .top => .isTrue (by simp [(· ≤ ·)])
    | .top, .val .. => .isFalse (by simp [(· ≤ ·)])
    | .top, .top => .isTrue (by simp [(· ≤ ·)])
    | .val l, .val r => inferInstanceAs (Decidable (l ≤ r))

instance : Monad FlatLattice where
  pure := FlatLattice.val
  bind mx f :=
    match mx with
    | .top => .top
    | .val x => f x
