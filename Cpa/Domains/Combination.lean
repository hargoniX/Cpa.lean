import Cpa.Domains.Def

namespace Domain

structure Combined (α β : Type) where
  left : α
  right : β
deriving Repr, Hashable, BEq

variable (α β : Type) [LE α] [DecidableRel (@LE.le α _)] [LE β] [DecidableRel (@LE.le β _)] [Domain α] [Domain β]

instance : LE (Combined α β) where
  le lhs rhs := lhs.left ≤ rhs.left ∧ lhs.right ≤ rhs.right

instance : DecidableRel (@LE.le (Combined α β) _) :=
  fun lhs rhs => inferInstanceAs (Decidable (lhs.left ≤ rhs.left ∧ lhs.right ≤ rhs.right))

instance : Domain (Combined α β) where
  meet lhs rhs := ⟨Domain.meet lhs.left rhs.left, Domain.meet lhs.right rhs.right⟩

instance [Transfer α] [Transfer β] : Transfer (Combined α β) where
  transfer c l e := do
    let lres ← Transfer.transfer c.left l e
    let rres ← Transfer.transfer c.right l e
    return ⟨lres, rres⟩

end Domain
