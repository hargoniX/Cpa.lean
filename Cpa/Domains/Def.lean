import Cpa.Cfa

class Domain (α : Type) [LE α] [DecidableRel (@LE.le α _)] where
  meet : α → α → α

class Transfer (α : Type) where
  transfer : α → Nat → Edge → α
