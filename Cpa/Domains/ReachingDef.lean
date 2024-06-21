import Cpa.Domains.Def
import Cpa.Cfa
import Lean.Data.RBMap

namespace Domain

open Lean

structure Definition where
  var : String
  entry : Nat
  exit : Nat
deriving Repr, Hashable, DecidableEq, Ord

structure ReachedDefinitions where
  defs : RBMap Definition Unit Ord.compare := {}
deriving Repr

instance : LE ReachedDefinitions where
  le lhs rhs := lhs.defs.all (fun d _ => rhs.defs.contains d)

instance : DecidableRel (@LE.le ReachedDefinitions _) :=
  fun lhs rhs => inferInstanceAs (Decidable (lhs.defs.all (fun d _ => rhs.defs.contains d)))

instance : BEq ReachedDefinitions where
  beq lhs rhs := lhs ≤ rhs && lhs.defs.size == rhs.defs.size

instance : Domain ReachedDefinitions where
  meet lhs rhs := ⟨rhs.defs.fold (init := lhs.defs) RBMap.insert⟩

instance : Transfer ReachedDefinitions where
  transfer r entry e := Id.run do
    match e.instr with
    | .assumption .. | .nop => r
    | .statement var _ =>
      let mut ⟨defs⟩ := r
      for (varDef, _) in r.defs do
        if varDef.var == var then
          defs := defs.erase varDef
          break
      defs := defs.insert ⟨var, entry, e.target⟩ ()
      return ⟨defs⟩

end Domain
