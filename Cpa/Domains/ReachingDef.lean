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

instance : ToString Definition where
  toString d := s!"{d.var} @ {d.entry}-{d.exit}"

structure ReachedDefinitions where
  defs : RBMap Definition Unit Ord.compare := {}
deriving Repr

instance : LE ReachedDefinitions where
  le lhs rhs := lhs.defs.all (fun d _ => rhs.defs.contains d)

instance : DecidableRel (@LE.le ReachedDefinitions _) :=
  fun lhs rhs => inferInstanceAs (Decidable (lhs.defs.all (fun d _ => rhs.defs.contains d)))

instance : BEq ReachedDefinitions where
  beq lhs rhs := lhs ≤ rhs && rhs ≥ lhs

instance : Domain ReachedDefinitions where
  meet lhs rhs := ⟨rhs.defs.fold (init := lhs.defs) RBMap.insert⟩

instance : Transfer ReachedDefinitions where
  transfer r entry e := do
    match e.instr with
    | .assumption .. | .nop => return r
    | .statement var _ =>
      let mut ⟨defs⟩ := r
      for (varDef, _) in r.defs do
        if varDef.var == var then
          defs := defs.erase varDef
      defs := defs.insert ⟨var, entry, e.target⟩ ()
      return ⟨defs⟩

instance : ToString ReachedDefinitions where
  toString reached := reached.defs.fold (init := "[") (fun acc d _ => acc ++ s!"{d}, ") ++ "]"

end Domain
