import Cpa.Domains.Def
import Cpa.Cfa
import Lean.Data.RBMap

namespace Domain

open Lean

abbrev Value : Type := FlatLattice Int

structure ValueAssignment where
  vars : RBMap String Value Ord.compare := {}
deriving Repr

namespace ValueAssignment

def find (assign : ValueAssignment) (var : String) : Value :=
  assign.vars.findD var .top

def insert (assign : ValueAssignment) (var : String) (val : Value) : ValueAssignment :=
  { assign with vars := assign.vars.insert var val }

def evalAexp (assign : ValueAssignment) (exp : AExp) : Value := do
  match exp with
  | .const x => return x
  | .ident var => assign.find var
  | .bin lhs op rhs =>
    let lval ← evalAexp assign lhs
    let rval ← evalAexp assign rhs
    return (denoteOp op) lval rval
  | .nondet => .top
where
  denoteOp (op : AOp) : Int → Int → Int :=
    match op with
    | .add => (· + ·)
    | .sub => (· - ·)
    | .mul => (· * ·)
    | .div => (· / ·)

def evalBExp (assign : ValueAssignment) (exp : BExp) : FlatLattice Bool := do
  match exp with
  | .const b => return b
  | .not b =>
    let bval ← evalBExp assign b
    return !bval
  | .bin lhs op rhs =>
    let lval ← evalAexp assign lhs
    let rval ← evalAexp assign rhs
    return (denoteOp op) lval rval
where
  denoteOp (op : BOp) : Int → Int → Bool :=
    match op with
    | .eq => (· == ·)
    | .neq => (· != ·)
    | .lt => (· < ·)
    | .gt => (· ≤ ·)

end ValueAssignment

instance : LE ValueAssignment where
  le lhs rhs := lhs.vars.all (fun var val => val ≤ rhs.find var)

instance : DecidableRel (@LE.le ValueAssignment _) :=
  fun lhs rhs => inferInstanceAs (Decidable (lhs.vars.all (fun var val => val ≤ rhs.find var)))

instance : BEq ValueAssignment where
  beq lhs rhs :=
    lhs.vars.all (fun var val => val == rhs.find var)
      &&
    rhs.vars.all (fun var val => val == lhs.find var)

instance : Domain ValueAssignment where
  meet lhs rhs :=
    let folder acc var val :=
      if rhs.find var == val then
        acc.insert var val
      else
        -- We would insert top here but we just say if a variable isn't in the set it's top so no
        -- need to insert anything
        acc
    lhs.vars.fold (init := {}) folder

instance : Transfer ValueAssignment where
  transfer assign _ e := do
    match e.instr with
    | .nop => return assign
    | .assumption bexp =>
      match assign.evalBExp bexp with
      | .val Bool.false => none
      | .top | .val Bool.true => return assign
    | .statement var aexp => assign.insert var (assign.evalAexp aexp)

instance : ToString ValueAssignment where
  toString assign := assign.vars.fold (init := "[") (fun acc var val => acc ++ s!"{var} ↦ {val}, ") ++ "]"

end Domain
