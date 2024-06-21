import Cpa.Cfa
import Cpa.Domains

namespace Cpa

open Lean
open Domain

structure Config (d : Type) where
  merge : d → d → d
  stop : d → Array d → Bool
  cfa : CFA

variable {d : Type} [LE d] [DecidableRel (@LE.le d _)] [Domain d] [BEq d] [Transfer d]

partial def run (config : Config (Combined Location d)) (e0 : d) : Array (Combined Location d) :=
  let init := ⟨.val 0, e0⟩
  go [init] #[init]
where
  go (waitlist : List (Combined Location d)) (reached : Array (Combined Location d))
      : Array (Combined Location d) := Id.run do
    match waitlist with
    | [] => reached
    | ⟨l, e⟩ :: waitlist =>
      match l with
      | .top => go waitlist reached
      | .val idx =>
        let mut waitlist := waitlist
        let mut reached := reached
        let edges := config.cfa.getEdges idx
        for edge in edges do
          let some e' := Transfer.transfer ⟨l, e⟩ idx edge | continue
          for e'' in reached do
            let e_new := config.merge e' e''
            if e_new != e'' then
              waitlist := e_new :: waitlist
              if let some e''_idx := reached.findIdx? (· == e'') then
                reached := reached.set! e''_idx e_new
              else
                reached := reached.push e_new
          if !config.stop e' reached then
              waitlist := e' :: waitlist
              reached := reached.push e'
        go waitlist reached

def mcMerge (_lhs rhs : Combined Location d) : Combined Location d := rhs
def dfaMerge (lhs rhs : Combined Location d) : Combined Location d :=
  if lhs.left == rhs.left then
    Domain.meet lhs rhs
  else
    rhs

def defaultStop (state : Combined Location d) (reached : Array (Combined Location d)) : Bool :=
  let ⟨l, e⟩ := state
  reached.any (fun ⟨l', e'⟩ => l' = l ∧ e ≤ e')

namespace Config

def modelChecking (d : Type) [LE d] [DecidableRel (@LE.le d _)] (cfa : CFA) : Config (Combined Location d) :=
  {
    merge := mcMerge,
    stop := defaultStop,
    cfa := cfa
  }

def dataFlowAnalysis (d : Type) [LE d] [DecidableRel (@LE.le d _)] [Domain d] (cfa : CFA) : Config (Combined Location d) :=
  {
    merge := dfaMerge,
    stop := defaultStop,
    cfa := cfa
  }

end Config

def modelChecking (cfa : CFA) (e0 : d) : Array (Combined Location d) :=
  let cfg := Config.modelChecking d cfa
  Cpa.run cfg e0

def dataFlowAnalysis (cfa : CFA) (e0 : d) : Array (Combined Location d) :=
  let cfg := Config.dataFlowAnalysis d cfa
  Cpa.run cfg e0

def reachingDefinitions (cfa : CFA) : Array (Combined Location ReachedDefinitions) :=
  dataFlowAnalysis cfa {}

def valueDataFlowAnalysis (cfa : CFA) : Array (Combined Location ValueAssignment) :=
  dataFlowAnalysis cfa {}

def valueModelChecking (cfa : CFA) : Array (Combined Location ValueAssignment) :=
  modelChecking cfa {}

end Cpa
