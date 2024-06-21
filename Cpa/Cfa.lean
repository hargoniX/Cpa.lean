import Cpa.Syntax
import Lean.Data.HashSet

open Lean

inductive Instruction where
| assumption (b : BExp)
| statement (var : String) (e : AExp)
| nop
deriving Repr, Hashable, DecidableEq, Inhabited

structure Edge where
  instr : Instruction
  target : Nat
deriving Repr, Hashable, DecidableEq, Inhabited

structure CFANode where
  isError : Bool
  successors : Array Edge
deriving Repr, Hashable, DecidableEq, Inhabited

structure CFA where
  graph : Array CFANode := #[]
deriving Repr, Hashable, DecidableEq, Inhabited

namespace CFA

def size (cfa : CFA) : Nat := cfa.graph.size

def newNode (cfa : CFA) (isError : Bool) : CFA :=
  { cfa with graph := cfa.graph.push { isError, successors := #[] }  }

def addEdge (cfa : CFA) (entry : Nat) (instr : Instruction) (exit : Nat) : CFA :=
  { cfa with
      graph :=
        cfa.graph.modify
          entry
          (fun node => { node with successors := node.successors.push ⟨instr, exit⟩ })
  }


def getEdges (cfa : CFA) (idx : Nat) : Array Edge :=
  cfa.graph[idx]!.successors

def isError (cfa : CFA) (idx : Nat) : Bool :=
  cfa.graph[idx]!.isError

namespace ofAST

structure Result where
  entry : Nat
  exit? : Option Nat
deriving Repr, Hashable, DecidableEq

structure LoopInfo where
  loopEntry : Nat
  loopExit : Nat
deriving Repr, Hashable, DecidableEq

structure Context where
  loopInfo : Option LoopInfo := none
deriving Repr, Hashable, DecidableEq

structure State where
  cfa : CFA := {}
deriving Repr, Hashable, DecidableEq

abbrev M := ReaderT Context <| StateT State <| Except String

namespace M

def run (x : M α) : Except String (α × CFA) :=
  ReaderT.run x {} |>.run {} |>.map (fun res => (res.fst, res.snd.cfa))

def newNode (isError : Bool := .false) : M Nat := do
  let s ← get
  let newIdx := s.cfa.size
  modify (fun s => { s with cfa := s.cfa.newNode isError })
  return newIdx

def addEdge (entry : Nat) (instr : Instruction) (exit : Nat) : M Unit := do
  modify (fun s => { s with cfa := s.cfa.addEdge entry instr exit })

def withLoop (loopEntry loopExit : Nat) (x : M α) : M α :=
  withReader (fun ctx => { ctx with loopInfo := some { loopEntry, loopExit } }) do
    x

def currLoopEntry? : M (Option Nat) := do
  let ctx ← read
  return ctx.loopInfo.map LoopInfo.loopEntry

def currLoopExit? : M (Option Nat) := do
  let ctx ← read
  return ctx.loopInfo.map LoopInfo.loopExit

end M

def go (s : Stmnt) : M Result := do
  match s with
  | .seq lhs rhs =>
    let ⟨lhsEntry, lhsExit?⟩ ← go lhs
    match lhsExit? with
    | none => return ⟨lhsEntry, none⟩
    | some lhsExit =>
      let ⟨rhsEntry, rhsExit?⟩ ← go rhs
      M.addEdge lhsExit .nop rhsEntry
      return ⟨lhsEntry, rhsExit?⟩
  | .ite discr pos neg =>
    let discrNode ← M.newNode
    let ⟨posEntry, posExit?⟩ ← go pos
    let ⟨negEntry, negExit?⟩ ← go neg
    let exitNode ← M.newNode

    M.addEdge discrNode (.assumption discr) posEntry
    M.addEdge discrNode (.assumption (.not discr)) negEntry
    if let some posExit := posExit? then
      M.addEdge posExit .nop exitNode

    if let some negExit := negExit? then
      M.addEdge negExit .nop exitNode

    if posExit?.isSome || negExit?.isSome then
      return ⟨discrNode, exitNode⟩
    else
      return ⟨discrNode, none⟩
  | .while discr body =>
    let discrNode ← M.newNode
    let exitNode ← M.newNode
    let ⟨bodyEntry, bodyExit?⟩ ←
      M.withLoop discrNode exitNode do
        go body
    M.addEdge discrNode (.assumption discr) bodyEntry
    M.addEdge discrNode (.assumption (.not discr)) exitNode

    if let some bodyExit := bodyExit? then
      M.addEdge bodyExit .nop discrNode

    return ⟨discrNode, exitNode⟩
  | .assign x exp =>
    let aEntry ← M.newNode
    let aExit ← M.newNode
    let instr := .statement x exp
    M.addEdge aEntry instr aExit
    return ⟨aEntry, some aExit⟩
  | .break =>
    let entry ← M.newNode
    let some loopExit ← M.currLoopExit? | throw "break outside of a loop detected"
    M.addEdge entry .nop loopExit
    return ⟨entry, none⟩
  | .continue =>
    let entry ← M.newNode
    let some loopEntry ← M.currLoopEntry? | throw "continue outside of a loop detected"
    M.addEdge entry .nop loopEntry
    return ⟨entry, none⟩
  | .reachError =>
    let eEntry ← M.newNode
    let eExit ← M.newNode (isError := .true)
    M.addEdge eEntry .nop eExit
    return ⟨eEntry, eExit⟩

end ofAST

def ofAST (s : Stmnt) : Except String CFA :=
  ofAST.go s |>.run |>.map Prod.snd

end CFA
