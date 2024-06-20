inductive AOp where
| add
| sub
| mul
| div
deriving Repr, Hashable, DecidableEq

inductive BOp where
| eq
| neq
| lt
| gt
deriving Repr, Hashable, DecidableEq

inductive AExp where
| ident (x : String)
| const (val : Int)
| bin (lhs : AExp) (op : AOp) (rhs : AExp)
| nondet
deriving Repr, Hashable, DecidableEq

inductive BExp where
| const (b : Bool)
| not (e : BExp)
| bin (lhs : AExp) (op : BOp) (rhs : AExp)
deriving Repr, Hashable, DecidableEq

inductive Stmnt where
| assign (x : String) (exp : AExp)
| seq (lhs rhs : Stmnt)
| ite (discr : BExp) (pos neg : Stmnt)
| while (discr : BExp) (body : Stmnt)
| break
| continue
| reachError
deriving Repr, Hashable, DecidableEq

declare_syntax_cat aexp
declare_syntax_cat bexp
declare_syntax_cat stmnt

syntax "true" : bexp
syntax "false" : bexp
syntax aexp " == " aexp : bexp
syntax aexp " != " aexp : bexp
syntax aexp " < " aexp : bexp
syntax aexp " > " aexp : bexp

syntax num : aexp
syntax ident : aexp
syntax aexp " + " aexp : aexp
syntax aexp " - " aexp : aexp
syntax aexp " * " aexp : aexp
syntax aexp " / " aexp : aexp
syntax "(" aexp ")" : aexp
syntax "nondet" "(" ")" : aexp


syntax ident " = " aexp : stmnt
syntax stmnt  stmnt : stmnt
syntax "if" "(" bexp ")" "{" stmnt "}" "else" "{" stmnt "}" : stmnt
syntax "while" "(" bexp ")" "{" stmnt "}" : stmnt
syntax "break" : stmnt
syntax "continue" : stmnt
syntax "reach_error" "(" ")" : stmnt

syntax "[bexp|" bexp "]" : term
syntax "[aexp|" aexp "]" : term
syntax "[stmnt|" stmnt "]" : term

open Lean in
macro_rules
| `([bexp| true]) => `(BExp.const Bool.true)
| `([bexp| false]) => `(BExp.const Bool.false)
| `([bexp| $lhs:aexp == $rhs:aexp]) => `(BExp.bin [aexp| $lhs] BOp.eq [aexp| $rhs])
| `([bexp| $lhs:aexp != $rhs:aexp]) => `(BExp.bin [aexp| $lhs] BOp.neq [aexp| $rhs])
| `([bexp| $lhs:aexp < $rhs:aexp]) => `(BExp.bin [aexp| $lhs] BOp.lt [aexp| $rhs])
| `([bexp| $lhs:aexp > $rhs:aexp]) => `(BExp.bin [aexp| $lhs] BOp.gt [aexp| $rhs])
| `([aexp| $n:num]) => `(AExp.const $n)
| `([aexp| $i:ident]) => `(AExp.ident $(quote i.getId.toString))
| `([aexp| $lhs:aexp + $rhs:aexp]) => `(AExp.bin [aexp| $lhs] AOp.add [aexp| $rhs])
| `([aexp| $lhs:aexp - $rhs:aexp]) => `(AExp.bin [aexp| $lhs] AOp.sub [aexp| $rhs])
| `([aexp| $lhs:aexp * $rhs:aexp]) => `(AExp.bin [aexp| $lhs] AOp.mul [aexp| $rhs])
| `([aexp| $lhs:aexp / $rhs:aexp]) => `(AExp.bin [aexp| $lhs] AOp.div [aexp| $rhs])
| `([aexp| nondet()]) => `(AExp.nondet)
| `([aexp| ($e:aexp)]) => `([aexp| $e])
| `([stmnt| $i:ident = $e:aexp]) => `(Stmnt.assign $(quote i.getId.toString) [aexp| $e])
| `([stmnt| $s1:stmnt $s2:stmnt]) => `(Stmnt.seq [stmnt| $s1] [stmnt| $s2])
| `([stmnt| if ($discr:bexp) { $pos:stmnt } else { $neg:stmnt }]) =>
    `(Stmnt.ite [bexp| $discr] [stmnt| $pos] [stmnt| $neg])
| `([stmnt| while ($discr:bexp) { $pos:stmnt }]) =>
    `(Stmnt.while [bexp| $discr] [stmnt| $pos])
| `([stmnt| break]) => `(Stmnt.break)
| `([stmnt| continue]) => `(Stmnt.continue)
| `([stmnt| reach_error()]) => `(Stmnt.reachError)
