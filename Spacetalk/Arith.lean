
namespace Arith

inductive Exp
  | var : String → Exp
  | plus : Exp → Exp → Exp

abbrev Env := String → Nat

inductive Eval : Env → Exp → Nat → Prop
  | var : env s = v → Eval env (.var s) v
  | plus : Eval env e1 x
           → Eval env e2 y
           → Eval env (.plus e1 e2) (x + y)

end Arith
