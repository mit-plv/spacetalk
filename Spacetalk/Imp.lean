import Lean

inductive Ty
  | unit
  | int
  | bool
  | ref
deriving BEq

inductive BinOp
  | add
  | eq

inductive Exp
  | unit_term : Exp
  | int_lit : Int → Exp
  | var : String → Exp
  | binop : BinOp → Exp → Exp → Exp
  | seq : Exp → Exp → Exp
  | mem : (base : Exp) → (offset : Exp) → Exp
  | assign : (lhs : Exp) → (rhs : Exp) → Exp
  | let_bind : String → Ty → Exp → (body : Exp) → Exp
  | for_loop : String
               → (start : Int)
               → (stop : Int)
               → (step : Int)
               → (body : Exp)
               → Exp
  | ite : (cond : Exp)
          → (then_body : Exp)
          → (else_body : Exp)
          → Exp

def TCtx := Std.HashMap String Ty

def typeOf (ctx : TCtx) : Exp → Option Ty
  | .unit_term => some .unit
  | .int_lit _ => some .int
  | .var name => ctx.get? name
  | .binop bop e1 e2 => do
    let t1 ← typeOf ctx e1
    let t2 ← typeOf ctx e2
    match bop with
    | .add =>
      if t1 == .int && t2 == .int then
        return .int
      else
        none
    | .eq =>
      if t1 == t2 then
        return t1
      else
        none
  | .seq e1 e2 => typeOf ctx e1 >>= λ _ => typeOf ctx e2
  | .mem base offset => do
    let base ← typeOf ctx base
    let offset ← typeOf ctx offset
    if base == .ref && offset == .int then
      return .ref
    else
      none
  | .assign lhs rhs => do
    let lhs ← typeOf ctx lhs
    let rhs ← typeOf ctx rhs
    if lhs == .ref && rhs == .ref then
      none
    else
      return .unit
  | .let_bind name ty rhs body => do
    let rhs ← typeOf ctx rhs
    if rhs != ty then
      none
    else
      let ctx := ctx.insert name ty
      typeOf ctx body
  | .for_loop lv _ _ _ body =>
    let ctx := ctx.insert lv .int
    typeOf ctx body
  | .ite cond then_body else_body => do
    let cond ← typeOf ctx cond
    let then_body ← typeOf ctx then_body
    let else_body ← typeOf ctx else_body
    if cond != .bool || then_body != else_body then
      none
    else
      then_body

namespace Syntax
  open Lean Elab Meta

  declare_syntax_cat typ
  declare_syntax_cat exp

  syntax "unit" : typ
  syntax "int" : typ
  syntax "bool" : typ
  syntax "ref" : typ

  syntax "()" : exp -- unit term
  syntax:100 "(" exp ")" : exp -- parens
  syntax:100 num : exp -- int literal
  syntax:100 ident : exp -- vars
  syntax:50 exp:50 " + " exp:51 : exp -- add
  syntax:40 exp:40 " == " exp:40 : exp -- eq
  syntax:10 exp:11 "; " exp:10 : exp -- seq
  syntax:80 exp:30 "[" exp:30 "]" : exp -- mem
  syntax:20 exp:21 " = " exp:21 : exp -- assign
  syntax:20 "let " ident " : " typ " = " exp:21 "; " exp:20 : exp -- let
  syntax:30 "for " ident " in " num ".." num ".." num " { " exp:0 " } " : exp -- for
  syntax:30 "if " exp:31 " { " exp:0 " } else { " exp:0 " } " : exp -- if

  def elabTyp : Syntax → MetaM Expr
    | `(typ| unit) => return .const ``Ty.unit []
    | `(typ| int) => return .const ``Ty.int []
    | `(typ| bool) => return .const ``Ty.bool []
    | `(typ| ref) => return .const ``Ty.ref []
    | _ => throwUnsupportedSyntax

  partial def elabExp : Syntax → MetaM Expr
    | `(exp| ()) => return .const ``Exp.unit_term []
    | `(exp| ( $e:exp )) => elabExp e
    | `(exp| $n:num) => do
      let n ← mkAppM ``Int.ofNat #[mkNatLit n.getNat]
      mkAppM ``Exp.int_lit  #[n]
    | `(exp| $id:ident) => mkAppM ``Exp.var #[mkStrLit id.getId.toString]
    | `(exp| $e1:exp + $e2:exp) => do
      let bop := .const ``BinOp.add []
      let e1 ← elabExp e1
      let e2 ← elabExp e2
      mkAppM ``Exp.binop #[bop, e1, e2]
    | `(exp| $e1:exp == $e2:exp) => do
      let bop := .const ``BinOp.eq []
      let e1 ← elabExp e1
      let e2 ← elabExp e2
      mkAppM ``Exp.binop #[bop, e1, e2]
    | `(exp| $e1:exp; $e2:exp) => do
      let e1 ← elabExp e1
      let e2 ← elabExp e2
      mkAppM ``Exp.seq #[e1, e2]
    | `(exp| $base:exp[$offset:exp]) => do
      let base ← elabExp base
      let offset ← elabExp offset
      mkAppM ``Exp.mem #[base, offset]
    | `(exp| $lhs:exp = $rhs:exp) => do
      let lhs ← elabExp lhs
      let rhs ← elabExp rhs
      mkAppM ``Exp.assign #[lhs, rhs]
    | `(exp| let $id:ident : $t:typ = $rhs:exp; $body:exp) => do
      let id := mkStrLit id.getId.toString
      let t ← elabTyp t
      let rhs ← elabExp rhs
      let body ← elabExp body
      mkAppM ``Exp.let_bind #[id, t, rhs, body]
    | `(exp| for $lv:ident in $start:num..$stop:num..$step:num { $body:exp }) => do
      let lv := mkStrLit lv.getId.toString
      let start ← mkAppM ``Int.ofNat #[mkNatLit start.getNat]
      let stop ← mkAppM ``Int.ofNat #[mkNatLit stop.getNat]
      let step ← mkAppM ``Int.ofNat #[mkNatLit step.getNat]
      let body ← elabExp body
      mkAppM ``Exp.for_loop #[lv, start, stop, step, body]
    | `(exp| if $cond:exp { $then_body:exp } else { $else_body:exp }) => do
      let cond ← elabExp cond
      let then_body ← elabExp then_body
      let else_body ← elabExp else_body
      mkAppM ``Exp.ite #[cond, then_body, else_body]
    | _ => throwUnsupportedSyntax

  elab " 〚 " e:exp " 〛 " : term => elabExp e

  #reduce 〚
    let x : int = 0;
    for i in 0 .. 10 .. 1 {
      if A[i] == i {
        A[i] = x
      } else {
        x = A[i]
      };
      x = x + i
    };
    x
  〛

end Syntax
