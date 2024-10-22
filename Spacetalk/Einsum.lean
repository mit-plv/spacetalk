import Lean
-- Z[m,n] = A[k,m] · B[k,n]


namespace Einsum

abbrev Var := String
abbrev Shape := List Var

structure Tensor where
  tensor : Var
  shape : Shape

inductive Einsum
  | tensor : Tensor → Einsum
  | mult : Einsum → Einsum → Einsum
  | assign : Tensor → Einsum → Einsum

open Lean Elab Meta

declare_syntax_cat shape
declare_syntax_cat tensor
declare_syntax_cat einsum

syntax ident : shape
syntax ident "," shape : shape

syntax ident "[" "]" : tensor
syntax ident "[" shape "]" : tensor

syntax:100 tensor : einsum
syntax:50 einsum:50 " · " einsum:51 : einsum
syntax:10 tensor " = " einsum : einsum

def Tensor.scalar (t : Var) : Tensor :=
  ⟨t, []⟩

def Shape.single (i : Var) : Shape := [i]

partial def elabShape : Syntax → MetaM Expr
  | `(shape| $i:ident) => mkAppM ``Shape.single #[mkStrLit i.getId.toString]
  | `(shape| $i:ident,$s:shape) => do
    let s ← elabShape s
    mkAppM ``List.cons #[mkStrLit i.getId.toString, s]
  | _ => throwUnsupportedSyntax

def elabTensor : Syntax → MetaM Expr
  | `(tensor| $i:ident []) => mkAppM ``Tensor.scalar #[mkStrLit i.getId.toString]
  | `(tensor| $i:ident [ $s:shape ]) => do
    let s ← elabShape s
    mkAppM ``Tensor.mk #[mkStrLit i.getId.toString, s]
  | _ => throwUnsupportedSyntax

partial def elabEinsum : Syntax → MetaM Expr
  | `(einsum| $t:tensor) => do
    let t ← elabTensor t
    mkAppM ``Einsum.tensor #[t]
  | `(einsum| $e1:einsum · $e2:einsum) => do
    let e1 ← elabEinsum e1
    let e2 ← elabEinsum e2
    mkAppM ``Einsum.mult #[e1, e2]
  | `(einsum| $t:tensor = $e:einsum) => do
    let t ← elabTensor t
    let e ← elabEinsum e
    mkAppM ``Einsum.assign #[t, e]
  | _ => throwUnsupportedSyntax

elab " 〚 " e:einsum " 〛 " : term => elabEinsum e

#check 〚 Z[m,n] = A[k,m] · B[k,n] 〛

end Einsum
