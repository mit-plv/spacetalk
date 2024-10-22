import Spacetalk.BoundedQueue
import Spacetalk.Graph

namespace SimpleDataflow

inductive Prim
  | bitVec : Nat → Prim
deriving DecidableEq

inductive Ty
  | option : Prim → Ty
deriving DecidableEq

inductive Mem
  | queue : Prim → Nat → Mem
deriving DecidableEq

@[reducible]
def Prim.toTy (p :Prim) : Ty :=
  .option p

@[reducible]
def Prim.denote : Prim → Type
  | bitVec w => BitVec w

def Prim.default : (p : Prim) → p.denote
  | bitVec _ => 0

@[reducible]
def Ty.denote : Ty → Type
  | option p => Option p.denote

@[simp]
def Ty.default : (ty : Ty) → ty.denote
  | .option _ => none

instance : Denote Ty where
  denote := Ty.denote
  default := Ty.default

@[reducible]
def Mem.denote : Mem → Type
  | queue p n => BoundedQueue p.denote n

@[simp]
def Mem.default : (m : Mem) → m.denote
  | queue _ n => .empty n

instance : Denote Mem where
  denote := Mem.denote
  default := Mem.default

abbrev BitVecPrim (w : Nat) := Prim.bitVec w
abbrev BoolPrim := BitVecPrim 1

abbrev BitVecTy (w : Nat) := (BitVecPrim w).toTy
abbrev BoolTy := BoolPrim.toTy

inductive BinaryOp : Prim → Prim → Prim → Type
  | add : {w : Nat} → BinaryOp (BitVecPrim w) (BitVecPrim w) (BitVecPrim w)
  | mul : {w : Nat} → BinaryOp (BitVecPrim w) (BitVecPrim w) (BitVecPrim w)
  | umod : {w : Nat} → BinaryOp (BitVecPrim w) (BitVecPrim w) (BitVecPrim w)
  | eq : BinaryOp α α BoolPrim

def BinaryOp.eval : BinaryOp α β γ → (α.denote → β.denote → γ.denote)
  | add => BitVec.add
  | mul => BitVec.mul
  | umod => BitVec.umod
  | eq => λ a b => if a == b then ⟨1, by simp⟩ else ⟨0, by simp⟩

example : ∀α x y (op : BinaryOp α α α), op.eval x y = op.eval x y := by
  simp

inductive UnaryOp : Prim → Prim → Type
  | identity : UnaryOp α α

@[simp]
def UnaryOp.eval : UnaryOp α β → (α.denote → β.denote)
  | identity => id

inductive Pipeline : (inputs : List Ty) → (outputs : List Ty) → Type
  | const : {α : Ty} → α.denote → Pipeline [] [α]
  | unaryOp : {α β : Prim} → UnaryOp α β → Pipeline [α.toTy] [β.toTy]
  | binaryOp : {α β γ : Prim} → BinaryOp α β γ → Pipeline [α.toTy, β.toTy] [γ.toTy]
  | guard : {any α : Ty} → Pipeline [any, α] [α]
  | mux : {α : Ty} → Pipeline [BoolTy, α, α] [α]

@[simp]
def Pipeline.eval : Pipeline α β → (DenoList α → DenoList β)
  | const a => Function.const _ [a]ₕ
  | unaryOp op => λ ([a]ₕ) => [a.map op.eval]ₕ
  | binaryOp op => λ ([a, b]ₕ) =>
    let res := do
      let aVal ← a
      let bVal ← b
      pure (op.eval aVal bVal)
    [res]ₕ
  | guard => λ ([g, a]ₕ) => [g >>= (Function.const _ a)]ₕ
  | mux => λ ([cond, a, b]ₕ) =>
    let res := do
      let condVal ← cond
      if condVal == 1 then
        a
      else
        b
    [res]ₕ

abbrev Ops (inputs outputs : List Ty) (state : List Mem) :=
  Pipeline inputs outputs

instance : NodeOps Ops where
  eval := λ pipeline inputs state => (pipeline.eval (inputs), )

abbrev DataflowMachine := DataflowGraph (σ := Mem) Ops

end SimpleDataflow
