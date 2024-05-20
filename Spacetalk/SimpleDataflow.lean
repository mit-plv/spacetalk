import Spacetalk.Graph

namespace SimpleDataflow

inductive Prim
  | bitVec : Nat → Prim
deriving DecidableEq

inductive Ty
  | option : Prim → Ty
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

def Ty.default : (ty : Ty) → ty.denote
  | .option _ => none

def Ty.denoteBEq : (ty : Ty) → (ty.denote → ty.denote → Bool)
  | .option _ => λ a b =>
    match a, b with
      | .some aa, .some bb => aa == bb
      | .none, .none => true
      | _, _ => false

def Ty.denoteDecEq : (ty : Ty) → DecidableEq ty.denote
  | .option _ => inferInstance

instance {ty : Ty} : BEq ty.denote where
  beq := ty.denoteBEq

instance {ty : Ty} : DecidableEq ty.denote :=
  ty.denoteDecEq

instance {ty : Ty} : LawfulBEq ty.denote where
  eq_of_beq := by
    intro a b h
    induction ty with
    | option _ =>
      cases a <;> cases b <;> repeat (first | contradiction | aesop)
      simp [BEq.beq, Ty.denoteBEq] at h
      simp [h]

  rfl := by
    intro a
    cases ty
    · cases a
      · rfl
      · simp [BEq.beq, Ty.denoteBEq]

instance : Denote Ty where
  denote := Ty.denote
  default := Ty.default

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

inductive UnaryOp : Prim → Prim → Type
  | identity : UnaryOp α α

def UnaryOp.eval : UnaryOp α β → (α.denote → β.denote)
  | identity => id

inductive Pipeline : (inputs : List Ty) → (outputs : List Ty) → Type
  | const : {α : Ty} → α.denote → Pipeline [] [α]
  | unaryOp : {α β : Prim} → UnaryOp α β → Pipeline [α.toTy] [β.toTy]
  | binaryOp : {α β γ : Prim} → BinaryOp α β γ → Pipeline [α.toTy, β.toTy] [γ.toTy]
  | guard : {α : Ty} → Pipeline [BoolTy, α] [α]
  | mux : {α : Ty} → Pipeline [BoolTy, α, α] [α]

def Pipeline.eval : Pipeline α β → (DenoList α → DenoList β)
  | const a => Function.const _ [a]ₕ
  | unaryOp op => λ ([a]ₕ) => [a.map op.eval]ₕ
  | binaryOp op => λ ([a, b]ₕ) =>
    let res := do
      let aVal ← a
      let bVal ← b
      pure (op.eval aVal bVal)
    [res]ₕ
  | @Pipeline.guard α => λ ([g, a]ₕ) => [g >>= (Function.const _ a)]ₕ
  | mux => λ ([cond, a, b]ₕ) =>
    let res := do
      let condVal ← cond
      if condVal == 1 then
        a
      else
        b
    [res]ₕ

def Ops (inputs outputs state : List Ty) :=
  Pipeline (inputs ++ state) (outputs ++ state)

instance : NodeOps Ops where
  eval := λ pipeline inputs state => (pipeline.eval (inputs ++ₕ state)).split

def DataflowMachine := DataflowGraph Ty Ops

end SimpleDataflow
