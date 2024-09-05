
-- inductive Ty
--   | bool
--   | nat
-- deriving DecidableEq

-- def Ty.denote : Ty → Type
--   | bool => Bool
--   | nat => Nat

-- inductive Typ
--   | bool
--   | nat
-- deriving DecidableEq

-- def Typ.denote : Typ → Type
--   | bool => Bool
--   | nat => Nat

-- def Ty.toTyp : Ty → Typ
--   | bool => .bool
--   | nat => .nat

-- import Mathlib.Data.List.Basic

-- structure Foo where
--   l : List Nat

-- structure Bar (l : List Nat) where
--   n : Nat
--   mem : n ∈ l

-- def find (foo : Foo) (n : Nat) : Option (Bar foo.l) :=
--   match h : foo.l.find? (· = n) with
--   | some x =>
--     some ⟨n, by
--       have hmem := List.mem_of_find?_eq_some h
--       have heq := List.find?_some h
--       simp_all
--     ⟩
--   | none => none

-- example : find ⟨[0]⟩ 0 = some ⟨0, by simp⟩ := by
--   simp [find]
--   have heq : List.find? (· = 0) [0] = some 0 := by simp
--   rw [heq]

inductive Ty
  | bv : Nat → Ty

@[reducible]
def Ty.denote : Ty → Type
  | bv w => BitVec w

inductive BinOp : Ty → Ty → Ty → Type
  | add : {w : Nat} → BinOp (.bv w) (.bv w) (.bv w)
  | eq : BinOp α α (.bv 1)

def BinOp.eval : BinOp α β γ → (α.denote → β.denote → γ.denote)
  | add => BitVec.add
  | eq => λ a b => if a == b then ⟨1⟩ else ⟨0⟩

example : ∀α x y (op : BinOp α α α), op.eval x y = op.eval x y := by
  simp
