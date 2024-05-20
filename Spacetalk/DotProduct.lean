import Spacetalk.Step
import Spacetalk.Compiler
import Spacetalk.SimpleDataflow

import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.ClearExcept

abbrev BV32 : Step.Ty := Step.BitVecTy 32
abbrev Inps := DenoStreamsList [BV32, BV32]
abbrev Outs := DenoStreamsList [BV32]

theorem bv_eq : Denote.denote BV32 = BitVec 32 := by simp [Denote.denote]

def dotProd (n : Nat) (inps : Inps) : Outs :=
  let a := inps.get .head
  let b := inps.get (.tail .head)
  Stream'.reduce (bv_eq ▸ · + ·) n (bv_eq ▸ 0) (Stream'.zip (bv_eq ▸ · * ·) a b) ::ₕ .nil

def sa : Stream' (BitVec 32) := λ n => ⟨n % (2 ^ 32), by apply Nat.mod_lt; simp⟩

theorem Nat.sub_one_succ {n : Nat} : 0 < n → n - 1 + 1 = n := by
  intro h
  rw [Nat.sub_add_cancel]
  exact h

namespace Step
  def dotProd (n : Nat) (h_n : 0 < n) : Prog [BV32, BV32] BV32 :=
    .reduce .add n h_n 0 (.zip .mul (.const _) (.const _))
end Step

theorem step_dp_equiv : ∀n : Nat, (h_n : 0 < n) → (Step.dotProd n h_n).denote = dotProd n := by
  simp [Step.dotProd, dotProd]

  sorry

def sdfDP (n : Nat) (h_n : 0 < n) := (Step.dotProd n h_n).compile

def checkInput (n : Nat) (h_n : 0 < n) (i : Nat) :=
  let inps := ([sa, sa]ₕ)
  let step := (Step.dotProd n h_n).denote inps
  -- let sdf := (sdfDP n h_n).g.denote inps

  0
