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
  Stream'.reduce BitVec.add n (bv_eq ▸ 0) (Stream'.zip BitVec.mul a b) ::ₕ .nil

def sa : Stream' (BitVec 32) := λ n => ⟨n % (2 ^ 32), Nat.mod_lt n (Nat.zero_lt_succ _)⟩

namespace Step
  def dotProd (n : Nat) : Prog [BV32, BV32] BV32 :=
    .reduce .add n 0 (.zip .mul (.const _) (.const _))
end Step

theorem step_dp_equiv : ∀n : Nat, (Step.dotProd n).denote = dotProd n := by
  intro n
  apply funext
  intro x
  apply (HList.cons.injEq _ _ _ _).mpr
  apply And.intro
  <;> repeat (first | (cases x; rename_i x) | rfl)

def sdfDP (n : Nat) := (Step.dotProd n).compile

def checkInput (n : Nat) (i : Nat) :=
  let inps : HList Stream' [BitVec 32, BitVec 32] := ([sa, sa]ₕ)
  let inpsOption : HList Stream' [Option (BitVec 32), Option (BitVec 32)] := ([
    λ n => some (sa n),
    λ n => some (sa n)
  ]ₕ)
  let step : Stream' (BitVec 32) := ((Step.dotProd n).denote inps).head
  let sdfGraph := sdfDP n
  let sdf : Stream' (Option (BitVec 32)) :=  (sdfGraph.g.denote inpsOption).head

  let step_res := (step i).toNat
  match sdf (i * n) with
  | some r => (step_res, r.toNat, r.toNat == step_res)
  | _ => (0, 0, false)

#eval checkInput 2 1
