import Spacetalk.Step
import Spacetalk.SimpleDataflow


def dotProd (n : Nat) (a : Stream' Nat) (b : Stream' Nat) : Stream' Nat :=
  Stream'.reduce (· + ·) n 0 (Stream'.zip (· * ·) a b)

def sa : Stream' Nat := id
def sb : Stream' Nat := id

theorem Nat.sub_one_succ {n : Nat} : 0 < n → n - 1 + 1 = n := by
  intro h
  rw [Nat.sub_add_cancel]
  exact h

namespace Step
  -- A dot product of length n vectors
  def dotProd (n : Nat) : Prog rep (.stream .nat → .stream .nat → .stream .nat) :=
    let multiply := .zip (.binop .mul)
    let reduction := .reduce (.binop .add) n 0
    .lam λ a => .lam λ b => .app reduction (.app (.app multiply (.var a)) (.var b))
end Step

theorem step_dp_equiv : ∀n : Nat, (Step.dotProd n).denote = dotProd n := by
  simp [dotProd]

namespace SimpleDataflow

  def accum (dim : Nat) : Ops [.nat] [.option .nat] [.nat, .nat] :=
    let state := [.nat, .nat] -- [counter, sum]
    let counter : Member .nat state := .head
    let sum : Member .nat state := .tail .head

    let sumUpdate : Ops [.nat] [] state := .binaryStateUpdate .add sum
    let sumOut : Ops [] [.nat] state := .unaryStateOp .id sum
    let outputGuard : Ops [.nat] [.option .nat] state := .stateUnaryGuard (.eqConst (dim - 1)) counter
    let stateReset : Ops [.option .nat] [.option .nat] state := .stateReset (.eqConst (dim - 1)) counter sum 0
    let incState : Ops [.option .nat] [.option .nat] state := .unaryStateUpdate (.incMod dim) counter

    .comp incState (.comp stateReset (.comp outputGuard (.comp sumOut sumUpdate)))

  def mul : Ops [.nat, .nat] [.nat] [] := .binaryOp .mul

  def dotProdGraph (dim : Nat) : DataflowMachine :=
    let inputs := [.nat, .nat]
    let outputs := [.option .nat]
    let mulNode : Node Ty Ops := ⟨inputs, [.nat], [], [], mul⟩
    let accumNode : Node Ty Ops := ⟨[.nat], outputs, [.nat, .nat], 0 :: 0 :: [], accum dim⟩
    let nodes : Vector (Node Ty Ops) 2:= .cons mulNode (.cons accumNode .nil)

    let mulToAccum := {
      t := .nat,
      producer := 0,
      consumer := 1,
      producerPort := .head,
      consumerPort := .head,
      adv := by simp
    }
    let inputA := {
      t := .nat,
      producer := .head,
      consumer := 0,
      consumerPort := .head,
    }
    let inputB := {
      t := .nat,
      producer := .tail .head,
      consumer := 0,
      consumerPort := .tail .head,
    }
    let output := {
      t := .option .nat,
      producer := 1,
      producerPort := .head,
      consumer := .head,
    }
    let fifos : List (FIFO inputs outputs nodes) := [
      .input inputA,
      .input inputB,
      .advancing mulToAccum,
      .output output
    ]

    {
      inputs := inputs,
      outputs := outputs,
      nodes := nodes,
      fifos := fifos
    }

  def dotProdUnfiltered (dim : Nat) (a : Stream' Nat) (b : Stream' Nat) : Stream' (Option Nat) :=
    ((dotProdGraph dim).denote (a :: b :: [])).get .head

  theorem dp_dim_some : ∀ (dim : Nat) (a : Stream' Nat) (b : Stream' Nat) (n : Nat),
    ((dotProdUnfiltered dim a b) n).isSome = true ↔ (n + 1) % dim = 0 := by
    intro dim a b n
    apply Iff.intro
    · sorry
    · intro h
      simp [dotProdUnfiltered]
      sorry

  def dotProd (dim : Nat) (h : 0 < dim) (a : Stream' Nat) (b : Stream' Nat) : Stream' Nat :=
    let unfiltered := dotProdUnfiltered dim a b
    λ n =>
      let val := unfiltered ((n + 1) * dim - 1)
      have h : val.isSome = true := by
        rw [dp_dim_some]
        have : 0 < (n + 1) * dim := by simp [h]
        calc
          ((n + 1) * dim - 1 + 1) % dim = ((n + 1) * dim) % dim := by rw [Nat.sub_one_succ this]
          _ = 0 := by rw [Nat.mul_mod_left]
      val.get h

  def dp := dotProd 10 (by decide) sa sb
  #eval dp 4

end SimpleDataflow
