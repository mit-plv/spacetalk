import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph

import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Vector.Basic

theorem Vector.get_append_left {xs : Vector α n} {ys : Vector α m} {i : Fin n}
  : (xs.append ys).get ⟨i, by apply Nat.lt_add_right; exact i.isLt⟩ = xs.get i := by
  apply List.get_append_left

theorem Vector.get_append_right {xs : Vector α n} {ys : Vector α m} {i : Fin m}
  : (xs.append ys).get ⟨i + n, by have := i.isLt; linarith⟩ = ys.get i := by
  simp_rw [Vector.get_eq_get]
  have := Vector.toList_append xs ys
  rw [List.get_of_eq this]
  simp [Fin.cast]
  have := List.get_append_right xs.toList ys.toList (i := i + n)
  have h_i_lt_append : ↑i + n < (xs.toList ++ ys.toList).length := by have := i.isLt; simp; linarith
  have h_i_sub_xs_lt_ys : ↑i + n - xs.toList.length < ys.toList.length := by simp
  have : List.get (xs.toList ++ ys.toList) ⟨↑i + n, h_i_lt_append⟩ = List.get ys.toList ⟨i + n - xs.toList.length, h_i_sub_xs_lt_ys⟩ := this (by rw [Vector.toList_length xs]; linarith)
  have h_eq : (⟨↑i + n - xs.toList.length, h_i_sub_xs_lt_ys⟩ : Fin ys.toList.length) = ⟨↑i, Fin.cast.proof_1 (toList_length ys).symm i⟩ := by simp
  rw [←h_eq]
  exact this

def SDFNode := Node SimpleDataflow.Ty SimpleDataflow.Ops

def SDFNodeList := NodeList SimpleDataflow.Ty SimpleDataflow.Ops

def Step.Prim.toSDF : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .prim (.bitVec w)

def Step.Prim.toSDFOpt : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .option (.bitVec w)

structure SDFOneOutput (p : Step.Prim) where
  g : SimpleDataflow.DataflowMachine
  fifo : OutputFIFO g.outputs g.nodes
  one_output : g.fifos.filter FIFO.isOutput = [.output fifo]
  ty_eq : fifo.t = p.toSDF

@[reducible]
def Step.Ty.toSDF (sty : Step.Ty) :=
  match sty with
    | .stream p => SDFOneOutput p

@[simp]
def binOpConstRightGraph {α β γ : Step.Prim} (op : SimpleDataflow.BinaryOp α.toSDF β.toSDF γ.toSDF) (c : β.denote) : SDFOneOutput γ :=
  let inputs := [α.toSDF]
  let outputs := [γ.toSDF]
  let constNode := ⟨[], [β.toSDF], [], []ₕ, .const c⟩
  let opNode := ⟨[α.toSDF, β.toSDF], [γ.toSDF], [], []ₕ, .binaryOp op⟩
  let nodes : SDFNodeList 2 := .cons opNode (.cons constNode .nil)
  have h_eq : (nodes.get 0).outputs = [γ.toSDF] := by aesop
  let outFifo : OutputFIFO outputs nodes := ⟨γ.toSDF, 0, h_eq ▸ .head, .head⟩
  let fifo := .output outFifo
  let fifos := [
    .input ⟨α.toSDF, .head, 0, .head⟩,
    .advancing ⟨β.toSDF, 1, 0, .head, .tail .head, _⟩,
    fifo
  ]
  let g : SimpleDataflow.DataflowMachine := ⟨inputs, outputs, 2, nodes, fifos⟩
  ⟨
    g,
    outFifo,
    by simp [fifos],
    by aesop
  ⟩

def binaryOpGraph {α β γ : Step.Prim} (op : SimpleDataflow.BinaryOp α.toSDF β.toSDF γ.toSDF) : SDFOneOutput γ :=
  let inputs := [α.toSDF, β.toSDF]
  let outputs := [γ.toSDF]
  let opNode : SDFNode := ⟨inputs, outputs, [], []ₕ, .binaryOp op⟩
  let nodes : SDFNodeList 1 := .cons opNode .nil
  let h_eq : (nodes.get 0).outputs = [γ.toSDF] := by aesop
  let outFifo : OutputFIFO outputs nodes := ⟨γ.toSDF, 0, h_eq ▸ .head, .head⟩
  let fifo := .output outFifo
  let fifos := [
    .input ⟨α.toSDF, .head, 0, .head⟩,
    .input ⟨β.toSDF, .tail .head, 0, .tail .head⟩,
    fifo
  ]
  let g := ⟨inputs, outputs, 1, nodes, fifos⟩
  ⟨
    g,
    (_ : outputs = g.outputs) ▸ outFifo,
    by simp [fifos],
    by aesop
  ⟩

def Step.UnaryOp.compile : Step.UnaryOp α β → SDFOneOutput β
  | .addConst c => binOpConstRightGraph .add c
  | .mulConst c => binOpConstRightGraph .mul c

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SimpleDataflow.Ops [α.toSDF, β.toSDF] [γ.toSDF] []
  | .add => .binaryOp .add
  | .mul => .binaryOp .mul

class IndexConverter {α : Type u} {n m : Nat} (h_m : 0 < m) (xs : Vector α n) (ys : Vector α m) :=
  conv : Fin n → Fin m
  conv_congr : ∀ {i}, xs.get i = ys.get (conv i)
  conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j
  conv_gt_zero: ∀ {i}, ⟨0, h_m⟩ < conv i

def consConverter : IndexConverter (Nat.zero_lt_succ _) xs (x ::ᵥ xs.append ys) :=
  let conv : Fin xs.length → Fin (x ::ᵥ xs.append ys).length := λ i ↦ ⟨i.val + 1, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, xs.get i = (x ::ᵥ xs.append ys).get (conv i) := by
    intro i
    rw [←(x ::ᵥ xs.append ys).get_tail ⟨i, Nat.lt_add_right _ i.isLt⟩]
    exact Vector.get_append_left.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  have conv_gt_zero: ∀ {i}, 0 < conv i := by
    intro i
    simp [conv]
    apply Fin.mk_lt_mk.mpr
    rw [Nat.zero_mod]
    simp
  ⟨conv, conv_congr, conv_lt, conv_gt_zero⟩

def consAppendConverter {xs : Vector α n} {ys : Vector α m} : IndexConverter (Nat.zero_lt_succ _) ys (x ::ᵥ xs.append ys) :=
  let conv : Fin m → Fin (n + m + 1) := λ i ↦ ⟨i.val + n + 1, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, ys.get i = (x ::ᵥ xs.append ys).get (conv i) := by
    intro i
    simp [conv]
    rw [←(x ::ᵥ xs.append ys).get_tail ⟨i + n, by simp; have := i.isLt; linarith⟩]
    simp
    exact Vector.get_append_right.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  have conv_gt_zero: ∀ {i}, 0 < conv i := by
    intro i
    simp [conv]
    apply Fin.mk_lt_mk.mpr
    rw [Nat.zero_mod]
    simp
  ⟨conv, conv_congr, conv_lt, conv_gt_zero⟩

/-- Assume new consumer has index 0. -/
def convertFifos {inputs outputs : List SimpleDataflow.Ty} {numNodes : Nat} {nodes : SDFNodeList numNodes}
  (h_len : 0 < numNodes) (a : SDFOneOutput α) (newConsumerPort : Member α.toSDF (nodes.get ⟨0, h_len⟩).inputs)
  (idxConv : IndexConverter h_len a.g.nodes nodes)
  (memConv : {t : SimpleDataflow.Ty} → Member t a.g.inputs → Member t inputs)
  : List (FIFO inputs outputs nodes) :=
  a.g.fifos.attach.map (
    λ ⟨fifo, h_mem⟩ ↦ match fifo with
      | .input f =>
        let newConsumer := idxConv.conv f.consumer
        let fifo : InputFIFO inputs nodes := {
          t := f.t,
          producer := memConv f.producer,
          consumer := newConsumer,
          consumerPort := idxConv.conv_congr ▸ f.consumerPort
        }
        .input fifo
      | .output f =>
        let newProducer := idxConv.conv f.producer
        have h_ty_eq : f.t = α.toSDF := by
          have : FIFO.output f = .output a.fifo := by
            apply List.mem_singleton.mp
            rw [←a.one_output]
            apply List.mem_filter.mpr (And.intro h_mem (by rfl))
          simp [FIFO.output.inj] at this
          rw [this]
          apply a.ty_eq
        let fifo : AdvancingFIFO nodes := {
          t := f.t,
          producer := newProducer,
          consumer := ⟨0, h_len⟩,
          producerPort := idxConv.conv_congr ▸ f.producerPort,
          consumerPort := h_ty_eq ▸ newConsumerPort,
          adv := idxConv.conv_gt_zero,
        }
        .advancing fifo
      | .advancing f =>
        let newProducer := idxConv.conv f.producer
        let newConsumer := idxConv.conv f.consumer
        have adv : newProducer.val > newConsumer.val := by
          simp [newProducer, newConsumer]
          apply idxConv.conv_lt
          exact f.adv
        let fifo : AdvancingFIFO nodes := {
          t := f.t,
          producer := newProducer,
          consumer := newConsumer,
          producerPort := idxConv.conv_congr ▸ f.producerPort,
          consumerPort := idxConv.conv_congr ▸ f.consumerPort,
          adv := adv
        }
        .advancing fifo
      | .initialized f =>
        let newProducer := idxConv.conv f.producer
        let newConsumer := idxConv.conv f.consumer
        let fifo : InitializedFIFO nodes := {
          t := f.t,
          initialValue := f.initialValue,
          producer := newProducer,
          consumer := newConsumer,
          producerPort := idxConv.conv_congr ▸ f.producerPort,
          consumerPort := idxConv.conv_congr ▸ f.consumerPort,
        }
        .initialized fifo
  )

def mergeGraphs (a : SDFOneOutput α) (b : SDFOneOutput β) (op : Step.BinaryOp α β γ) : SDFOneOutput γ :=
  let inputs := a.g.inputs ++ b.g.inputs
  let outputs := [γ.toSDF]
  let newNode : SDFNode := ⟨[α.toSDF, β.toSDF], [γ.toSDF], [], []ₕ, op.compile⟩
  let nodes := newNode ::ᵥ (a.g.nodes.append b.g.nodes)

  let aFifosUpdated : List (FIFO inputs outputs nodes) := convertFifos _ a .head consConverter .append_left
  let bFifosUpdated : List (FIFO inputs outputs nodes) := convertFifos _ b (.tail .head) consAppendConverter .append_right
  sorry

def Step.Prog.compile {sty : Step.Ty} : Step.Prog sty → sty.toSDF
  | @Step.Prog.const α as => sorry
  | @Step.Prog.zip α β γ op as bs =>
    let asg := as.compile
    let bsg := bs.compile
    mergeGraphs asg bsg op
  | Step.Prog.map op as => sorry
  | @Step.Prog.reduce α β op len init bs => sorry
  decreasing_by (all_goals sorry)


-- def c : SimpleDataflow.Pipeline [] [SimpleDataflow.BoolTy] :=
--   .const 1

-- def g : SimpleDataflow.DataflowMachine :=
--   let inputs : List SimpleDataflow.Ty := []
--   let outputs : List SimpleDataflow.Ty := [SimpleDataflow.BoolTy]
--   let state : List SimpleDataflow.Ty := []
--   let pipeline : SimpleDataflow.Ops inputs outputs state := c
--   let node := ⟨inputs, outputs, state, []ₕ, pipeline⟩
--   let nodes : SDFNodeList 1 := .cons node .nil
--   let fifos := [
--     .output ⟨SimpleDataflow.BoolTy, 0, .head, .head⟩
--   ]
--   ⟨inputs, outputs, 1, nodes, fifos⟩

-- namespace _hidden
--   def w := 10
--   def add1 := binOpConstRight (.add (w := w)) 1
--   def mul1 := binOpConstRight (.mul (w := w)) 1
--   def s : Stream' (BitVec w) := λ n => ⟨n % (2 ^ w), by apply Nat.mod_lt; simp⟩
--   #eval ((add1.denote [s]ₕ).head 8).toNat
-- end _hidden
