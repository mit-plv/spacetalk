import Mathlib.Data.Vector.Defs
import Mathlib.Data.Stream.Defs
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith.Frontend

import Spacetalk.HList

open Mathlib

----------------------------------------------------------------------------------------------------
/-- Syntax -/

-- Bit rep?
class Denote (τ : Type) [DecidableEq τ] where
  denote : τ → Type
  default : (t : τ) → denote t

section
variable {τ : Type}
variable [DecidableEq τ]
variable [Denote τ]

/-- Lean denotation of a (List τ) where τ implements Denote -/
abbrev DenoList (ts : List τ) := HList Denote.denote ts

/-- Lean denotation of a list of sterams of type τ where τ implements Denote -/
abbrev DenoStreamsList (ts : List τ) := HList Stream' (ts.map Denote.denote)

/-- Lean denotation of a steram of list of type τ where τ implements Denote -/
abbrev DenoListsStream (ts : List τ) := Stream' (DenoList ts)
abbrev NodeType (τ : Type) [DecidableEq τ] [Denote τ] :=
  (inputs : List τ) → (outputs : List τ) → (state : List τ) → Type

class NodeOps (F : NodeType τ) where
  eval : F inputs outputs state → DenoList inputs → DenoList state → (DenoList outputs × DenoList state)

variable {F : NodeType τ}
variable [NodeOps F]

structure Node (τ : Type) [DecidableEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  state : List τ
  initialState : DenoList state
  ops : F inputs outputs state

def NodeList (τ : Type) [DecidableEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] (numNodes : Nat) :=
  Vector (Node τ F) numNodes

structure InputFIFO where
  producer : Nat
  consumer : Nat
  consumerPort: Nat

structure OutputFIFO where
  producer : Nat
  producerPort: Nat
  consumer : Nat

structure AdvancingFIFO where
  producer : Nat
  consumer : Nat
  producerPort: Nat
  consumerPort: Nat
  /-- We put consumers earlier in the nodes list because `Vector.cons` puts new nodes in the front. -/
  adv : producer > consumer

structure InitializedFIFO where
  α : Type
  initialValue : α
  producer : Nat
  consumer : Nat
  producerPort: Nat
  consumerPort: Nat

inductive FIFO
  | input : InputFIFO → FIFO
  | output : OutputFIFO → FIFO
  | advancing : AdvancingFIFO → FIFO
  | initialized : InitializedFIFO → FIFO

namespace FIFO
  @[simp]
  def isInput : FIFO → Bool
    | .input _ => true
    | _ => false

  @[simp]
  def isOutput : FIFO → Bool
    | .output _ => true
    | _ => false

  theorem outputNotInput {fifo : FIFO}
    : fifo.isOutput = true → fifo.isInput = false := by
    intro h
    cases h_match : fifo <;> repeat (first | simp | simp [h_match, FIFO.isOutput] at h)

  theorem inputNotOutput {fifo : FIFO}
    : fifo.isInput = true → fifo.isOutput = false := by
    intro h
    cases h_match : fifo <;> repeat (first | simp [FIFO.isOutput] | simp [h_match] at h)

  @[simp]
  def producer : (fifo : FIFO) → fifo.isInput = false → Nat
    | .initialized f, _ | .advancing f, _ | .output f, _ => f.producer

  @[simp]
  def producerPort : (fifo : FIFO) → fifo.isInput = false → Nat
    | .initialized f, _ | .advancing f, _ | .output f, _ => f.producerPort

  @[simp]
  def consumer : (fifo : FIFO) → fifo.isOutput = false → Nat
    | .initialized f, _ | .advancing f, _ | .input f, _ => f.consumer

  @[simp]
  def consumerPort : (fifo : FIFO) → fifo.isOutput = false → Nat
    | .initialized f, _ | .advancing f, _ | .input f, _ => f.consumerPort

  @[simp]
  def getInput : FIFO → Option InputFIFO
    | input f => some f
    | _ => none

  @[simp]
  def getInputs (fifos : List FIFO) : List InputFIFO :=
    fifos.filterMap getInput

  @[simp]
  def getOutput : FIFO → Option OutputFIFO
    | output f => some f
    | _ => none

  @[simp]
  def getOutputs (fifos : List FIFO) : List OutputFIFO :=
    fifos.filterMap getOutput

  @[simp]
  def isNodeInput (nid : Nat) (port : Nat) (fifo : FIFO) : Bool :=
    match fifo with
    | .input fifo' | .initialized fifo' | .advancing fifo' =>
      fifo'.consumer = nid ∧ fifo'.consumerPort = port
    | _ => false

  @[simp]
  def findNodeInput (fifos : List FIFO) (nid : Nat) (port : Nat) : Option FIFO :=
    fifos.find? (isNodeInput nid port)

  @[simp]
  def findOutput (fifos : List FIFO) (output : Nat) : Option OutputFIFO :=
    let outputs := fifos.filterMap FIFO.getOutput
    outputs.find? (λ fifo => fifo.consumer = output)
end FIFO

structure DataflowGraph (τ : Type) [DecidableEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  numNodes : Nat
  nodes : NodeList τ F numNodes
  fifos : List FIFO

abbrev fifo_idx_valid (inputs outputs : List τ) (nodes : NodeList τ F numNodes) (fifos : List FIFO) : Prop :=
  ∀ f ∈ fifos,
    match f with
    | .input f =>
      f.producer < inputs.length
        ∧ f.consumer < nodes.length
    | .output f =>
      f.consumer < nodes.length
        ∧ f.consumer < outputs.length
    | .advancing f =>
      f.producer < nodes.length
        ∧ f.consumer < nodes.length
    | .initialized f =>
      f.producer < nodes.length
        ∧ f.consumer < nodes.length

abbrev fifos_fully_connected (nodes : NodeList τ F numNodes) (fifos : List FIFO) : Prop :=
  ∀ (nid : Fin numNodes) (port : Fin (nodes.get nid).inputs.length),
    (FIFO.findNodeInput fifos nid port).isSome = true
      ∧ (FIFO.findNodeInput fifos nid port).map (FIFO.isNodeInput nid port) = true

abbrev node_inputs_well_typed {nodes : NodeList τ F numNodes} (idx_valid : fifo_idx_valid inputs outputs nodes fifos) : Prop :=
  ∀ (nid : Fin numNodes) (port : Fin (nodes.get nid).inputs.length) (fifo : FIFO),
    (h : fifo ∈ fifos) → (h_input : fifo.isNodeInput nid port) →
      match h_fifo : fifo with
      | .input f =>
        let idx : Fin inputs.length := ⟨f.producer, by
          have := idx_valid fifo (h_fifo ▸ h)
          simp [h_fifo] at this
          exact this.left
        ⟩
        inputs.get idx = (nodes.get nid).inputs.get port
      | _ => True

structure dfg_well_formed (dfg : DataflowGraph τ F) where
  fifo_idx : fifo_idx_valid dfg.inputs dfg.outputs dfg.nodes dfg.fifos
  fifos_fc : fifos_fully_connected dfg.nodes dfg.fifos
  inputs_type : node_inputs_well_typed fifo_idx

----------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------
/-- Semantics -/

@[simp]
def DenoStreamsList.Forall {ts : List τ} (dsl : DenoStreamsList ts) (p : {t : τ} → Stream' (Denote.denote t) → Prop) : Prop :=
  match ts, dsl with
  | [], []ₕ => True
  | _::_, x ::ₕ t => p x ∧ Forall t p

def DenoStreamsList.map {τ' : Type} [DecidableEq τ'] [Denote τ']
  (f : τ → τ') (g : {t : τ} → Denote.denote t → Denote.denote (f t)) :
  {ts : List τ} → DenoStreamsList ts → DenoStreamsList (ts.map f)
  | [], []ₕ => []ₕ
  | _::_, vh ::ₕ vt => (λ i => g (vh i)) ::ₕ DenoStreamsList.map f g vt

@[simp]
def DenoStreamsList.split {as : List τ} {bs : List τ}
  (dsl : DenoStreamsList (as ++ bs)) : DenoStreamsList as × DenoStreamsList bs :=
  match as with
  | [] => ([]ₕ, dsl)
  | _::_ =>
    let (l, r) := DenoStreamsList.split dsl.tail
    (dsl.head ::ₕ l, r)

@[simp]
def DenoStreamsList.pack {ts : List τ} (dsl : DenoStreamsList ts) : DenoListsStream ts :=
  match ts with
  | [] => λ _ => []ₕ
  | h::t =>
    λ n =>
      let h_elem : (Denote.denote h) := (dsl.get .head) n
      let tail_streams : DenoStreamsList t :=
        match dsl with
          | _ ::ₕ rest => rest
      h_elem ::ₕ (pack tail_streams) n

@[simp]
def DenoListsStream.unpack {ts : List τ} (dls : DenoListsStream ts) : DenoStreamsList ts :=
  match ts with
  | [] => []ₕ
  | h::t =>
    let h_stream : Stream' (Denote.denote h) := λ n => (dls n).get .head
    let t_stream : DenoListsStream t := λ n =>
      match dls n with
      | _ ::ₕ rest => rest
    h_stream ::ₕ unpack t_stream

theorem DenoStreamsList_pack_unpack_eq {ts : List τ} {dsl : DenoStreamsList ts}
  : dsl.pack.unpack = dsl := by
  induction ts <;> (cases dsl; simp_all)

theorem DenoListsStream_unpack_pack_eq {ts : List τ} {dls : DenoListsStream ts}
  : dls.unpack.pack = dls := by
  apply funext
  intro n
  induction ts <;> (cases hm : dls n; simp_all)


namespace DataflowGraph

  abbrev stateMap (dfg : DataflowGraph τ F) :=
    (nid : Fin dfg.numNodes) → (DenoList (dfg.nodes.get nid).outputs) × (DenoList (dfg.nodes.get nid).state)

  -- theorem node_input_fifo_ty_eq {dfg : DataflowGraph τ F} --   {nid : Fin dfg.numNodes} {fin : Fin (dfg.nodes.get nid).inputs.length} --   {port : Member ((dfg.nodes.get nid).inputs.get fin) (dfg.nodes.get nid).inputs} {fifo : FIFO dfg.inputs dfg.outputs dfg.nodes} --   (h_is_node_input : dfg.isNodeInput port fifo = true) : fifo.t = (dfg.nodes.get nid).inputs.get fin := by --   cases h_fm : fifo <;> simp [h_fm, isNodeInput] at h_is_node_input <;> --   (
  --     rename_i fifo'
  --     exact h_is_node_input.left
  --   )

  -- theorem advancing_fifo_lt {dfg : DataflowGraph τ F}
  --   {nid : Fin dfg.numNodes} {fin : Fin (dfg.nodes.get nid).inputs.length}
  --   {port : Member ((dfg.nodes.get nid).inputs.get fin) (dfg.nodes.get nid).inputs} {fifo : AdvancingFIFO dfg.nodes}
  --   (h_is_node_input : dfg.isNodeInput port (.advancing fifo) = true) : nid < fifo.producer := by
  --   have : fifo.consumer = nid := by
  --     simp [isNodeInput] at h_is_node_input
  --     exact h_is_node_input.right.left
  --   rw [←this]
  --   exact fifo.adv

  def nthCycleState (dfg : DataflowGraph τ F) (wf : dfg_well_formed dfg) (inputs : DenoListsStream dfg.inputs) : Nat -> dfg.stateMap :=
    λ n nid =>
      let node := dfg.nodes.get nid
      let nthInput (port : Fin node.inputs.length) : Denote.denote (node.inputs.get port) :=
          let fifoOpt := FIFO.findNodeInput dfg.fifos nid port
          have : fifoOpt.isSome = true := (wf.fifos_fc nid port).left
          match h_some : fifoOpt with
          | .some fifo =>
            have h_mem : fifo ∈ dfg.fifos := List.mem_of_find?_eq_some h_some
            have h_input : fifo.isNodeInput nid port := List.find?_some h_some

            match h_fifo : fifo with
            | .input f =>
              have h_lt : f.producer < dfg.inputs.length := by
                have := wf.fifo_idx fifo (h_fifo ▸ h_mem)
                simp [h_fifo] at this
                exact this.left
              let idx : Fin dfg.inputs.length := ⟨f.producer, h_lt⟩
              have h_ty_eq : dfg.inputs.get idx = node.inputs.get port := by
                have h_wf := wf.inputs_type nid port fifo (h_fifo ▸ h_mem) (h_fifo ▸ h_input)
                subst h_fifo
                exact h_wf
              h_ty_eq ▸ (inputs n).getNth idx
            | .advancing f =>
              sorry
            | .initialized f =>
              sorry
      let inputsFinRange := List.finRange node.inputs.length
      have finRange_map_eq : inputsFinRange.map node.inputs.get = node.inputs := List.finRange_map_get node.inputs
      let nodeInputs : (DenoList node.inputs) := finRange_map_eq ▸ inputsFinRange.toHList node.inputs.get nthInput
      let currState : DenoList node.state :=
        match n with
        | 0 => node.initialState
        | n' + 1 => (dfg.nthCycleState wf inputs n' nid).snd
      (NodeOps.eval node.ops) nodeInputs currState
  -- def nthCycleState (dfg : WFDataflowGraph) (inputs : DenoListsStream dfg.inputs) : Nat -> dfg.stateMap :=
  --   λ n nid =>
  --     let node := dfg.nodes.get nid
  --     let inputsFinRange := List.finRange node.inputs.length
  --     have finRange_map_eq : inputsFinRange.map node.inputs.get = node.inputs := List.finRange_map_get node.inputs
  --     let nodeInputs : (DenoList node.inputs) := finRange_map_eq ▸ inputsFinRange.toHList node.inputs.get (
  --       λ port =>
  --         match FIFO.findNodeInput dfg.fifos nid port with
  --         | .some fifo =>
  --           -- have h : isNodeInput port fifo = true := List.find?_some h_match
  --           -- have h_ty_eq : fifo.t = node.inputs.get fin := node_input_fifo_ty_eq h
  --           match fifo with
  --           | .input fifo' =>
  --             (inputs n).getNth fifo'.producer
  --           | .advancing fifo' =>
  --             have := advancing_fifo_lt h
  --             let producerOutputs := (dfg.nthCycleState inputs n fifo'.producer).fst
  --             h_ty_eq ▸ producerOutputs.get fifo'.producerPort
  --           | .initialized fifo' =>
  --             match n with
  --             | 0 => h_ty_eq ▸ fifo'.initialValue
  --             | n' + 1 =>
  --               let producerOutputs := (dfg.nthCycleState inputs n' fifo'.producer).fst
  --               h_ty_eq ▸ producerOutputs.get fifo'.producerPort
  --         | .none =>
  --           Denote.default (node.inputs.get fin)
  --     )
  --     let currState : DenoList node.state :=
  --       match n with
  --       | 0 => node.initialState
  --       | n' + 1 => (dfg.nthCycleState inputs n' nid).snd
  --     (NodeOps.eval node.ops) nodeInputs currState
  --   termination_by n nid => (n, dfg.numNodes - nid)

  -- @[simp]
  -- def denote (dfg : DataflowGraph τ F)
  --   (inputs : DenoStreamsList dfg.inputs) : DenoStreamsList (dfg.outputs) :=
  --   let packedInputs := inputs.pack
  --   let stateStream := dfg.nthCycleState packedInputs
  --   let outputsFinRange := List.finRange dfg.outputs.length
  --   have finRange_map_eq : outputsFinRange.map dfg.outputs.get = dfg.outputs := List.finRange_map_get dfg.outputs
  --   let packedOutputStream : DenoListsStream dfg.outputs :=
  --     λ n =>
  --       finRange_map_eq ▸ outputsFinRange.toHList dfg.outputs.get (
  --         λ fin =>
  --           let outputMem := dfg.outputs.nthMember fin
  --           let fifoOpt := dfg.findGlobalOutput outputMem
  --           match fifoOpt with
  --           | .some ⟨fifo, h⟩ =>
  --             let outputs : DenoList (dfg.nodes.get fifo.producer).outputs := (stateStream n fifo.producer).fst
  --             let output : Denote.denote fifo.t := outputs.get fifo.producerPort
  --             h ▸ output
  --           | .none =>
  --             Denote.default (dfg.outputs.get fin)
  --       )
  --   packedOutputStream.unpack

end DataflowGraph

end
