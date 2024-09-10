import Mathlib.Data.Vector.Defs
import Mathlib.Data.Stream.Defs
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith.Frontend

import Spacetalk.HList

open Mathlib

-- Bit rep?
class Denote (τ : Type) [BEq τ] [LawfulBEq τ] where
  denote : τ → Type
  default : (t : τ) → denote t

section
variable {τ : Type}
variable [BEq τ]
variable [LawfulBEq τ]
variable [Denote τ]

/-- Lean denotation of a (List τ) where τ implements Denote -/
abbrev DenoList (ts : List τ) := HList Denote.denote ts

/-- Lean denotation of a list of sterams of type τ where τ implements Denote -/
abbrev DenoStreamsList (ts : List τ) := HList Stream' (ts.map Denote.denote)

@[simp]
def DenoStreamsList.Forall {ts : List τ} (dsl : DenoStreamsList ts) (p : {t : τ} → Stream' (Denote.denote t) → Prop) : Prop :=
  match ts, dsl with
    | [], []ₕ => True
    | _::_, x ::ₕ t => p x ∧ Forall t p

def DenoStreamsList.map {τ' : Type} [BEq τ'] [LawfulBEq τ'] [Denote τ']
  (f : τ → τ') (g : {t : τ} → Denote.denote t → Denote.denote (f t)) :
  {ts : List τ} → DenoStreamsList ts → DenoStreamsList (ts.map f)
  | [], []ₕ => []ₕ
  | _::_, vh ::ₕ vt => (λ i => g (vh i)) ::ₕ DenoStreamsList.map f g vt

/-- Lean denotation of a steram of list of type τ where τ implements Denote -/
abbrev DenoListsStream (ts : List τ) := Stream' (DenoList ts)

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
  induction ts with
  | nil =>
    simp [DenoStreamsList] at dsl
    simp
    cases dsl
    · rfl
  | cons h t ih => aesop

theorem DenoListsStream_unpack_pack_eq {ts : List τ} {dls : DenoListsStream ts}
  : dls.unpack.pack = dls := by
  apply funext
  intro n
  induction ts
  case nil =>
    cases dls n
    rfl
  case cons h t ih =>
    cases hm : dls n with
    | cons hh tt =>
      aesop

abbrev NodeType (τ : Type) [BEq τ] [LawfulBEq τ] [Denote τ] :=
  (inputs : List τ) → (outputs : List τ) → (state : List τ) → Type

class NodeOps (F : NodeType τ) where
  eval : F inputs outputs state → DenoList inputs → DenoList state → (DenoList outputs × DenoList state)

variable {F : NodeType τ}
variable [NodeOps F]

structure Node (τ : Type) [BEq τ] [LawfulBEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  state : List τ
  initialState : DenoList state
  ops : F inputs outputs state

def NodeList (τ : Type) [BEq τ] [LawfulBEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] (numNodes : Nat) :=
  Vector (Node τ F) numNodes

structure InputFIFO (inputs : List τ) (nodes : NodeList τ F numNodes) where
  t : τ
  producer : Member t inputs
  consumer : Fin numNodes
  consumerPort: Member t (nodes.get consumer).inputs

structure OutputFIFO (outputs : List τ) (nodes : NodeList τ F numNodes) where
  t : τ
  producer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumer : Member t outputs

structure AdvancingFIFO (nodes : NodeList τ F numNodes) where
  t : τ
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumerPort: Member t (nodes.get consumer).inputs
  /-- We put consumers earlier in the nodes list because `Vector.cons` puts new nodes in the front. -/
  adv : producer > consumer

structure InitializedFIFO (nodes : NodeList τ F numNodes) where
  t : τ
  initialValue : Denote.denote t
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumerPort: Member t (nodes.get consumer).inputs

inductive FIFO (inputs outputs : List τ) (nodes : NodeList τ F numNodes)
  | input : InputFIFO inputs nodes → FIFO inputs outputs nodes
  | output : OutputFIFO outputs nodes → FIFO inputs outputs nodes
  | advancing : AdvancingFIFO nodes → FIFO inputs outputs nodes
  | initialized : InitializedFIFO nodes → FIFO inputs outputs nodes

namespace FIFO
section
variable {numNodes : Nat}
variable {nodes : NodeList τ F numNodes}

  @[simp]
  def t {inputs outputs : List τ} : (fifo : FIFO inputs outputs nodes) → τ
    | .input f | .output f | .advancing f | .initialized f => f.t

  @[simp]
  def isInput {inputs outputs : List τ} : (fifo : FIFO inputs outputs nodes) → Bool
    | .input _ => true
    | _ => false

  @[simp]
  def isOutput {inputs outputs : List τ} : (fifo : FIFO inputs outputs nodes) → Bool
    | .output _ => true
    | _ => false

  theorem outputNotInput {inputs outputs : List τ} {fifo : FIFO inputs outputs nodes}
    : fifo.isOutput = true → fifo.isInput = false := by
    intro h
    cases h_match : fifo <;> repeat (first | simp | simp [h_match, FIFO.isOutput] at h)

  theorem inputNotOutput {inputs outputs : List τ} {fifo : FIFO inputs outputs nodes}
    : fifo.isInput = true → fifo.isOutput = false := by
    intro h
    cases h_match : fifo <;> repeat (first | simp [FIFO.isOutput] | simp [h_match] at h)

  @[simp]
  def producer {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → fifo.isInput = false → Fin numNodes
    | .initialized f, _ | .advancing f, _ | .output f, _ => f.producer

  @[simp]
  def producerPort {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → (h : fifo.isInput = false) → Member fifo.t (nodes.get (fifo.producer h)).outputs
    | .initialized f, _ | .advancing f, _ | .output f, _ => f.producerPort

  @[simp]
  def consumer {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → fifo.isOutput = false → Fin numNodes
    | .initialized f, _ | .advancing f, _ | .input f, _ => f.consumer

  @[simp]
  def consumerPort {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → (h : fifo.isOutput = false) → Member fifo.t (nodes.get (fifo.consumer h)).inputs
    | .initialized f, _ | .advancing f, _ | .input f, _ => f.consumerPort

  @[simp]
  def getInput {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → Option (InputFIFO inputs nodes)
    | input f => some f
    | _ => none

  @[simp]
  def getInputs {inputs outputs : List τ}
    (fifos : List (FIFO inputs outputs nodes)) : List (InputFIFO inputs nodes) :=
    fifos.filterMap getInput

  @[simp]
  def getOutput {inputs outputs : List τ}
    : (fifo : FIFO inputs outputs nodes) → Option (OutputFIFO outputs nodes)
    | output f => some f
    | _ => none

  @[simp]
  def getOutputs {inputs outputs : List τ}
    (fifos : List (FIFO inputs outputs nodes)) : List (OutputFIFO outputs nodes) :=
    fifos.filterMap getOutput
end
end FIFO

structure DataflowGraph (τ : Type) [BEq τ] [LawfulBEq τ] [Denote τ] (F : NodeType τ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  numNodes : Nat
  nodes : NodeList τ F numNodes
  fifos : List (FIFO inputs outputs nodes)

namespace Node

end Node

namespace DataflowGraph

  abbrev FIFOType (dfg : DataflowGraph τ F) := FIFO dfg.inputs dfg.outputs dfg.nodes

  @[simp]
  def isNodeInput {dfg : DataflowGraph τ F} {nid : Fin dfg.numNodes} {t : τ}
    (port : Member t (dfg.nodes.get nid).inputs) (fifo : dfg.FIFOType) : Bool :=
    match fifo with
      | .input fifo' | .initialized fifo' | .advancing fifo' =>
        fifo'.t == t && fifo'.consumer == nid && fifo'.consumerPort.compare port
      | _ => false

  @[simp]
  def findGlobalOutput (dfg : DataflowGraph τ F) (output : Member t dfg.outputs)
    : Option {fifo : OutputFIFO dfg.outputs dfg.nodes // fifo.t == t} :=
    let outputs := dfg.fifos.filterMap FIFO.getOutput
    let fifo := outputs.find? (λ fifo => fifo.t == t && fifo.consumer.compare output)
    match h : fifo with
    | some f =>
        some ⟨f, by have := List.find?_some h; exact Bool.and_elim_left this⟩
    | none => none

  abbrev stateMap (dfg : DataflowGraph τ F) :=
    (nid : Fin dfg.numNodes) → (DenoList (dfg.nodes.get nid).outputs) × (DenoList (dfg.nodes.get nid).state)

  theorem node_input_fifo_ty_eq {dfg : DataflowGraph τ F}
    {nid : Fin dfg.numNodes} {fin : Fin (dfg.nodes.get nid).inputs.length}
    {port : Member ((dfg.nodes.get nid).inputs.get fin) (dfg.nodes.get nid).inputs} {fifo : FIFO dfg.inputs dfg.outputs dfg.nodes}
    (h_is_node_input : dfg.isNodeInput port fifo = true) : fifo.t = (dfg.nodes.get nid).inputs.get fin := by
    cases h_fm : fifo <;> simp [h_fm, isNodeInput] at h_is_node_input <;>
    (
      rename_i fifo'
      exact h_is_node_input.left.left
    )

  theorem advancing_fifo_lt {dfg : DataflowGraph τ F}
    {nid : Fin dfg.numNodes} {fin : Fin (dfg.nodes.get nid).inputs.length}
    {port : Member ((dfg.nodes.get nid).inputs.get fin) (dfg.nodes.get nid).inputs} {fifo : AdvancingFIFO dfg.nodes}
    (h_is_node_input : dfg.isNodeInput port (.advancing fifo) = true) : nid < fifo.producer := by
    have : fifo.consumer = nid := by
      simp [isNodeInput] at h_is_node_input
      exact h_is_node_input.left.right
    rw [←this]
    exact fifo.adv

  def nthCycleState (dfg : DataflowGraph τ F) (inputs : DenoListsStream dfg.inputs) : Nat -> dfg.stateMap :=
    λ n nid =>
      let node := dfg.nodes.get nid
      let inputsFinRange := List.finRange node.inputs.length
      have finRange_map_eq : inputsFinRange.map node.inputs.get = node.inputs := List.finRange_map_get node.inputs
      let nodeInputs : (DenoList node.inputs) := finRange_map_eq ▸ inputsFinRange.toHList node.inputs.get (
        λ fin =>
          let port := node.inputs.nthMember fin
          let fifoOpt := dfg.fifos.find? (dfg.isNodeInput port)
          match h_match_opt : fifoOpt with
            | .some fifo =>
              have h_is_node_input : dfg.isNodeInput port fifo = true := List.find?_some h_match_opt
              have h_ty_eq : fifo.t = node.inputs.get fin := node_input_fifo_ty_eq (h_is_node_input)
              match fifo with
                | .input fifo' =>
                  h_ty_eq ▸ (inputs n).get fifo'.producer
                | .advancing fifo' =>
                  have := advancing_fifo_lt h_is_node_input
                  let producerOutputs := (dfg.nthCycleState inputs n fifo'.producer).fst
                  h_ty_eq ▸ producerOutputs.get fifo'.producerPort
                | .initialized fifo' =>
                  match n with
                    | 0 => h_ty_eq ▸ fifo'.initialValue
                    | n' + 1 =>
                      let producerOutputs := (dfg.nthCycleState inputs n' fifo'.producer).fst
                      h_ty_eq ▸ producerOutputs.get fifo'.producerPort
            | .none =>
              Denote.default (node.inputs.get fin)
      )
      let currState : DenoList node.state :=
        match n with
         | 0 => node.initialState
         | n' + 1 => (dfg.nthCycleState inputs n' nid).snd
      (NodeOps.eval node.ops) nodeInputs currState
    termination_by n nid => (n, dfg.numNodes - nid)

  @[simp]
  def denote (dfg : DataflowGraph τ F)
    (inputs : DenoStreamsList dfg.inputs) : DenoStreamsList (dfg.outputs) :=
    let packedInputs := inputs.pack
    let stateStream := dfg.nthCycleState packedInputs
    let outputsFinRange := List.finRange dfg.outputs.length
    have finRange_map_eq : outputsFinRange.map dfg.outputs.get = dfg.outputs := List.finRange_map_get dfg.outputs
    let packedOutputStream : DenoListsStream dfg.outputs :=
      λ n =>
        finRange_map_eq ▸ outputsFinRange.toHList dfg.outputs.get (
          λ fin =>
            let outputMem : Member (dfg.outputs.get fin) dfg.outputs := dfg.outputs.nthMember fin
            let fifoOpt : Option {fifo : OutputFIFO dfg.outputs dfg.nodes // fifo.t == dfg.outputs.get fin} :=
              dfg.findGlobalOutput outputMem
            match fifoOpt with
              | .some ⟨fifo, h⟩ =>
                let outputs : DenoList (dfg.nodes.get fifo.producer).outputs := (stateStream n fifo.producer).fst
                let output : Denote.denote fifo.t := outputs.get fifo.producerPort
                (eq_of_beq h) ▸ output
              | .none =>
                Denote.default (dfg.outputs.get fin)
        )
    packedOutputStream.unpack

end DataflowGraph

end
