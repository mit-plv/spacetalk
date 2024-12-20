import Mathlib.Data.Stream.Defs
import Mathlib.Data.Vector.Basic

import Spacetalk.HList

open Mathlib

----------------------------------------------------------------------------------------------------
/-- Syntax -/

-- Bit rep?
class Denote (τ : Type) [DecidableEq τ] where
  denote : τ → Type
  default : (t : τ) → denote t

/-- Lean denotation of a (List τ) where τ implements Denote -/
abbrev DenoList {τ : Type} [DecidableEq τ] [Denote τ] (ts : List τ) :=
  HList Denote.denote ts

/-- Lean denotation of a list of sterams of type τ where τ implements Denote -/
abbrev DenoStreamsList {τ : Type} [DecidableEq τ] [Denote τ] (ts : List τ) :=
  HList Stream' (ts.map Denote.denote)

/-- Lean denotation of a steram of list of type τ where τ implements Denote -/
abbrev DenoListsStream {τ : Type} [DecidableEq τ] [Denote τ] (ts : List τ) :=
  Stream' (DenoList ts)

abbrev NodeType (τ : Type) [DecidableEq τ] [Denote τ]
                (σ : Type) [DecidableEq σ] [Denote σ] :=
  (inputs : List τ) → (outputs : List τ) → (state : List σ) → Type

section
variable {τ : Type}
variable [DecidableEq τ]
variable [Denote τ]

variable {σ : Type}
variable [DecidableEq σ]
variable [Denote σ]

class NodeOps (F : NodeType τ σ) where
  eval : F inputs outputs state → DenoList inputs → DenoList state → (DenoList outputs × DenoList state)

variable {F : NodeType τ σ}
variable [NodeOps F]

structure Node (F : NodeType τ σ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  state : List σ
  initialState : DenoList state
  ops : F inputs outputs state

def NodeList (F : NodeType τ σ) [NodeOps F] (numNodes : Nat) :=
  Vector (Node F) numNodes

structure InputFIFO (inputs : List τ) (nodes : NodeList F numNodes) where
  t : τ
  producer : Member t inputs
  consumer : Fin numNodes
  consumerPort: Member t (nodes.get consumer).inputs

structure OutputFIFO (outputs : List τ) (nodes : NodeList F numNodes) where
  t : τ
  producer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumer : Member t outputs

structure AdvancingFIFO (nodes : NodeList F numNodes) where
  t : τ
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumerPort: Member t (nodes.get consumer).inputs
  /-- We put consumers earlier in the nodes list because `Vector.cons` puts new nodes in the front. -/
  adv : producer > consumer

structure InitializedFIFO (nodes : NodeList F numNodes) where
  t : τ
  initialValue : Denote.denote t
  producer : Fin numNodes
  consumer : Fin numNodes
  producerPort: Member t (nodes.get producer).outputs
  consumerPort: Member t (nodes.get consumer).inputs

inductive FIFO (inputs outputs : List τ) (nodes : NodeList F numNodes)
  | input : InputFIFO inputs nodes → FIFO inputs outputs nodes
  | output : OutputFIFO outputs nodes → FIFO inputs outputs nodes
  | advancing : AdvancingFIFO nodes → FIFO inputs outputs nodes
  | initialized : InitializedFIFO nodes → FIFO inputs outputs nodes

structure DataflowGraph (F : NodeType τ σ) [NodeOps F] where
  inputs : List τ
  outputs : List τ
  numNodes : Nat
  nodes : NodeList F numNodes
  fifos : List (FIFO inputs outputs nodes)

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
namespace FIFO
section
variable {numNodes : Nat}
variable {nodes : NodeList F numNodes}

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
    intro; cases fifo <;> simp_all

  theorem inputNotOutput {inputs outputs : List τ} {fifo : FIFO inputs outputs nodes}
    : fifo.isInput = true → fifo.isOutput = false := by
    intro; cases fifo <;> simp_all

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

namespace DataflowGraph

  abbrev FIFOType (dfg : DataflowGraph F) := FIFO dfg.inputs dfg.outputs dfg.nodes

  @[simp]
  def isNodeInput {dfg : DataflowGraph F} {nid : Fin dfg.numNodes} {t : τ}
    (port : Member t (dfg.nodes.get nid).inputs) (fifo : dfg.FIFOType) : Bool :=
    match fifo with
    | .input fifo' | .initialized fifo' | .advancing fifo' =>
      fifo'.t = t ∧ fifo'.consumer = nid ∧ fifo'.consumerPort.compare port
    | _ => false

  @[simp]
  def findNodeInput {dfg : DataflowGraph F} {nid : Fin dfg.numNodes} {t : τ}
    (port : Member t (dfg.nodes.get nid).inputs) : Option dfg.FIFOType :=
    dfg.fifos.find? (isNodeInput port)

  @[simp]
  def findGlobalOutput (dfg : DataflowGraph F) (output : Member t dfg.outputs)
    : Option {fifo : OutputFIFO dfg.outputs dfg.nodes // fifo.t = t} :=
    let outputs := dfg.fifos.filterMap FIFO.getOutput
    let fifo := outputs.find? (λ fifo => fifo.t = t ∧ fifo.consumer.compare output)
    match h : fifo with
    | some f => some ⟨f, by have := List.find?_some h; simp_all⟩
    | none => none

  abbrev stateMap (dfg : DataflowGraph F) :=
    (nid : Fin dfg.numNodes) → (DenoList (dfg.nodes.get nid).outputs) × (DenoList (dfg.nodes.get nid).state)

  theorem node_input_fifo_ty_eq {dfg : DataflowGraph F}
    {nid : Fin dfg.numNodes} {fin : Fin (dfg.nodes.get nid).inputs.length}
    {port : Member ((dfg.nodes.get nid).inputs.get fin) (dfg.nodes.get nid).inputs} {fifo : FIFO dfg.inputs dfg.outputs dfg.nodes}
    (h_is_node_input : dfg.isNodeInput port fifo = true) : fifo.t = (dfg.nodes.get nid).inputs.get fin := by
    cases fifo <;> simp_all

  theorem advancing_fifo_lt {dfg : DataflowGraph F}
    {nid : Fin dfg.numNodes} {fin : Fin (dfg.nodes.get nid).inputs.length}
    {port : Member ((dfg.nodes.get nid).inputs.get fin) (dfg.nodes.get nid).inputs} {fifo : AdvancingFIFO dfg.nodes}
    (h_is_node_input : dfg.isNodeInput port (.advancing fifo) = true) : nid < fifo.producer := by
    suffices heq : fifo.consumer = nid from heq ▸ fifo.adv
    simp_all

  def nthCycleState (dfg : DataflowGraph F) (inputs : DenoListsStream dfg.inputs) : Nat -> dfg.stateMap :=
    λ n nid =>
      let node := dfg.nodes.get nid
      let nthInput (fin : Fin node.inputs.length) : Denote.denote (node.inputs.get fin) :=
        let port := node.inputs.nthMember fin
        match h_match : findNodeInput port with
        | .some fifo =>
          have h : isNodeInput port fifo = true := List.find?_some h_match
          have h_ty_eq : fifo.t = node.inputs.get fin := node_input_fifo_ty_eq h
          match fifo with
          | .input fifo' =>
            h_ty_eq ▸ (inputs n).get fifo'.producer
          | .advancing fifo' =>
            have := advancing_fifo_lt h
            let producerOutputs := (dfg.nthCycleState inputs n fifo'.producer).fst
            h_ty_eq ▸ producerOutputs.get fifo'.producerPort
          | .initialized fifo' =>
            match n with
            | 0 => h_ty_eq ▸ fifo'.initialValue
            | n' + 1 =>
              let producerOutputs := (dfg.nthCycleState inputs n' fifo'.producer).fst
              h_ty_eq ▸ producerOutputs.get fifo'.producerPort
        | .none => Denote.default (node.inputs.get fin)
      let inputsFinRange := List.finRange node.inputs.length
      let nodeInputs : (DenoList node.inputs) :=
        (List.finRange_map_get node.inputs) ▸ inputsFinRange.toHList node.inputs.get nthInput
      let currState : DenoList node.state :=
        match n with
        | 0 => node.initialState
        | n' + 1 => (dfg.nthCycleState inputs n' nid).snd
      (NodeOps.eval node.ops) nodeInputs currState
    termination_by n nid => (n, dfg.numNodes - nid)

  @[simp]
  def denote (dfg : DataflowGraph F)
    (inputs : DenoStreamsList dfg.inputs) : DenoStreamsList (dfg.outputs) :=
    let packedInputs := inputs.pack
    let stateStream := dfg.nthCycleState packedInputs
    let outputsFinRange := List.finRange dfg.outputs.length
    have finRange_map_eq : outputsFinRange.map dfg.outputs.get = dfg.outputs := List.finRange_map_get dfg.outputs
    let packedOutputStream : DenoListsStream dfg.outputs :=
      λ n =>
        finRange_map_eq ▸ outputsFinRange.toHList dfg.outputs.get (
          λ fin =>
            let outputMem := dfg.outputs.nthMember fin
            let fifoOpt := dfg.findGlobalOutput outputMem
            match fifoOpt with
            | .some ⟨fifo, h⟩ =>
              let outputs : DenoList (dfg.nodes.get fifo.producer).outputs := (stateStream n fifo.producer).fst
              let output : Denote.denote fifo.t := outputs.get fifo.producerPort
              h ▸ output
            | .none =>
              Denote.default (dfg.outputs.get fin)
        )
    packedOutputStream.unpack

end DataflowGraph

end
