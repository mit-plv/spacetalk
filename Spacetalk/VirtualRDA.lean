import Spacetalk.HList
import Spacetalk.Stream
import Mathlib.Data.Vector
import Mathlib.Data.List.Range
import Mathlib.Logic.Basic
import Std.Data.List.Lemmas

namespace VirtualRDA

  -- Syntax

  inductive Ty
    | unit
    | nat

  @[reducible] def Ty.denote : Ty → Type
    | unit => Unit
    | nat => Nat

  abbrev TyStream (ty : Ty) := Stream' (ty.denote)

  abbrev TyStreamsHList (tys : List Ty) := HList TyStream tys

  abbrev TysHList (tys : List Ty) := HList Ty.denote tys

  abbrev TysHListStream (tys : List Ty) := Stream' (TysHList tys)

  def pack_hlist_stream (shl : TyStreamsHList tys) : TysHListStream tys :=
    match tys with
      | [] => λ _ => []
      | h::t =>
        λ n =>
          let h_elem : h.denote := (shl.get .head) n
          let tail_streams : TyStreamsHList t :=
            match shl with
              | _ :: rest => rest
          h_elem :: (pack_hlist_stream tail_streams) n

  def unpack_hlist_stream (s : TysHListStream tys) : TyStreamsHList tys :=
    match tys with
      | [] => []
      | h::t =>
        let h_stream : Stream' h.denote := λ n => (s n).get .head
        let t_stream : TysHListStream t := λ n =>
          match s n with
            | _ :: rest => rest
        h_stream :: unpack_hlist_stream t_stream

  -- More expressive adds that choose inputs with Fins
  -- monotonic to preserver old inputs
  inductive NodeOps : (inputs : List Ty) → List Ty → Type
    | nop : NodeOps α α -- for stateless nodes
    | add : (a : Member .nat inputs) → (b : Member .nat inputs) → NodeOps inputs (.nat :: inputs)
    | mul : (a : Member .nat inputs) → (b : Member .nat inputs) → NodeOps inputs (.nat :: inputs)
    | select : (ty : Ty) → (a : Member ty inputs) → NodeOps inputs [ty]
    | comp : NodeOps α β → NodeOps β γ → NodeOps α γ

  structure InputFIFO (inputs : List Ty) where
    ty : Ty
    producer : Member ty inputs
    consumer : Fin num_nodes

  structure OutputFIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes

  structure AdvancingFIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes
    consumer : Fin num_nodes
    adv : producer < consumer

  structure InitializedFIFO (num_nodes : Nat) where
    ty : Ty
    producer : Fin num_nodes
    consumer : Fin num_nodes
    initial_value : ty.denote

  inductive FIFO (inputs : List Ty) (num_nodes : Nat)
    | input : InputFIFO inputs → FIFO inputs num_nodes
    | output : OutputFIFO num_nodes → FIFO inputs num_nodes
    | advancing : AdvancingFIFO num_nodes → FIFO inputs num_nodes
    | initialized : InitializedFIFO num_nodes → FIFO inputs num_nodes

  namespace FIFO

    @[simp] def get_ty : FIFO inputs nn → Ty
      | .input fifo | .output fifo | .advancing fifo | .initialized fifo => fifo.ty

    @[simp] def is_input : FIFO inputs nn → Bool
      | .input _ => true
      | _ => false

    @[simp] def is_output : FIFO inputs nn → Bool
      | .output _ => true
      | _ => false

    @[simp] def producer : (fifo : FIFO inputs nn) → fifo.is_input = false → Fin nn
      | .initialized fifo', _ | .advancing fifo', _ | .output fifo', _ => fifo'.producer

  end FIFO

  def FIFOList (inputs : List Ty) (num_nodes num_fifos : Nat) :=
    Fin num_fifos → FIFO inputs num_nodes

  namespace FIFOList

    @[simp] def get_ty (coe : Idx → Fin nf) (fifos : FIFOList ins nn nf) (i : Idx) :=
      (fifos (coe i)).get_ty

    @[simp] def is_node_input (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
      match fifos i with
        | .input fifo | .advancing fifo | .initialized fifo => fifo.consumer == nid
        | _ => false

    @[simp] def is_node_output (fifos : FIFOList ins nn nf) (nid : Fin nn) (i : Fin nf) : Bool :=
      match fifos i with
        | .output fifo | .advancing fifo | .initialized fifo => fifo.producer == nid
        | _ => false

    def output_fid (fifos : FIFOList ins nn nf) :=
      {fid : Fin nf // (fifos fid).is_output = true}

    def non_output_fid (fifos : FIFOList ins nn nf) :=
      {fid : Fin nf // (fifos fid).is_output = false}

    theorem filtered_input_is_not_output {fifos : FIFOList ins nn nf} {fid : Fin nf}
      (h_mem : fid ∈ (List.finRange nf).filter (fifos.is_node_input nid))
      : (fifos fid).is_output = false := by
      simp [List.mem_filter] at h_mem
      cases h_match : fifos fid <;> simp; simp [h_match] at h_mem

    @[simp] def node_input_fids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List fifos.non_output_fid :=
      let fin_range := List.finRange nf
      let filtered := fin_range.filter (fifos.is_node_input nid)
      filtered.attach.map (λ ⟨fid, h_mem⟩ => ⟨fid, filtered_input_is_not_output h_mem⟩)

    @[simp] def node_inputs (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
      (fifos.node_input_fids nid).map (fifos.get_ty Subtype.val)

    @[simp] def node_output_fids (fifos : FIFOList ins nn nf) (nid : Fin nn) : List (Fin nf) :=
      let fin_range := List.finRange nf
      fin_range.filter (fifos.is_node_output nid)

    @[simp] def node_outputs (fifos : FIFOList ins nn nf) (nid : Fin nn) : List Ty :=
      (fifos.node_output_fids nid).map (fifos.get_ty id)

  end FIFOList

  structure Node (fifos : FIFOList inputs num_nodes num_fifos) (nid : Fin num_nodes) where
    state : List Ty
    initial_state : TysHList state
    state_transform : NodeOps (state ++ (fifos.node_inputs nid)) state
    pipeline : NodeOps (state ++ (fifos.node_inputs nid)) (fifos.node_outputs nid)

  def NodeList (fifos : FIFOList inputs num_nodes num_fifos) :=
    (nid : Fin num_nodes) → Node fifos nid

  structure VirtualRDA where
    inputs : List Ty
    num_nodes : Nat
    num_fifos : Nat
    fifos : FIFOList inputs num_nodes num_fifos
    nodes : NodeList fifos

  -- Semantics

  @[simp] def NodeOps.denote : NodeOps α β → (TysHList α → TysHList β)
    | .nop => id
    | .add a b => λ inputs => ((inputs.get a) + (inputs.get b)) :: inputs
    | .mul a b => λ inputs => ((inputs.get a) * (inputs.get b)) :: inputs
    | .select _ a => λ inputs => inputs.get a :: []
    | .comp f g => g.denote ∘ f.denote

  namespace Node

    def next_state (node : Node fifos nid)
      (inputs : TysHList (fifos.node_inputs nid))
      (curr_state : TysHList node.state)
       : TysHList node.state :=
      node.state_transform.denote (curr_state ++ inputs)

    @[simp] def denote (node : Node fifos nid)
      (inputs : TysHList (fifos.node_inputs nid))
      (curr_state : TysHList node.state) : TysHList (fifos.node_outputs nid) :=
      node.pipeline.denote (curr_state ++ inputs)

  end Node

  namespace VirtualRDA

    def state_map (vrda : VirtualRDA) :=
      (nid : Fin vrda.num_nodes) → (TysHList (vrda.fifos.node_outputs nid)) × (TysHList (vrda.nodes nid).state)

    theorem filtered_output_is_not_input {vrda : VirtualRDA} {fid : Fin vrda.num_fifos}
      (h_mem : fid ∈ (List.finRange vrda.num_fifos).filter (λ i => (vrda.fifos i).is_output))
      : (vrda.fifos fid).is_output = true := by
      simp [List.mem_filter] at h_mem
      exact h_mem

    def output_fifos (vrda : VirtualRDA) : List vrda.fifos.output_fid :=
      let fin_range := List.finRange vrda.num_fifos
      let filtered := fin_range.filter (λ i => (vrda.fifos i).is_output)
      filtered.attach.map (λ ⟨fid, h_mem⟩ => ⟨fid, filtered_output_is_not_input h_mem⟩)

    theorem output_fid_idx_lt_output_tys_length {vrda : VirtualRDA} {fid : Fin vrda.num_fifos} {fifo : FIFO vrda.inputs vrda.num_nodes}
      (h : vrda.fifos fid = fifo) (h_is_not_input : fifo.is_input = false)
      : (vrda.fifos.node_output_fids (fifo.producer h_is_not_input)).indexOf fid
        < (vrda.fifos.node_outputs (fifo.producer h_is_not_input)).length := by
      simp [List.indexOf]
      apply List.findIdx_lt_length_of_exists
      · simp
        apply List.mem_filter.mpr
        apply And.intro
        · apply List.mem_finRange
        · simp [h]
          cases fifo <;> simp; simp at h_is_not_input

    def extract_fifo_output {vrda : VirtualRDA} {fid : Fin vrda.num_fifos} {fifo : FIFO vrda.inputs vrda.num_nodes}
      (h : vrda.fifos fid = fifo) (h_is_not_input : fifo.is_input = false)
      (outputs : TysHList (vrda.fifos.node_outputs (fifo.producer h_is_not_input))) : fifo.get_ty.denote :=

      let producer_id := fifo.producer h_is_not_input
      let output_fids := vrda.fifos.node_output_fids producer_id
      let output_tys := vrda.fifos.node_outputs producer_id

      let idx : Fin output_tys.length := ⟨output_fids.indexOf fid, output_fid_idx_lt_output_tys_length h h_is_not_input⟩
      let h_eq : Member (output_tys.get idx) output_tys = Member fifo.get_ty output_tys := by simp [h]
      let mem := h_eq ▸ (output_tys.nth_member idx)
      outputs.get mem

    theorem advancing_fifo_lt {vrda : VirtualRDA} {nid : Fin vrda.num_nodes} {fid : vrda.fifos.non_output_fid} {fifo : AdvancingFIFO vrda.num_nodes}
      (h_mem : fid ∈ vrda.fifos.node_input_fids nid) (h_match : vrda.fifos fid.val = FIFO.advancing fifo)
      : fifo.producer < nid := by
      have h_is_input : vrda.fifos.is_node_input nid fid.val = true
      · simp at h_mem
        have h_mem' : fid.val ∈ (List.finRange vrda.num_fifos).filter (vrda.fifos.is_node_input nid)
        · cases h_mem with
          | intro x px =>
            cases px with
              | intro y py =>
                have h_x_eq : fid.val = x
                · symm at py
                  rw [py]
                rw [h_x_eq]
                exact y
        exact (List.mem_filter.mp h_mem').right
      have h_consumer_eq : nid = fifo.consumer
      . simp [h_match] at h_is_input
        symm
        assumption
      rw [h_consumer_eq]
      exact fifo.adv

    def convert_fifo_ty {vrda : VirtualRDA} {coe : Idx → Fin vrda.num_fifos} {fid : Idx}
                      {fifo : FIFO vrda.inputs vrda.num_nodes} (h_match : vrda.fifos (coe fid) = fifo)
                      (val : fifo.get_ty.denote)
                      : (vrda.fifos.get_ty coe fid).denote :=
      let h_eq : fifo.get_ty = (vrda.fifos.get_ty coe) fid := by simp [h_match]
      h_eq ▸ val

    theorem input_map_attach_eq {vrda : VirtualRDA} {nid : Fin vrda.num_nodes}
      : vrda.fifos.node_inputs nid = ((vrda.fifos.node_input_fids nid).attach.map (vrda.fifos.get_ty Subtype.val ∘ Subtype.val)) := by
      rw [List.comp_map (vrda.fifos.get_ty Subtype.val) Subtype.val]
      simp

    def nth_cycle_state (vrda : VirtualRDA) (inputs : TysHListStream vrda.inputs) (n : Nat)
                        : vrda.state_map :=
      λ nid =>
        let input_fids : List vrda.fifos.non_output_fid := vrda.fifos.node_input_fids nid
        let input_vals : TysHList (vrda.fifos.node_inputs nid) :=
          input_map_attach_eq ▸ input_fids.attach.to_hlist (vrda.fifos.get_ty Subtype.val ∘ Subtype.val) (
            λ ⟨fid, h_mem⟩ =>
              match h_match : vrda.fifos fid.val, fid.property with
                | .input fifo, _ =>
                  let val := (inputs n).get fifo.producer
                  convert_fifo_ty h_match val
                | .advancing fifo, _ =>
                  have := advancing_fifo_lt h_mem h_match
                  let producer_outputs := (vrda.nth_cycle_state inputs n fifo.producer).fst
                  let val := extract_fifo_output h_match rfl producer_outputs
                  convert_fifo_ty h_match val
                | .initialized fifo, _ =>
                  let val := match n with
                    | 0 => fifo.initial_value
                    | n' + 1 =>
                      let last_outputs := (vrda.nth_cycle_state inputs n' fifo.producer).fst
                      extract_fifo_output h_match rfl last_outputs
                  convert_fifo_ty h_match val
          )
        let node := vrda.nodes nid
        let outputs := node.denote input_vals node.initial_state
        let next_state := node.next_state input_vals node.initial_state
        (outputs, next_state)
        termination_by nth_cycle_state _ _ n nid => (n, nid)

    @[simp] def denote (vrda : VirtualRDA) (inputs : TyStreamsHList vrda.inputs)
                      : TyStreamsHList (vrda.output_fifos.map (vrda.fifos.get_ty Subtype.val)) :=
      let packed_inputs := pack_hlist_stream inputs
      let state_stream := vrda.nth_cycle_state packed_inputs
      let packed_output_stream : TysHListStream (vrda.output_fifos.map (vrda.fifos.get_ty Subtype.val)) :=
        λ n =>
          vrda.output_fifos.to_hlist (vrda.fifos.get_ty Subtype.val) (
            λ fid =>
              match h_match : vrda.fifos fid.val, fid.property with
                | .output fifo, _ =>
                  let producer_outputs := ((state_stream n) fifo.producer).fst
                  let val := extract_fifo_output h_match rfl producer_outputs
                  convert_fifo_ty h_match val
          )
      unpack_hlist_stream packed_output_stream

  end VirtualRDA

end VirtualRDA
