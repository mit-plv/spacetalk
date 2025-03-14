import Aesop
import Spacetalk.Compiler
import Mathlib.Data.List.Nodup

open Arith DF Compiler

namespace DF

  @[simp]
  def DFG.initialState (dfg : DFG) (env : Env) : State :=
    dfg.foldl
      (λ state node =>
        match node with
        | ⟨nid, .input var _⟩ => state ↦ ⟨env var, ⟨nid, 0⟩⟩
        | _ => state
      )
      .empty

  @[simp]
  def State.union (s1 s2 : State) : State :=
    λ port => s1 port ++ s2 port
  infixl:100 " ⊕ " => State.union

  @[simp]
  theorem State.empty_union_left : State.empty.union s = s := by
    aesop

  @[simp]
  theorem State.empty_union_right {s : State} : s.union .empty = s := by
    aesop

end DF

namespace Compiler.MarkedDFG

  @[simp]
  def initialState (dfg : MarkedDFG) (env : Env) : State :=
    dfg.dfg.initialState env

  @[simp]
  def finalState (dfg : MarkedDFG) (val : Nat) : State :=
    .empty ↦ ⟨val, dfg.ret⟩

end Compiler.MarkedDFG

@[simp]
def mergeVarsRightInitialState (g1 g2 : DFG) (env : Env) : State :=
  g2.foldl (
    λ s node =>
      match node with
      | ⟨nid, .input var _⟩ =>
        match g1[(sameVarInputIdx g1 var)]? with
        | some _ => s
        | none => s ↦ ⟨env var, ⟨nid, 0⟩⟩
      | _ => s
  ) .empty

@[simp]
def mergeVarsOverlappingState (g1 g2 : DFG) (env : Env) : State :=
  g2.foldl (
    λ s node =>
      match node with
      | ⟨_, .input var ports⟩ =>
        match g1[(sameVarInputIdx g1 var)]? with
        | some ⟨_, .input var _⟩ =>
          s ↦↦ ⟨env var, ports⟩
        | _ => s
      | _ => s
  ) .empty

lemma dfg_step_cons {dfg : DFG} (step : dfg.Step s1 s2) : DFG.Step (node :: dfg) s1 s2 := by
  obtain ⟨node, h_mem, step⟩ := step
  apply DFG.Step.node node _ step
  apply List.mem_cons.mpr
  apply Or.intro_right
  exact h_mem

lemma mergeVars_nid_in_original : ∀ node ∈ mergeVars g1 g2, (∃ node' ∈ g1, node.id = node'.id) ∨ ∃ node' ∈ g2, node.id = node'.id := by
  intro node h_mem
  apply List.foldlRecOn g2 mergeVarsAux g1 _ _ _ h_mem
    (motive := λ dfg => ∀ node ∈ dfg,
                          (∃ node', node' ∈ g1 ∧ node.id = node'.id)
                            ∨ (∃ node', node' ∈ g2 ∧ node.id = node'.id))
  · aesop
  · intro dfg ih node h_mem node' h_mem'
    simp only [mergeVarsAux] at h_mem'
    split at h_mem'
    · split at h_mem'
      · apply (List.mem_or_eq_of_mem_set h_mem').elim
        · simp_all
        · intro h
          rw [h]
          rename_i heq
          have ⟨_, h⟩ := List.getElem?_eq_some_iff.mp heq
          apply ih _ (List.mem_iff_get.mpr ⟨_, h⟩)
      · aesop
    · aesop

lemma mergeTwo_nid_in_original : ∀ node ∈ mergeTwo g1 g2 newOutput, (∃ node' ∈ g1.dfg, node.id = node'.id) ∨ ∃ node' ∈ g2.dfg, node.id = node'.id := by
  intro node h_mem
  simp only [mergeTwo, removeOutputNodes, updateReturn, List.map_map, List.mem_filter,
    List.mem_map, Function.comp_apply] at h_mem
  obtain ⟨⟨node', ⟨h_mem', h_eq⟩⟩⟩ := h_mem
  rw [←h_eq]
  apply mergeVars_nid_in_original _ h_mem'

lemma maxNid_lt_new_maxNid : maxNid < (compileAux maxNid e).2 := by
  cases e with
  | var => aesop
  | plus e1 e2 =>
    simp only [compileAux]
    have := maxNid_lt_new_maxNid (e := e1) (maxNid := maxNid)
    have := maxNid_lt_new_maxNid (e := e2) (maxNid := (compileAux maxNid e1).2)
    omega

lemma nid_lt_new_maxNid : ∀ node ∈ (compileAux maxNid e).1.dfg, node.id < (compileAux maxNid e).2 := by
  cases e with
  | var => aesop
  | plus e1 e2 =>
    intro node h_mem
    simp_all only [compileAux]
    repeat (apply (List.mem_cons.mp h_mem).elim (by simp_all); intro h_mem)
    apply (mergeTwo_nid_in_original _ h_mem).elim
    <;> (intro h;
         obtain ⟨node', ⟨h_mem, h_eq⟩⟩ := h;
         rw [h_eq];
         have := maxNid_lt_new_maxNid (e := e2) (maxNid := (compileAux maxNid e1).2);
         have := nid_lt_new_maxNid _ h_mem;
         omega)

lemma maxNid_le_nid : ∀ node ∈ (compileAux maxNid e).1.dfg, maxNid ≤ node.id := by
  cases e with
  | var => aesop
  | plus e1 e2 =>
    intro node h_mem
    simp_all only [compileAux]
    repeat
     (apply (List.mem_cons.mp h_mem).elim
      intro h
      have := @maxNid_lt_new_maxNid maxNid e1
      have := @maxNid_lt_new_maxNid (compileAux maxNid e1).2 e2
      rw [h]
      simp only
      omega
      intro h_mem)
    apply (mergeTwo_nid_in_original _ h_mem).elim
    <;>
     (intro h
      obtain ⟨node', ⟨h_mem, h_eq⟩⟩ := h
      rw [h_eq]
      have := maxNid_le_nid node' h_mem
      have := @maxNid_lt_new_maxNid maxNid e1
      omega)

lemma ret_lt_new_maxNid : (compileAux maxNid e).1.ret.node < (compileAux maxNid e).2 :=  by
  cases e <;> simp_all

lemma maxNid_lt_ret : maxNid < (compileAux maxNid e).1.ret.node :=  by
  cases e with
  | var => simp
  | plus e1 e2 =>
    simp only [compileAux]
    have := @maxNid_lt_new_maxNid maxNid e1
    have := @maxNid_lt_new_maxNid (compileAux maxNid e1).2 e2
    omega

lemma output_if_ret
  : ∀ node ∈ (compileAux maxNid e).1.dfg, node.id = (compileAux maxNid e).1.ret.node → node.isOutput = true := by
  intro node h_mem h_ret
  cases e with
  | var => aesop
  | plus e1 e2 =>
    simp_all only [compileAux]
    have :
      ∀ node ∈ mergeTwo
                (compileAux maxNid e1).1
                (compileAux (compileAux maxNid e1).2 e2).1
                (compileAux (compileAux maxNid e1).2 e2).2,
        node.id ≠ (compileAux (compileAux maxNid e1).2 e2).2 + 1 := by
      intro node h_mem
      apply (mergeTwo_nid_in_original _ h_mem).elim
      <;> (intro h;
           obtain ⟨node', ⟨h_mem, h_eq⟩⟩ := h;
           have := nid_lt_new_maxNid _ h_mem;
           have := maxNid_lt_new_maxNid (e := e2) (maxNid := (compileAux maxNid e1).2);
           omega)
    aesop

lemma initial_state_node_eq {dfg : DFG}
  : ∀ p, dfg.initialState env p ≠ [] → ∃ node ∈ dfg, node.id = p.node ∧ node.isInput = true := by
  intro p h
  apply List.foldlRecOn (motive := λ (s : State) => s p ≠ [] → ∃ node ∈ dfg, node.id = p.node ∧ node.isInput = true) _ _ _ _ _ h
  · simp_all
  · aesop

lemma mergeVars_maintains_op_type
  : ∀ node ∈ mergeVars g1 g2,
      (∃ node' ∈ g1, node'.id = node.id ∧ node'.opTypeEq node) ∨
       ∃ node' ∈ g2, node'.id = node.id ∧ node'.opTypeEq node := by
  intro node h_mem
  simp only [mergeVars] at h_mem
  apply List.foldlRecOn g2 mergeVarsAux g1 _ _ node h_mem
    (motive := λ (dfg : DFG) => ∀ node ∈ dfg,
                                  (∃ node' ∈ g1, node'.id = node.id ∧ node'.opTypeEq node) ∨
                                  ∃ node' ∈ g2, node'.id = node.id ∧ node'.opTypeEq node)
  · intro node h_mem
    apply Or.intro_left
    exists node
    apply And.intro h_mem
    exact And.intro rfl Node.opTypeEq_refl
  · intro dfg ih node h_mem node' h_mem'
    simp only [mergeVarsAux] at h_mem'
    split at h_mem'
    · split at h_mem'
      · apply (List.mem_or_eq_of_mem_set h_mem').elim
        · intro h
          exact ih node' h
        · intro h
          rename_i nid var ports _ nid' var' ports' heq
          have := List.mem_of_getElem? heq
          apply (ih _ this).elim
          all_goals (intro h; obtain ⟨node, ⟨h_mem, ⟨h_id, h_op⟩⟩⟩ := h)
          on_goal 1 => apply Or.intro_left
          on_goal 2 => apply Or.intro_right
          all_goals
           (exists node
            apply And.intro h_mem
            apply And.intro
            · rw [h_id]
              rw [h]
            · obtain ⟨nid, op⟩ := node
              obtain ⟨nid', op'⟩ := node'
              cases op <;> cases op' <;> simp_all)
      · simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at h_mem'
        apply h_mem'.elim
        · intro h; exact ih node' h
        · intro h
          apply Or.intro_right
          exists node'
          apply And.intro (h ▸ h_mem)
          exact And.intro rfl Node.opTypeEq_refl
    · simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at h_mem'
      apply h_mem'.elim
      · intro h; exact ih node' h
      · intro h
        apply Or.intro_right
        exists node
        apply And.intro h_mem
        exact And.intro (by rw [h]) (h ▸ Node.opTypeEq_refl)

lemma varNames_nodup_false {dfg : DFG} : ⟨nid1, .input var ports1⟩ ∈ dfg → ⟨nid2, .input var ports2⟩ ∈ dfg → False := sorry

lemma mergeVars_no_overlapping_cons (h : (g1 ++ g2).varNames.Nodup) : mergeVars g1 g2 = g1 ++ g2 := by
  cases g2 with
  | nil => simp
  | cons hd tl =>
    simp only [mergeVars, List.foldl_cons, mergeVarsAux, sameVarInputIdx]
    split; split
    next heq =>
      rename_i _ id1 var1 ports1 _ id2 var2 ports2
      have ⟨h, heq⟩ := List.getElem?_eq_some_iff.mp heq
      have ⟨h, _⟩ :=
        (List.findIdx_eq h
          (p := fun node =>
            match node with
            | { id := id2, op := NodeOp.input var2 ports2 } => decide (var2 = var1)
            | x => false)
        ).mp rfl
      simp only [heq, decide_eq_true_eq] at h
      exfalso
      -- apply varNames_nodup_false (dfg := g1 ++ ⟨id1, .input var1 ports2⟩ :: tl)
      -- · have := List.mem_of_getElem heq
      sorry
    all_goals
      refine Eq.subst ?_ (mergeVars_no_overlapping_cons ?_) <;> aesop

@[simp]
lemma mergeVars_empty_left (h : g.varNames.Nodup) : mergeVars [] g = g := by
  induction g with
  | nil => simp
  | cons hd tl ih =>
    simp
    split
    <;>
     (conv =>
        rhs
        rw [←List.singleton_append]
      rw [←List.singleton_append] at h
      exact mergeVars_no_overlapping_cons h)

lemma mergeVars_initial_state_breakdown (h : g1.Disjoint g2)
  : (mergeVars g1 g2).initialState env = g1.initialState env ⊕ mergeVarsRightInitialState g1 g2 env := by
  induction g1 with
  | nil =>
    simp
    sorry
  | cons hd tl ih => sorry

lemma mergeVars_trace (maxNid : Nat) (e1 e2 : Exp) (env : Env) (x y : Nat)
  : (compileAux maxNid e1).1.dfg.MultiStep ((compileAux maxNid e1).1.initialState env) ((compileAux maxNid e1).1.finalState x)
    → (compileAux (compileAux maxNid e1).2 e2).1.dfg.MultiStep ((compileAux (compileAux maxNid e1).2 e2).1.initialState env) ((compileAux (compileAux maxNid e1).2 e2).1.finalState y)
    → (mergeVars (compileAux maxNid e1).1.dfg (compileAux (compileAux maxNid e1).2 e2).1.dfg).MultiStep
        ((mergeVars (compileAux maxNid e1).1.dfg (compileAux (compileAux maxNid e1).2 e2).1.dfg).initialState env)
        (((compileAux maxNid e1).1.finalState x) ⊕ ((compileAux (compileAux maxNid e1).2 e2).1.finalState y)) := by
  intro t1 t2
  trans ((compileAux maxNid e1).1.finalState x) ⊕ (mergeVarsOverlappingState (compileAux maxNid e1).1.dfg (compileAux (compileAux maxNid e1).2 e2).1.dfg env)
  · sorry
  · sorry

lemma dfg_cons_non_input_initial_state (dfg : DFG) (node : Node)
  (h : node.isInput = false) : (DFG.initialState (node :: dfg) env) = dfg.initialState env := by
  aesop

lemma removeOutputNodes_initial_state
  : (removeOutputNodes dfg).initialState env = dfg.initialState env :=
  let rec go {init : State} {dfg : DFG} :
    (removeOutputNodes dfg).foldl
      (λ state node =>
        match node with
        | ⟨nid, .input var _⟩ => state ↦ ⟨env var, ⟨nid, 0⟩⟩
        | _ => state
      )
      init =
    dfg.foldl
      (λ state node =>
        match node with
        | ⟨nid, .input var _⟩ => state ↦ ⟨env var, ⟨nid, 0⟩⟩
        | _ => state
      )
      init := by
    cases dfg with
    | nil => rfl
    | cons hd tl =>
      have := List.filter_cons (x := hd) (xs := tl) (p := Node.notOutput)
      by_cases h : hd.notOutput
      · simp only [h, if_true] at this
        simp only [removeOutputNodes, this, List.foldl_cons]
        apply go
      · have := @go init tl
        aesop
  go

lemma updateReturn_initial_state
  : (updateReturn dfg ret newRet).initialState env = dfg.initialState env :=
  let rec go {init : State} {dfg : DFG} :
    (updateReturn dfg ret newRet).foldl
      (λ state node =>
        match node with
        | ⟨nid, .input var _⟩ => state ↦ ⟨env var, ⟨nid, 0⟩⟩
        | _ => state
      )
      init =
    dfg.foldl
      (λ state node =>
        match node with
        | ⟨nid, .input var _⟩ => state ↦ ⟨env var, ⟨nid, 0⟩⟩
        | _ => state
      )
      init := by
    cases dfg with
    | nil => rfl
    | cons hd tl =>
      simp only [updateReturn, List.map_cons, List.foldl_cons]
      have : (match
               ({ id := hd.id,
                  op :=
                     match hd.op with
                     | NodeOp.input var ports => NodeOp.input var (List.map (fun p => if p = ret then newRet else p) ports)
                     | NodeOp.output => NodeOp.output
                     | NodeOp.binOp op ports => NodeOp.binOp op (List.map (fun p => if p = ret then newRet else p) ports) } : Node) with
              | { id := nid, op := NodeOp.input var a } => init ↦ { val := env var, port := { node := nid, port := 0 } }
              | x => init) =
              (match hd with
              | { id := nid, op := NodeOp.input var a } => init ↦ { val := env var, port := { node := nid, port := 0 } }
              | x => init) := by
        obtain ⟨nid, op⟩ := hd
        cases op <;> simp
      rw [←this]
      apply go
  go

lemma plus_initial_state_eq_mergeVars : ((compileAux maxNid (e1.plus e2)).fst.initialState env) =
  (mergeVars (compileAux maxNid e1).fst.dfg (compileAux (compileAux maxNid e1).snd e2).fst.dfg).initialState env := by
  simp only [compileAux]
  have h1 := dfg_cons_non_input_initial_state (env := env)
              (⟨(compileAux (compileAux maxNid e1).2 e2).2 + 1, .output⟩ ::
                mergeTwo (compileAux maxNid e1).1 (compileAux (compileAux maxNid e1).2 e2).1 (compileAux (compileAux maxNid e1).2 e2).2)
              ⟨(compileAux (compileAux maxNid e1).2 e2).2, .binOp .plus [⟨(compileAux (compileAux maxNid e1).2 e2).2 + 1, 0⟩]⟩
              (by simp)
  have h2 := dfg_cons_non_input_initial_state (env := env)
              (mergeTwo (compileAux maxNid e1).1 (compileAux (compileAux maxNid e1).2 e2).1 (compileAux (compileAux maxNid e1).2 e2).2)
              ⟨(compileAux (compileAux maxNid e1).2 e2).2 + 1, .output⟩
              (by simp)
  simp_rw [MarkedDFG.initialState, h1, h2]
  simp only [mergeTwo]
  rw [removeOutputNodes_initial_state]
  rw [updateReturn_initial_state]
  rw [updateReturn_initial_state]

@[simp]
def mergedState (dfg1 dfg2 : MarkedDFG) (nid : Nat) (s : State) : State :=
  λ p =>
    if p = ⟨nid, 0⟩ then
      s dfg1.ret
    else if p = ⟨nid, 1⟩ then
      s dfg2.ret
    else if p = dfg1.ret ∨ p = dfg2.ret then
      []
    else
      s p

lemma merged_state_unchanged {s : State}
  (h_nid1 : s ⟨nid, 0⟩ = []) (h_nid2 : s ⟨nid, 1⟩ = [])
  (h_ret1 : s e1.ret = []) (h_ret2 : s e2.ret = [])
  : (mergedState e1 e2 nid s) = s := by
  aesop

@[simp]
abbrev MergedState (e1 e2 : Exp) (maxId : Nat) (s : State) : State :=
  mergedState (compileAux maxId e1).1 (compileAux (compileAux maxId e1).2 e2).1 (compileAux (compileAux maxId e1).2 e2).2 s

lemma mergeVars_non_output_nodes_not_ret
  (h_mem : node ∈ mergeVars (compileAux maxNid e1).1.dfg (compileAux (compileAux maxNid e1).2 e2).1.dfg)
  (h_output : node.notOutput = true)
  : ⟨node.id, port1⟩ ≠ (compileAux maxNid e1).1.ret ∧ ⟨node.id, port2⟩ ≠ (compileAux (compileAux maxNid e1).2 e2).1.ret := by
  apply List.foldlRecOn _ _ _ _ _ _ h_mem h_output
    (motive := λ dfg => ∀ node ∈ dfg, node.notOutput = true → ⟨node.id, port1⟩ ≠ (compileAux maxNid e1).1.ret ∧ ⟨node.id, port2⟩ ≠ (compileAux (compileAux maxNid e1).2 e2).1.ret)
  · intro node h_mem h_not_output
    apply And.intro
    · apply Port.node_ne
      by_contra h
      have := output_if_ret _ h_mem h
      aesop
    · apply Port.node_ne
      have := nid_lt_new_maxNid _ h_mem
      have := @maxNid_lt_ret (compileAux maxNid e1).2 e2
      simp only
      omega
  · intro dfg ih node h_mem node' h_mem' h_not_output
    simp only [mergeVarsAux] at h_mem'
    split at h_mem'
    · split at h_mem'
      · apply (List.mem_or_eq_of_mem_set h_mem').elim
        · intro h; exact ih _ h h_not_output
        · intro h
          rename_i heq
          have := List.mem_iff_get.mpr ⟨_, (List.getElem?_eq_some_iff.mp heq).snd⟩
          have := ih _ this (by simp)
          rw [h]
          exact this
      · simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at h_mem'
        apply h_mem'.elim
        · intro h; exact ih _ h h_not_output
        · intro h
          rw [h]
          rw [h] at h_not_output
          apply And.intro
          · apply Port.node_ne
            have := maxNid_le_nid _ h_mem
            have := @ret_lt_new_maxNid maxNid e1
            simp_all only
            omega
          · apply Port.node_ne
            by_contra h
            have := output_if_ret _ h_mem
            aesop
    · simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at h_mem'
      apply h_mem'.elim
      · intro h; exact ih _ h h_not_output
      · intro h
        rw [h]
        rw [h] at h_not_output
        apply And.intro
        · apply Port.node_ne
          have := maxNid_le_nid _ h_mem
          have := @ret_lt_new_maxNid maxNid e1
          simp only
          omega
        · apply Port.node_ne
          by_contra h
          have := output_if_ret _ h_mem
          aesop

lemma mergeVars_to_compile_plus
  : (mergeVars (compileAux maxNid e1).1.dfg (compileAux (compileAux maxNid e1).2 e2).1.dfg).MultiStep s1 s2
    → (compileAux maxNid (e1.plus e2)).1.dfg.MultiStep (MergedState e1 e2 maxNid s1) (MergedState e1 e2 maxNid s2) := by
  intro h
  induction h with
  | refl => rfl
  | tail hd tl ih =>
    apply Relation.ReflTransGen.tail ih
    simp only [compileAux]
    repeat apply dfg_step_cons
    obtain ⟨node, h_mem, step⟩ := tl
    match node, step with
    | ⟨nid, .input var ports⟩, .input h =>
      let newNode : Node :=
        updateReturnAux (compileAux (compileAux maxNid e1).2 e2).1.ret ⟨(compileAux (compileAux maxNid e1).2 e2).2, 1⟩
        (updateReturnAux (compileAux maxNid e1).1.ret ⟨(compileAux (compileAux maxNid e1).2 e2).2, 0⟩ ⟨nid, .input var ports⟩)
      simp only [mergeTwo]
      apply DFG.Step.node newNode
      · apply List.mem_filter.mpr
        apply And.intro
        · apply List.mem_map.mpr
          exists updateReturnAux (compileAux maxNid e1).1.ret ⟨(compileAux (compileAux maxNid e1).2 e2).2, 0⟩ ⟨nid, .input var ports⟩
          apply And.intro _ rfl
          apply List.mem_map.mpr
          exists ⟨nid, .input var ports⟩
        · simp [newNode]
      · refine Eq.subst ?_ (Node.Step.input ?_)
        ·
          sorry
        · have := mergeVars_non_output_nodes_not_ret (port1 := 0) (port2 := 0) h_mem (by simp)
          have : nid ≠ (compileAux (compileAux maxNid e1).2 e2).2 := by
            apply (mergeVars_nid_in_original _ h_mem).elim
            <;>
             (intro h
              obtain ⟨node, ⟨h_mem, h_nid⟩⟩ := h
              simp only at h_nid
              rw [h_nid]
              have := nid_lt_new_maxNid _ h_mem
              have := @maxNid_lt_new_maxNid (compileAux maxNid e1).2 e2
              omega)
          simp_all
    | ⟨nid, .binOp op ports⟩, .binOp h1 h2 =>
      sorry

theorem compile_value_correct (eval : Eval env e v)
  : (compileAux maxNid e).1.dfg.MultiStep ((compileAux maxNid e).1.initialState env) ((compileAux maxNid e).1.finalState v) := by
  cases e with
  | var name =>
    apply Relation.ReflTransGen.single
    apply DFG.Step.node ⟨maxNid, .input name [⟨maxNid + 1, 0⟩]⟩
    · simp
    · refine Eq.subst ?_ (Node.Step.input ?_)
      cases eval
      aesop
  | plus e1 e2 =>
    cases eval
    rename_i x y eval1 eval2
    apply Relation.ReflTransGen.tail
      (b := .empty ↦ ⟨x, ⟨(compileAux (compileAux maxNid e1).2 e2).2, 0⟩⟩
                   ↦ ⟨y, ⟨(compileAux (compileAux maxNid e1).2 e2).2, 1⟩⟩)
    · have merge_trace := mergeVars_trace maxNid e1 e2 env x y (compile_value_correct eval1) (compile_value_correct eval2)
      rw [←plus_initial_state_eq_mergeVars] at merge_trace
      have : (MergedState e1 e2 maxNid ((compileAux maxNid (e1.plus e2)).fst.initialState env)) = ((compileAux maxNid (e1.plus e2)).fst.initialState env) := by
        rw [plus_initial_state_eq_mergeVars]
        apply merged_state_unchanged
        repeat
         (by_contra h
          obtain ⟨node, ⟨h_mem, ⟨h_id⟩⟩⟩ := initial_state_node_eq _ h
          apply (mergeVars_nid_in_original _ h_mem).elim
          <;>
           (intro h
            obtain ⟨node', ⟨h_mem', h_id'⟩⟩ := h
            rw [h_id] at h_id'
            have := nid_lt_new_maxNid _ h_mem'
            have := @maxNid_lt_new_maxNid (compileAux maxNid e1).2 e2
            simp only at h_id'
            omega))
        repeat
         (by_contra h
          obtain ⟨node, ⟨h_mem, ⟨h_id, h_input⟩⟩⟩ := initial_state_node_eq _ h
          have h_output : node.isOutput = true := by
            apply (mergeVars_maintains_op_type node h_mem).elim
            all_goals (intro h; obtain ⟨node', ⟨h_mem', ⟨h_id', h_op⟩⟩⟩ := h)
            all_goals first
            | (have := output_if_ret node' h_mem' (h_id' ▸ h_id)
               obtain ⟨nid, op⟩ := node
               obtain ⟨nid', op'⟩ := node'
               cases op <;> cases op' <;> simp_all)
            | (have := maxNid_le_nid node' h_mem'
               have := @ret_lt_new_maxNid maxNid e1
               have := nid_lt_new_maxNid node' h_mem'
               have := @maxNid_lt_ret (compileAux maxNid e1).2 e2
               omega)
          obtain ⟨nid, op⟩ := node
          cases op <;> contradiction)
      have := this ▸ mergeVars_to_compile_plus merge_trace
      refine Eq.subst ?_ this
      have : (compileAux maxNid e1).1.ret ≠ (compileAux (compileAux maxNid e1).2 e2).1.ret := by
        apply Port.node_ne
        have := @ret_lt_new_maxNid maxNid e1
        have := @maxNid_lt_ret (compileAux maxNid e1).2 e2
        omega
      -- aesop?
      simp_all only [mergeVars, MarkedDFG.initialState, DFG.initialState, compileAux, mergeTwo, removeOutputNodes,
        updateReturn, List.map_map, List.foldl_cons, MarkedDFG.finalState, MergedState, ne_eq]
      ext x_1 i a : 3
      simp_all only [mergedState, State.union, State.push, ↓reduceIte, State.empty, List.concat_eq_append,
        List.nil_append, List.singleton_append, Option.mem_def, Port.mk.injEq, Nat.add_one_ne_zero, and_false]
      apply Iff.intro
      · intro a_1
        split
        next h =>
          subst h
          simp_all only [Port.mk.injEq, Nat.add_one_ne_zero, and_false, ↓reduceIte]
          split at a_1
          next h => simp_all only [not_true_eq_false]
          next h => simp_all only [List.nil_append]
        next h =>
          simp_all only [↓reduceIte]
          split
          next h_1 =>
            subst h_1
            simp_all only [↓reduceIte, Port.mk.injEq, reduceCtorEq, and_false, not_false_eq_true]
          next h_1 =>
            simp_all only [↓reduceIte, List.getElem?_nil, reduceCtorEq]
            split at a_1
            next h_2 => simp_all only [List.getElem?_nil, reduceCtorEq]
            next h_2 =>
              split at a_1
              next h_3 =>
                split at a_1
                next h_4 =>
                  subst h_3
                  simp_all only [not_true_eq_false]
                next h_4 =>
                  subst h_3
                  simp_all only [not_false_eq_true, List.singleton_append, or_false, not_true_eq_false]
              next h_3 =>
                split at a_1
                next h_4 =>
                  subst h_4
                  simp_all only [List.nil_append, or_true, not_true_eq_false]
                next h_4 =>
                  simp_all only [or_self, not_false_eq_true, List.append_nil, List.getElem?_nil, reduceCtorEq]
      · intro a_1
        split
        next h =>
          subst h
          simp_all only [Port.mk.injEq, reduceCtorEq, and_false, ↓reduceIte]
        next h =>
          simp_all only [↓reduceIte]
          split
          next h_1 =>
            subst h_1
            simp_all only [↓reduceIte, Port.mk.injEq, Nat.add_one_ne_zero, and_false, not_false_eq_true]
            split
            next h => simp_all only [not_true_eq_false]
            next h => simp_all only [List.nil_append]
          next h_1 => simp_all only [↓reduceIte, List.getElem?_nil, reduceCtorEq]
    · apply DFG.Step.node ⟨(compileAux (compileAux maxNid e1).2 e2).2,
                            .binOp .plus [⟨(compileAux (compileAux maxNid e1).2 e2).2 + 1, 0⟩]⟩
      · simp
      · refine Eq.subst ?_ (Node.Step.binOp ?_ ?_)
        aesop

theorem compile_confluence
  : (compile e).dfg.MultiStep a b → (compile e).dfg.MultiStep a c
      → ∃ d, (compile e).dfg.MultiStep b d ∧ (compile e).dfg.MultiStep c d
  | .refl, .refl => ⟨a, .intro .refl .refl⟩
  | .refl, s => ⟨c, .intro s .refl⟩
  | s, .refl => ⟨b, .intro .refl s⟩
  | .tail gs1 ns1, .tail gs2 ns2 => by
    cases ns1
    cases ns2
    rename_i _ _ b c node1 h_mem1 ns1 node2 h_mem2 ns2
    rename_i c' b'
    cases ns1 <;> cases ns2
    all_goals sorry

theorem final_state_halts
  : ∀ s, (compile e).dfg.MultiStep ((compile e).finalState v) s → s = (compile e).finalState v := by
  intro s step
  induction step with
  | refl => rfl
  | tail _ step ih =>
    rw [ih] at step
    obtain ⟨⟨nid, op⟩, h_mem, step⟩ := step
    cases step
    <;> (have h_ret : ⟨nid, 0⟩ = (compile e).ret := by simp_all;
         have := output_if_ret _ h_mem (Port.mk.inj h_ret).left;
         simp at this)

theorem compile_correct
  : Eval env e v
    → ∀ s, (compile e).dfg.MultiStep ((compile e).initialState env) s
          → (compile e).dfg.MultiStep s ((compile e).finalState v) := by
  intro eval _ step
  obtain ⟨final, ⟨trace, refl_step⟩⟩ := compile_confluence step (compile_value_correct eval)
  rw [final_state_halts final refl_step] at trace
  exact trace

theorem compile_no_infinite_trace
  : ¬∃ f : Nat → State,
    f 0 = ((compile e).initialState env)
      ∧ ∀ n, (compile e).dfg.Step (f n) (f (n + 1)) := by
  intro h
  obtain ⟨f, ⟨h_zero, h_succ⟩⟩ := h
  cases e with
  | var name =>
    have h_f1 : f 1 = .empty ↦ ⟨env name, ⟨1, 0⟩⟩ := by
      have := h_succ 0
      rw [h_zero] at this
      obtain ⟨node, h_mem, step⟩ := this
      simp only [compile, compileAux, Nat.zero_add,
        List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h_mem
      generalize f 1 = s2 at *
      apply h_mem.elim
      <;> (intro h;
           rw [h] at step;
           cases step;
           try aesop)
    have := h_succ 1
    rw [h_f1] at this
    obtain ⟨node, h_mem, step⟩ := this
    simp only [compile, compileAux, Nat.zero_add,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h_mem
    generalize f 2 = s2 at *
    apply h_mem.elim
    <;> (intro h;
         rw [h] at step;
         cases step;
         try contradiction)
  | plus =>
    simp only [compile, compileAux] at h_succ
    sorry
