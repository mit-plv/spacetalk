import Aesop
import Spacetalk.Compiler

open Arith DF Compiler

namespace DF

  @[simp]
  def Node.isOutput : Node → Bool
    | ⟨_, .output⟩ => true
    | _ => false

end DF

namespace Compiler.MarkedDFG

  @[simp]
  def initialState (dfg : MarkedDFG) (env : Env) : State :=
    dfg.dfg.foldl
      (λ state node =>
        match node with
        | ⟨nid, .input var _⟩ => state ↦ ⟨env var, ⟨nid, 0⟩⟩
        | _ => state
      )
      .empty

  @[simp]
  def finalState (dfg : MarkedDFG) (val : Nat) : State :=
    .empty ↦ ⟨val, dfg.ret⟩

end Compiler.MarkedDFG

lemma mergeTwo_nid_in_original : ∀ node ∈ mergeTwo g1 g2 newOutput, (∃ node' ∈ g1.dfg, node.id = node'.id) ∨ ∃ node' ∈ g2.dfg, node.id = node'.id := by
  intro node h_mem
  simp only [mergeTwo, removeOutputNodes, updateReturn, mergeVars, List.map_map, List.mem_filter,
    List.mem_map, Function.comp_apply] at h_mem
  obtain ⟨⟨node', ⟨h_mem', h_eq⟩⟩⟩ := h_mem
  rw [←h_eq]
  apply List.foldlRecOn g2.dfg mergeVarsAux g1.dfg _ _ _ h_mem'
    (motive := λ dfg => ∀ node ∈ dfg,
                          (∃ node', node' ∈ g1.dfg ∧ node.id = node'.id)
                            ∨ (∃ node', node' ∈ g2.dfg ∧ node.id = node'.id))
  · -- aesop?
    rename_i right
    intro node_1 a
    subst h_eq
    simp_all only
    split at right
    next x heq =>
      split at heq
      next x_1 var ports heq_1 =>
        split at heq_1
        next x_2 var_1 ports_1 heq_2 => simp_all only [Bool.false_eq_true]
        next x_2 heq_2 => simp_all only [Bool.false_eq_true]
        next x_2 op ports_1 heq_2 => simp_all only [Bool.false_eq_true]
      next x_1 heq_1 =>
        split at heq_1
        next x_2 var ports heq_2 => simp_all only [Bool.false_eq_true]
        next x_2 heq_2 => simp_all only [Bool.false_eq_true]
        next x_2 op ports heq_2 => simp_all only [Bool.false_eq_true]
      next x_1 op ports heq_1 =>
        split at heq_1
        next x_2 var ports_1 heq_2 => simp_all only [Bool.false_eq_true]
        next x_2 heq_2 => simp_all only [Bool.false_eq_true]
        next x_2 op_1 ports_1 heq_2 => simp_all only [Bool.false_eq_true]
    next x x_1 =>
      split at x_1
      rename_i x_2 var ports heq
      split at heq
      rename_i x_3 var_1 ports_1 heq_1
      simp_all only [reduceCtorEq, implies_true, NodeOp.input.injEq]
      obtain ⟨left, right⟩ := heq
      subst right left
      apply Or.inl
      apply Exists.intro
      apply And.intro
      on_goal 6 => rename_i x_2 heq
      on_goal 7 => rename_i x_2 op ports heq
      on_goal 4 => rename_i x_3 heq_1
      on_goal 5 => rename_i x_3 op ports_1 heq_1
      on_goal 6 => split at heq
      on_goal 6 => rename_i x_3 var ports heq_1
      on_goal 7 => rename_i x_3 heq_1
      on_goal 8 => rename_i x_3 op ports heq_1
      on_goal 9 => split at heq
      on_goal 9 => rename_i x_3 var ports_1 heq_1
      on_goal 10 => rename_i x_3 heq_1
      on_goal 11 => rename_i x_3 op_1 ports_1 heq_1
      on_goal 2 => {rfl
      }
      · simp_all only
      simp_all only [NodeOp.input.injEq, true_and, imp_false, reduceCtorEq]
      simp_all only [reduceCtorEq, implies_true]
      simp_all only [imp_false, not_true_eq_false]
      simp_all only [imp_false, not_true_eq_false]
      simp_all only [imp_false, not_true_eq_false]
      simp_all only [reduceCtorEq, implies_true]
      simp_all only [NodeOp.binOp.injEq, true_and, imp_false, reduceCtorEq]
      simp_all only [reduceCtorEq, implies_true, NodeOp.binOp.injEq, true_and]
      subst heq
      apply Or.inl
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
  · intro dfg ih node h_mem node' h_mem'
    simp only [mergeVarsAux] at h_mem'
    split at h_mem'
    · split at h_mem'
      · apply (List.mem_or_eq_of_mem_set h_mem').elim
        · simp_all
        · intro h
          rw [h]
          rename_i heq
          have ⟨node, h⟩ := List.get?_eq_some_iff.mp heq
          apply ih _ (List.mem_iff_get.mpr ⟨_, h⟩)
      · -- aesop?
        rename_i right node'_1 h_mem'_1 node_1 id var' a x x_1
        subst h_eq
        simp_all only [List.get?_eq_getElem?, imp_false, List.mem_cons]
        cases h_mem' with
        | inl h =>
          subst h
          simp_all only
          split at right
          next x_2 heq =>
            split at heq
            next x_3 var ports heq_1 =>
              split at heq_1
              next x_4 var_1 ports_1 heq_2 => simp_all only [Bool.false_eq_true]
              next x_4 heq_2 => simp_all only [Bool.false_eq_true]
              next x_4 op ports_1 heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 heq_1 =>
              split at heq_1
              next x_4 var ports heq_2 => simp_all only [Bool.false_eq_true]
              next x_4 heq_2 => simp_all only [Bool.false_eq_true]
              next x_4 op ports heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 op ports heq_1 =>
              split at heq_1
              next x_4 var ports_1 heq_2 => simp_all only [Bool.false_eq_true]
              next x_4 heq_2 => simp_all only [Bool.false_eq_true]
              next x_4 op_1 ports_1 heq_2 => simp_all only [Bool.false_eq_true]
          next x_2 x_3 =>
            split at x_3
            next x_4 var ports heq =>
              split at heq
              next x_5 var_1 ports_1
                heq_1 =>
                simp_all only [reduceCtorEq, implies_true, NodeOp.input.injEq]
                obtain ⟨left, right⟩ := heq
                subst left right
                apply Or.inr
                apply Exists.intro
                · apply And.intro
                  · exact h_mem
                  · simp_all only
              next x_5 heq_1 => simp_all only [NodeOp.input.injEq, true_and, imp_false, reduceCtorEq]
              next x_5 op ports_1 heq_1 => simp_all only [reduceCtorEq, implies_true]
            next x_4 heq =>
              split at heq
              next x_5 var ports heq_1 => simp_all only [implies_true, imp_false, not_true_eq_false]
              next x_5 heq_1 => simp_all only [implies_true, imp_false, not_true_eq_false]
              next x_5 op ports heq_1 => simp_all only [implies_true, imp_false, not_true_eq_false]
            next x_4 op ports heq =>
              split at heq
              next x_5 var ports_1 heq_1 => simp_all only [reduceCtorEq, implies_true]
              next x_5 heq_1 => simp_all only [NodeOp.binOp.injEq, true_and, imp_false, reduceCtorEq]
              next x_5 op_1 ports_1
                heq_1 =>
                simp_all only [reduceCtorEq, implies_true, NodeOp.binOp.injEq, true_and]
                subst heq
                apply Or.inr
                apply Exists.intro
                · apply And.intro
                  · exact h_mem
                  · simp_all only
        | inr h_1 => simp_all only
    · -- aesop?
      rename_i right node'_1 h_mem'_1 node_2 x
      subst h_eq
      simp_all only [imp_false, List.mem_cons]
      cases h_mem' with
      | inl h =>
        subst h
        split at right
        next x_1 heq =>
          split at heq
          next x_2 var ports heq_1 =>
            split at heq_1
            next x_3 var_1 ports_1 heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 op ports_1 heq_2 => simp_all only [Bool.false_eq_true]
          next x_2 heq_1 =>
            split at heq_1
            next x_3 var ports heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 op ports heq_2 => simp_all only [Bool.false_eq_true]
          next x_2 op ports heq_1 =>
            split at heq_1
            next x_3 var ports_1 heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 heq_2 => simp_all only [Bool.false_eq_true]
            next x_3 op_1 ports_1 heq_2 => simp_all only [Bool.false_eq_true]
        next x_1 x_2 =>
          split at x_2
          rename_i x_3 var ports heq
          split at heq
          rename_i x_4 var_1 ports_1 heq_1
          simp_all only [reduceCtorEq, implies_true, NodeOp.input.injEq]
          obtain ⟨left, right⟩ := heq
          subst left right
          apply Or.inr
          apply Exists.intro
          apply And.intro
          on_goal 6 => rename_i x_3 heq
          on_goal 7 => rename_i x_3 op ports heq
          on_goal 4 => rename_i x_4 heq_1
          on_goal 5 => rename_i x_4 op ports_1 heq_1
          on_goal 6 => split at heq
          on_goal 6 => rename_i x_4 var ports heq_1
          on_goal 7 => rename_i x_4 heq_1
          on_goal 8 => rename_i x_4 op ports heq_1
          on_goal 9 => split at heq
          on_goal 9 => rename_i x_4 var ports_1 heq_1
          on_goal 10 => rename_i x_4 heq_1
          on_goal 11 => rename_i x_4 op_1 ports_1 heq_1
          on_goal 2 => {rfl
          }
          · simp_all only
          simp_all only [NodeOp.input.injEq, true_and, imp_false, reduceCtorEq]
          simp_all only [reduceCtorEq, implies_true]
          simp_all only [imp_false, not_true_eq_false]
          simp_all only [imp_false, not_true_eq_false]
          simp_all only [imp_false, not_true_eq_false]
          simp_all only [reduceCtorEq, implies_true]
          simp_all only [NodeOp.binOp.injEq, true_and, imp_false, reduceCtorEq]
          simp_all only [reduceCtorEq, implies_true, NodeOp.binOp.injEq, true_and]
          subst heq
          apply Or.inr
          apply Exists.intro
          · apply And.intro
            on_goal 2 => {rfl
            }
            · simp_all only
      | inr h_1 => simp_all only

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
    sorry

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
    have := h_succ 1
    have : f 1 = .empty ↦ ⟨env name, ⟨1, 0⟩⟩ := by
      have := h_succ 0
      sorry
    sorry
  | plus => sorry
