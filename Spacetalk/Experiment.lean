import Aesop
import Mathlib.Data.Vector.Basic
import Std.Data.DHashMap.Internal.WF

open Mathlib

abbrev Ty := Nat

namespace Arith
  inductive Exp
    | var : String → Exp
    | plus : Exp → Exp → Exp

  abbrev Env := String → Ty

  inductive Eval : Env → Exp → Ty → Prop
    | var : env s = v → Eval env (.var s) v
    | plus : Eval env e1 x
      → Eval env e2 y
      → Eval env (.plus e1 e2) (x + y)
end Arith

namespace Df
  abbrev Nid := Nat
  abbrev Pid := Nat

  structure Port where
    node : Nid
    port : Pid
  deriving DecidableEq

  structure Token where
    val : Ty
    tag : Port

  structure BToken where
    val : Ty
    tags : List Port

  @[simp]
  def Nid.fst (n : Nid) : Port := ⟨n, 0⟩

  @[simp]
  def Nid.snd (n : Nid) : Port := ⟨n, 1⟩

  inductive BinOp
    | plus

  inductive NodeOp
    | input : List Port → NodeOp
    | output : NodeOp
    | binOp : BinOp → List Port → NodeOp

  @[simp]
  def NodeOp.isOutput : NodeOp → Bool
    | .output => true
    | _ => false

  structure Node where
    id : Nid
    op : NodeOp

  abbrev DFG := List Node

  abbrev State := Port → List Ty

  @[simp]
  def State.empty : State := λ _ => []

  @[simp]
  def State.pop (s : State) (t : Port) : State :=
    λ t' => if t' = t then (s t).tail else s t'

  @[simp]
  def State.push (s : State) (tok : Token) : State :=
    λ t' => if t' = tok.tag then (s tok.tag).concat tok.val else (s t')

  @[simp]
  def State.pushAll (s : State) (tok : BToken) : State :=
    tok.tags.foldl (λ s tag => s.push ⟨tok.val, tag⟩) s

  @[simp]
  def BinOp.denote : BinOp → Ty → Ty → Ty
    | plus => HAdd.hAdd

  infixl:100 " ↤ " => State.pop
  infixl:100 " ↦ " => State.push
  infixl:100 " ↦↦ " => State.pushAll

  inductive Node.Step : Node → State → State → Prop
    | input : (h : s nid.fst ≠ [])
      → Node.Step ⟨nid, .input ts⟩ s (s ↤ nid.fst ↦↦ ⟨(s nid.fst).head h, ts⟩)
    | binOp : {op : BinOp} → (h1 : s nid.fst ≠ []) → (h1 : s nid.snd ≠ [])
      → Node.Step ⟨nid, .binOp op ts⟩ s (s ↤ nid.fst ↤ nid.snd ↦↦ ⟨op.denote v1 v2, ts⟩)

  inductive DFG.Step : DFG → State → State → Prop
    | node : (node : Node) → node ∈ dfg → node.Step s1 s2 → DFG.Step dfg s1 s2

  abbrev DFG.MultiStep (dfg : DFG) := Relation.ReflTransGen dfg.Step

  theorem DFG.multi_step_subst {dfg : DFG} {s1 s2 s3 : State}
    (node : Node) (h_mem : node ∈ dfg) (step : node.Step s1 s2) (heq : s2 = s3)
    : dfg.MultiStep s1 s3 :=
    heq ▸ .single (.node node h_mem step)
end Df

namespace Compiler
  open Arith Df

  abbrev VarMap := List (String × Port)

  structure MarkedDFG where
    dfg : DFG
    vars : VarMap
    ret : Port

  theorem DFG.MultiStep.cons {s1 s2 : State} {dfg : DFG} (node : Node)
    (step : dfg.MultiStep s1 s2) : DFG.MultiStep (node :: dfg) s1 s2 := by
    induction step with
    | refl => rfl
    | tail _ tl ih =>
      cases tl
      rename_i node h_mem ns
      apply Relation.ReflTransGen.tail ih
      apply DFG.Step.node node
      · exact List.mem_cons.mpr (Or.intro_right _ h_mem)
      · exact ns

  -- Merge consumers of input nodes that map to the same variable
  @[simp]
  def mergeVarsAux (g1 : MarkedDFG) : DFG × VarMap → String × Port → DFG × VarMap :=
    λ (dfg, vars) (s, t2) =>
        match dfg.find? (·.id = t2.node) with
        | some ⟨_, .input ts2⟩ =>
          match g1.vars.find? (·.fst = s) with
          | some (_, t1) =>
            let dfg := (dfg.filter (·.id ≠ t2.node)).map (
              λ node =>
                if node.id = t1.node then
                  match node.op with
                  | .input ts1 => {node with op := .input (ts1 ++ ts2)}
                  | _ => node
                else
                  node
            )
            (dfg, vars)
          | none => (dfg, (s, t2) :: vars)
        | _ => (dfg, vars)

  def mergeVars (g1 g2 : MarkedDFG) : DFG × VarMap :=
    g2.vars.foldl (mergeVarsAux g1) (g1.dfg ++ g2.dfg, g1.vars)

  -- Update the "return" value of a graph to be the port of the new output node
  def Node.updateReturn (ret : Port) (newRet : Port) (node : Node) : Node :=
    let replace t := if t = ret then newRet else t
    {node with op :=
      match node.op with
      | .input ts => .input (ts.map replace)
      | .output => .output
      | .binOp op ts => .binOp op (ts.map replace)
    }

  @[simp]
  def mergeTwo (g1 g2 : MarkedDFG) (nid : Nid)
    : DFG × VarMap :=
    let (dfg, vars) := mergeVars g1 g2
    -- Update links to the original output nodes
    let dfg := dfg.map (Node.updateReturn g1.ret nid.fst)
    let dfg := dfg.map (Node.updateReturn g2.ret nid.snd)
    -- Remove all output nodes
    let dfg := dfg.filter (λ node => match node.op with | .output => false | _ => true)
    (dfg, vars)

  @[simp]
  def compileAux (maxNid : Nid) : Exp → MarkedDFG × Nid
    | .var s =>
      let inpId := maxNid
      let outId := maxNid + 1
      let dfg := [⟨inpId, .input [Nid.fst outId]⟩, ⟨outId, .output⟩]
      let vars := [(s, maxNid.fst)]
      (⟨dfg, vars, outId.fst⟩, maxNid + 2)
    | .plus e1 e2 =>
      let (e1, maxNid) := compileAux maxNid e1
      let (e2, maxNid) := compileAux maxNid e2
      let plusId := maxNid
      let outId := maxNid + 1
      let (dfg, vars) := mergeTwo e1 e2 plusId
      let dfg := ⟨plusId, .binOp .plus [outId.fst]⟩ :: ⟨outId, .output⟩ :: dfg
      (⟨dfg, vars, outId.fst⟩, maxNid + 2)

  @[simp]
  def compile (e : Exp) : MarkedDFG :=
    (compileAux 0 e).fst

  @[simp]
  def VarMap.initialState (vars : VarMap) (env : Env) : State :=
    vars.foldl (λ s (name, port) => s ↦ ⟨env name, port⟩) .empty

  theorem List.foldl_induction {f : α → β → α} (init : α) (l : List β)
    (P : α → Prop)
    (h : P init)
    (ih : ∀ agg, ∀ x ∈ l, P agg → P (f agg x))
    : P (l.foldl f init) :=
    match l with
    | [] => h
    | hd :: tl =>
      List.foldl_induction (f init hd) tl P (ih init hd (by simp_all) h)
        (λ agg x h_mem h => ih agg x (by simp_all) h)

  lemma ret_not_in_initial_state {ret : Port} {vars : VarMap} {env : Env}
    (h : ∀ var ∈ vars, ret ≠ var.2) : (vars.initialState env) ret = [] := by
    apply List.foldl_induction State.empty vars (λ s => s ret = []) (f := λ s (name, port) => s ↦ ⟨env name, port⟩)
    · rfl
    · intro s b h_mem ih
      simp_all [h b h_mem]

  @[simp]
  def MarkedDFG.initialState (dfg : MarkedDFG) (env : Env) : State :=
    dfg.vars.initialState env

  @[simp]
  def MarkedDFG.finalState (dfg : MarkedDFG) (v : Ty) : State :=
    λ t => if t = dfg.ret then [v] else []

  -- Proofs

  abbrev dfg_id_lt_max (dfg : DFG) (max : Nid) :=
    ∀ node ∈ dfg, node.id < max

  lemma mergeVarsAux_id_eq :
    node ∈ (mergeVarsAux g1 (dfg, vars) (s, t2)).fst → ∃ node' ∈ dfg, node.id = node'.id := by
    intro h_mem
    aesop

  lemma mergeVars_id_eq {dfg1 dfg2 : MarkedDFG} {node : Node}
    (h_mem : node ∈ (mergeVars dfg1 dfg2).fst)
      : (∃ n1 ∈ dfg1.dfg, node.id = n1.id) ∨ (∃ n2 ∈ dfg2.dfg, node.id = n2.id) := by
    have ⟨n, ⟨h_mem, h_id⟩⟩ : ∃ n ∈ dfg1.dfg ++ dfg2.dfg, node.id = n.id := by
      apply List.foldlRecOn dfg2.vars (mergeVarsAux dfg1) (dfg1.dfg ++ dfg2.dfg, dfg1.vars)
        (motive := λ (g, _) => ∀ n ∈ g, (∃ n' ∈ dfg1.dfg ++ dfg2.dfg, n.id = n'.id))
      · aesop
      · simp_all only [List.mem_append, Prod.forall]
        intro dfg _ h _ _ _ nn h_mem_merge
        obtain ⟨nn', hh⟩ := mergeVarsAux_id_eq h_mem_merge
        aesop
      · exact h_mem
    aesop

  lemma updateReturn_id_eq : (Node.updateReturn ret tag node).id = node.id := by
    simp only [Node.updateReturn]

  lemma merge_id_lt_max {dfg1 dfg2 : MarkedDFG} {nid : Nid}
    (maxId : Nid) (h1 : dfg_id_lt_max dfg1.dfg maxId) (h2: dfg_id_lt_max dfg2.dfg maxId)
    : dfg_id_lt_max (mergeTwo dfg1 dfg2 nid).fst maxId := by
    intro node h_mem
    have : (∃ node1 ∈ dfg1.dfg, node.id = node1.id)
           ∨ (∃ node2 ∈ dfg2.dfg, node.id = node2.id) := by
      simp only [mergeTwo] at h_mem
      have := (List.mem_filter.mp h_mem).left
      obtain ⟨a_update_ret, ⟨h_mem, heq_update_ret⟩⟩ := List.mem_map.mp this
      obtain ⟨a_update_vars, ⟨h_mem, heq_update_vars⟩⟩ := List.mem_map.mp h_mem
      have := mergeVars_id_eq h_mem
      aesop
    aesop

  lemma compile_maxId_lt {e : Exp} {initialMax : Nid}
    : initialMax < (compileAux initialMax e).snd := by
    cases e <;> simp [compileAux]
    rename_i e1 e2
    trans (compileAux initialMax e1).2
    exact compile_maxId_lt
    trans (compileAux (compileAux initialMax e1).2 e2).2
    exact compile_maxId_lt
    simp

  lemma compile_id_lt_max {e : Exp} {initialMax : Nid}
    : dfg_id_lt_max (compileAux initialMax e).fst.dfg (compileAux initialMax e).snd := by
    intro node h_mem
    cases e with
    | var _ =>
      aesop
    | plus e1 e2 =>
      simp_all only [compileAux]
      cases h_mem with
      | head => simp
      | tail _ h =>
        cases h with
        | head => simp
        | tail _ h =>
          generalize h_maxId1 : (compileAux initialMax e1).2 = maxId1 at *
          generalize h_maxId2 : (compileAux maxId1 e2).2 = maxId2 at *
          have e1_ih := @compile_id_lt_max e1 initialMax
          have e2_ih := @compile_id_lt_max e2 maxId1
          rw [h_maxId1] at e1_ih
          rw [h_maxId2] at e2_ih
          have h_lt : maxId1 < maxId2 := by
            rw [←h_maxId2]
            exact compile_maxId_lt
          have e1_ih : dfg_id_lt_max (compileAux initialMax e1).1.dfg maxId2 :=
            λ node h_mem => Nat.lt_trans (e1_ih node h_mem) h_lt
          apply Nat.lt_trans
          · exact merge_id_lt_max maxId2 e1_ih e2_ih node h
          · simp

  abbrev MarkedDFG.ret_if_output (dfg : MarkedDFG) :=
    ∀ node ∈ dfg.dfg, node.op.isOutput = true → node.id = dfg.ret.node

  abbrev MarkedDFG.output_if_ret (dfg : MarkedDFG) :=
    ∀ node ∈ dfg.dfg, node.id = dfg.ret.node → node.op.isOutput = true

  abbrev MarkedDFG.ret_iff_output (dfg : MarkedDFG) :=
    ∀ node ∈ dfg.dfg, node.id = dfg.ret.node ↔ node.op.isOutput = true

  lemma merge_no_output {dfg1 dfg2 : MarkedDFG} {nid : Nid}
    : dfg1.ret_if_output → dfg2.ret_if_output
      → ∀ node ∈ (mergeTwo dfg1 dfg2 nid).fst, node.op.isOutput = false := by
    aesop

  theorem Nat.succ_lt_false {x : Nat} : x + 1 < x → False := by simp
  theorem Nid.succ_lt_false {x : Nid} : x + 1 < x → False := Nat.succ_lt_false

  lemma compileAux_ret_if_output {e : Exp} {maxId : Nid}
    : (compileAux maxId e).fst.ret_if_output := by
    intro node h_mem
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      cases h_mem with
      | head => simp_all
      | tail _ h =>
        cases h with
        | head => simp
        | tail _ h =>
          have e1_ih := @compileAux_ret_if_output e1 maxId
          have e2_ih := @compileAux_ret_if_output e2 (compileAux maxId e1).2
          have := merge_no_output e1_ih e2_ih node h
          simp_all

  lemma compile_output_if_ret {e : Exp}
    : (compile e).output_if_ret := by
    intro node h_mem h_ret
    cases h_cases : e with
    | var _ =>
      simp_all only [compile, compileAux, zero_add, Nid.fst, List.mem_cons,
        List.mem_singleton]
      cases h_mem <;> simp_all
    | plus e1 e2 =>
      simp_all only [compile, compileAux, Nid.fst, List.mem_cons, NodeOp.isOutput]
      cases h_mem with
      | inl h =>
        simp_all
      | inr h =>
        cases h with
        | inl h => rw [h]
        | inr h =>
          generalize h_max0 : (compileAux 0 e1).snd = maxId0 at *
          generalize h_max1 : (compileAux maxId0 e2).snd = maxId1 at *
          have e1_id_lt_max : dfg_id_lt_max (compileAux 0 e1).fst.dfg maxId0 := by
            rw [←h_max0]
            exact compile_id_lt_max
          have e2_id_lt_max : dfg_id_lt_max (compileAux maxId0 e2).fst.dfg maxId1 := by
            rw [←h_max1]
            exact compile_id_lt_max
          have max0_lt_max1 : maxId0 < maxId1 := by
            rw [←h_max1]
            exact compile_maxId_lt
          have e1_id_lt_max : dfg_id_lt_max (compileAux 0 e1).fst.dfg maxId1 :=
            λ node h_mem => LT.lt.trans (e1_id_lt_max node h_mem) max0_lt_max1
          have := merge_id_lt_max maxId1 (nid := maxId1) e1_id_lt_max e2_id_lt_max
          have := this node h
          rw [h_ret] at this
          exfalso
          exact Nid.succ_lt_false this

  lemma compile_ret_iff_output {e : Exp} : (compile e).ret_iff_output :=
    λ node h_mem => Iff.intro (compile_output_if_ret node h_mem) (compileAux_ret_if_output node h_mem)

  lemma compile_ret_is_fst {nid : Nid} {e : Exp}
    : (compile e).ret.node = nid → (compile e).ret = nid.fst := by
    simp only [compile, Nid.fst]
    cases e <;> aesop

  theorem DFG.MultiStep.step_transfer
    (step : DFG.MultiStep dfg1 s1 s2)
    (h : ⦃a b : State⦄ → ∀ node1 ∈ dfg1, node1.Step a b → ∃ node2 ∈ dfg2, node2.Step a b)
    : DFG.MultiStep dfg2 s1 s2 := by
    induction step with
    | refl => rfl
    | tail _ tl ih =>
      apply Relation.ReflTransGen.tail ih
      obtain ⟨node, h_mem, ns⟩ := tl
      obtain ⟨node, h_mem, ns⟩ := h node h_mem ns
      apply DFG.Step.node node h_mem ns

  lemma mergeVars_vars_id_lt {dfg1 dfg2 : MarkedDFG} {maxId : Nid}
    (h1 : ∀ var ∈ dfg1.vars, var.2.node < maxId)
    (h2 : ∀ var ∈ dfg2.vars, var.2.node < maxId)
    : ∀ var ∈ (mergeVars dfg1 dfg2).2, var.2.node < maxId := by
    intro var h_mem
    simp [mergeVars] at h_mem
    apply List.foldl_induction (f := mergeVarsAux dfg1) (dfg1.dfg ++ dfg2.dfg, dfg1.vars) dfg2.vars
      (λ x => ∀ var ∈ x.2, var.2.node < maxId) _ _ _ h_mem
    <;> aesop

  lemma merge_vars_id_lt {dfg1 dfg2 : MarkedDFG} {maxId : Nid}
    (h1 : ∀ var ∈ dfg1.vars, var.2.node < maxId)
    (h2 : ∀ var ∈ dfg2.vars, var.2.node < maxId)
    : ∀ var ∈ (mergeTwo dfg1 dfg2 maxId).2, var.2.node < maxId :=
    mergeVars_vars_id_lt h1 h2

  lemma compile_vars_id_lt {e : Exp} {maxId : Nid}
    : ∀ var ∈ (compileAux maxId e).fst.vars, var.snd.node < (compileAux maxId e).snd := by
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      intro var h_mem
      simp_all only [compileAux, Nid.fst, mergeTwo, Nid.snd, List.map_map]
      trans (compileAux (compileAux maxId e1).2 e2).2
      · apply mergeVars_vars_id_lt _ _ var h_mem
        · intro var h_mem
          trans (compileAux maxId e1).2
          · exact compile_vars_id_lt var h_mem
          · exact compile_maxId_lt
        · exact compile_vars_id_lt
      · simp

  lemma initial_final_eq_false {e : Exp} {maxId : Nid} {env : Env} {v : Ty}
    : (compileAux maxId e).fst.finalState v = (compileAux maxId e).fst.initialState env → False := by
    intro heq
    cases e with
    | var s =>
      suffices h : (compileAux maxId (Exp.var s)).1.finalState v ⟨maxId + 1, 0⟩ = []
        by
          delta MarkedDFG.finalState at h
          simp at h
      rw [heq]
      simp
    | plus e1 e2 =>
      let ret := ((compileAux (compileAux maxId e1).2 e2).2 + 1).fst
      suffices h : (compileAux maxId (e1.plus e2)).1.finalState v ret = [v]
                    ∧ (compileAux maxId (e1.plus e2)).1.initialState env ret = []
        by
          exfalso
          rw [←heq] at h
          simp at h
      apply And.intro
      · aesop
      · apply ret_not_in_initial_state
        intro var h_mem
        suffices h : var.2.node ≠ ret.node by aesop
        suffices h_lt : var.2.node < (compileAux (compileAux maxId e1).2 e2).2
          by
            have h {x y : Nat} : x < y → x ≠ y + 1 := by omega
            exact h h_lt
        simp only [compileAux] at h_mem
        apply merge_vars_id_lt _ _ var h_mem
        · intro var h_mem
          trans (compileAux maxId e1).2
          · exact compile_vars_id_lt var h_mem
          · exact compile_maxId_lt
        · intro var h_mem
          exact compile_vars_id_lt var h_mem

  lemma mergeTwo_eval {e1 e2 : Exp} {env : Env} {x y : Ty} {maxId maxId1 maxId2 : Nid}
    : (h_maxId1 : (compileAux maxId e1).2 = maxId1)
      → (h_maxId2 : (compileAux maxId1 e2).2 = maxId2)
      → (compileAux maxId e1).1.dfg.MultiStep ((compileAux maxId e1).1.initialState env) ((compileAux maxId e1).1.finalState x)
      → (compileAux maxId1 e2).1.dfg.MultiStep ((compileAux maxId1 e2).1.initialState env) ((compileAux maxId1 e2).1.finalState y)
      → (mergeTwo (compileAux maxId e1).1 (compileAux maxId1 e2).1 maxId2).1.MultiStep
          ((mergeTwo (compileAux maxId e1).1 (compileAux maxId1 e2).1 maxId2).2.initialState env)
          (.empty ↦ ⟨x, maxId2.fst⟩ ↦ ⟨y, maxId2.snd⟩) := by
    intro h_maxId1 h_maxId2 h1 h2
    generalize h_g1 : compileAux maxId e1 = g1 at *
    generalize h_g2 : compileAux maxId1 e2 = g2 at *
    obtain ⟨dfg1, vars1⟩ := g1
    obtain ⟨dfg2, vars2⟩ := g2
    generalize h_mg : (mergeTwo dfg1 dfg2 maxId2) = mg
    obtain ⟨dfg_mg, vars_mg⟩ := mg

    generalize h_g1i : dfg1.initialState env = g1i at *
    generalize h_g1f : dfg1.finalState x = g1f at *
    induction h1 with
    | refl =>
      exfalso
      suffices h : (compileAux maxId e1).fst.finalState x = (compileAux maxId e1).fst.initialState env
        from initial_final_eq_false h
      simp_all
    | tail hd1 tl1 ih1 =>
      generalize h_g2i : dfg2.initialState env = g2i at *
      generalize h_g2f : dfg2.finalState y = g2f at *
      induction h2 with
      | refl =>
        exfalso
        suffices h : (compileAux maxId1 e2).fst.finalState y = (compileAux maxId1 e2).fst.initialState env
          from initial_final_eq_false h
        simp_all
      | tail hd2 tl2 ih2 =>
        sorry

  theorem compileAux_value_correct {e : Exp} {env : Env} {v : Ty} {maxId : Nid}
    : Eval env e v
      → (compileAux maxId e).fst.dfg.MultiStep ((compileAux maxId e).fst.initialState env) ((compileAux maxId e).fst.finalState v) := by
    intro eval
    cases e with
    | var s =>
      cases eval
      rename_i h_v
      apply DFG.multi_step_subst ⟨maxId, .input [⟨maxId + 1, 0⟩]⟩
      · simp
      · apply Node.Step.input
        simp
      · aesop
    | plus e1 e2 =>
      simp only [compileAux]
      generalize maxId1_eq : (compileAux maxId e1).2 = maxId1
      generalize maxId2_eq : (compileAux maxId1 e2).2 = maxId2
      cases eval
      rename_i x y eval1 eval2
      trans (.empty ↦ ⟨x, maxId2.fst⟩ ↦ ⟨y, maxId2.snd⟩)
      · apply DFG.MultiStep.cons
        apply DFG.MultiStep.cons
        apply mergeTwo_eval maxId1_eq maxId2_eq
        · exact compileAux_value_correct eval1
        · exact compileAux_value_correct eval2
      · apply DFG.multi_step_subst ⟨maxId2, .binOp .plus [(maxId2 + 1).fst]⟩
        · simp
        · apply Node.Step.binOp (v1 := x) (v2 := y) <;> simp
        · aesop

  theorem compile_value_correct {e : Exp} {env : Env} {v : Ty} (eval : Eval env e v)
    : (compile e).dfg.MultiStep ((compile e).initialState env) ((compile e).finalState v) :=
    compileAux_value_correct eval

  theorem compile_confluence {e : Exp} {a b c : State}
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

  lemma final_state_halts {e : Exp} {v : Ty}
    : ∀ s, (compile e).dfg.MultiStep ((compile e).finalState v) s → s = (compile e).finalState v := by
    intro s step
    induction step with
    | refl => rfl
    | tail _ ns ih =>
      rw [ih] at ns
      cases ns
      rename_i node h_mem ns
      cases ns with
      | input h =>
        rename_i nid ts
        have : nid.fst = (compile e).ret := by aesop
        have : nid = (compile e).ret.node := (Port.mk.inj this).left
        have := (compile_ret_iff_output _ h_mem).mp this
        simp at this
      | binOp h1 h2 =>
        rename_i nid _ _ _ _
        have : nid.fst ≠ (compile e).ret := by
          intro h
          have := (compile_ret_iff_output _ h_mem).mp (Port.mk.inj h).left
          simp_all
        simp_all

  theorem compile_correct {e : Exp} {env : Env} {v : Ty}
    : Eval env e v
      → ∀ s, (compile e).dfg.MultiStep ((compile e).initialState env) s
            → (compile e).dfg.MultiStep s ((compile e).finalState v) := by
    intro as s ds
    have := compile_confluence ds (compile_value_correct as)
    obtain ⟨w, h⟩ := this
    obtain ⟨left, right⟩ := h
    have := final_state_halts w right
    rw [this] at left
    exact left

end Compiler
