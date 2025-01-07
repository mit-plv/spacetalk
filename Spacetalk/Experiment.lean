import Aesop
import Mathlib.Data.Vector.Basic
import Std.Data.DHashMap.Internal.WF
import Mathlib.Data.List.Sublists

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

  @[simp]
  def Node.isInput : Node → Bool
    | ⟨_, .input _⟩ => true
    | _ => false

  @[simp]
  def Node.isOp : Node → Bool
    | ⟨_, .binOp _ _⟩ => true
    | _ => false

  abbrev DFG := List Node

  abbrev DFG.NodeMem (dfg : DFG) := {node : Node // node ∈ dfg}

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
  def State.union (s1 : State) (s2 : State) : State :=
    λ t => (s1 t) ++ (s2 t)

  @[simp]
  def BinOp.denote : BinOp → Ty → Ty → Ty
    | plus => HAdd.hAdd

  infixl:100 " ↤ " => State.pop
  infixl:100 " ↦ " => State.push
  infixl:100 " ↦↦ " => State.pushAll
  infixl:100 " ⊕ " => State.union

  inductive Node.Step : Node → State → State → Prop
    | input : (h : s nid.fst ≠ [])
      → Node.Step ⟨nid, .input ts⟩ s (s ↤ nid.fst ↦↦ ⟨(s nid.fst).head h, ts⟩)
    | binOp : {op : BinOp} → (h1 : s nid.fst ≠ []) → (h2 : s nid.snd ≠ [])
      → Node.Step ⟨nid, .binOp op ts⟩ s (s ↤ nid.fst ↤ nid.snd ↦↦ ⟨op.denote ((s nid.fst).head h1) ((s nid.snd).head h2), ts⟩)

  @[simp]
  def Predicate := Node → State → State → Prop

  inductive PredicatedStep : Predicate → State → State → Prop
    | node : (node : Node) → P node s1 s2 → node.Step s1 s2 → PredicatedStep P s1 s2

  @[simp]
  def DFGMem (dfg : DFG) : Predicate :=
    λ node _ _ => node ∈ dfg

  @[simp]
  def NidContained (low high : Nid) : Predicate :=
    λ _ s1 s2 =>
      ∀ port, port.node < low ∨ port.node > high → s1 port = s2 port

  @[simp]
  def Predicate.isInput : Predicate :=
    λ node _ _ => node.isInput = true

  @[simp]
  def Predicate.isOp : Predicate :=
    λ node _ _ => node.isOp = true

  @[simp]
  def Predicate.and (p1 p2 : Predicate) : Predicate :=
    λ node s1 s2 => p1 node s1 s2 ∧ p2 node s1 s2

  infixr:50 " ∧ " => Predicate.and

  @[simp]
  def DFG.MultiStep (dfg : DFG) := Relation.ReflTransGen (PredicatedStep (DFGMem dfg))

  @[refl]
  theorem DFG.MultiStep.refl' {dfg : DFG} : dfg.MultiStep s s :=
    Relation.ReflTransGen.refl

  @[trans]
  theorem DFG.MultiStep.trans' {dfg : DFG} (s1 : dfg.MultiStep a b) (s2 : dfg.MultiStep b c) : dfg.MultiStep a c :=
    Relation.ReflTransGen.trans s1 s2

  @[simp]
  def DFG.MultiStepContained {dfg : DFG} (low high : Nid) :=
    Relation.ReflTransGen (PredicatedStep (DFGMem dfg ∧ NidContained low high))

  @[simp]
  def DFG.MultiStepContainedInput {dfg : DFG} (low high : Nid) :=
    Relation.ReflTransGen (PredicatedStep (DFGMem dfg ∧ NidContained low high ∧ Predicate.isInput))

  @[simp]
  def DFG.MultiStepContainedOp {dfg : DFG} (low high : Nid) :=
    Relation.ReflTransGen (PredicatedStep (DFGMem dfg ∧ NidContained low high ∧ Predicate.isOp))

  inductive DFG.Canonical : DFG → Nid → Nid → State → State → Prop
    | mk : (s2 : State)
      → dfg.MultiStepContainedInput low high s1 s2
      → dfg.MultiStepContainedOp low high s2 s3
      → DFG.Canonical dfg low high s1 s3

  theorem predicate_transfer {P1 P2 : Predicate} (h : ∀ node, ∀ a b, P1 node a b → P2 node a b)
    (step : Relation.ReflTransGen (PredicatedStep P1) s1 s2) : Relation.ReflTransGen (PredicatedStep P2) s1 s2 := by
    induction step with
    | refl => rfl
    | tail hd tl ih =>
      apply Relation.ReflTransGen.tail ih
      obtain ⟨node, p, step⟩ := tl
      exact PredicatedStep.node node (h _ _ _ p) step

  theorem DFG.Canonical.to_multi_step {dfg : DFG} {s1 s3 : State} : dfg.Canonical low high s1 s3 → dfg.MultiStep s1 s3
  | .mk s2 t1 t2 => by
    trans s2
    · apply predicate_transfer (λ _ _ _ h => h.left) t1
    · apply predicate_transfer (λ _ _ _ h => h.left) t2

  -- inductive DFG.Step : DFG → State → State → Prop
  --   | node : (node : Node) → node ∈ dfg → node.Step s1 s2 → DFG.Step dfg s1 s2

  -- inductive DFG.InputStep : DFG → State → State → Prop
  --   | node : (node : Node) → node.isInput = true → node ∈ dfg → node.Step s1 s2 → DFG.InputStep dfg s1 s2

  -- inductive DFG.OpStep : DFG → State → State → Prop
  --   | node : (node : Node) → node.isOp = true → node ∈ dfg → node.Step s1 s2 → DFG.OpStep dfg s1 s2

  -- def DFG.InputStep.toStep {dfg : DFG} : dfg.InputStep s1 s2 → dfg.Step s1 s2
  --   | .node n _ h_mem step => .node n h_mem step

  -- def DFG.OpStep.toStep {dfg : DFG} : dfg.OpStep s1 s2 → dfg.Step s1 s2
  --   | .node n _ h_mem step => .node n h_mem step

  -- abbrev DFG.MultiInputStep (dfg : DFG) := Relation.ReflTransGen dfg.InputStep

  -- abbrev DFG.MultiOpStep (dfg : DFG) := Relation.ReflTransGen dfg.OpStep

  -- theorem DFG.MultiInputStep.to_MultiStep {dfg : DFG} (h : dfg.MultiInputStep s1 s2) : dfg.MultiStep s1 s2 := by
  --   induction h with
  --   | refl => rfl
  --   | tail hd tl ih => exact Relation.ReflTransGen.tail ih tl.toStep

  -- theorem DFG.MultiOpStep.to_MultiStep {dfg : DFG} (h : dfg.MultiOpStep s1 s2) : dfg.MultiStep s1 s2 := by
  --   induction h with
  --   | refl => rfl
  --   | tail hd tl ih => apply Relation.ReflTransGen.tail ih tl.toStep

  -- theorem Node.Step.subst {node : Node} {s1 s2 s3 : State}
  --   (ns : node.Step s1 s2) (h : s2 = s3) : node.Step s1 s3 :=
  --   h ▸ ns

  -- inductive DFG.Canonical : DFG → State → State → Prop
  --   | mk : (s2 : State)
  --     → dfg.MultiInputStep s1 s2
  --     → dfg.MultiOpStep s2 s3
  --     → DFG.Canonical dfg s1 s3

  -- theorem DFG.Canonical.to_steps {dfg : DFG} {s1 s2 : State} : dfg.Canonical s1 s2 → dfg.MultiStep s1 s2
  -- | .mk _ t1 t2 => .trans t1.to_MultiStep t2.to_MultiStep

  -- theorem DFG.Step.subst {dfg : DFG} {s1 s2 s3 : State}
  --   (step : dfg.Step s1 s2) (h : s2 = s3) : dfg.Step s1 s3 :=
  --   h ▸ step

  -- theorem DFG.OpStep.subst {dfg : DFG} {s1 s2 s3 : State}
  --   (step : dfg.OpStep s1 s2) (h : s2 = s3) : dfg.OpStep s1 s3 :=
  --   h ▸ step

  -- theorem DFG.OpStep.subst_both {dfg : DFG} {s1 s2 s3 s4 : State}
  --   (step : dfg.OpStep s1 s2) (h1 : s1 = s3) (h2 : s2 = s4) : dfg.OpStep s3 s4 :=
  --   h1 ▸ h2 ▸ step

  -- theorem DFG.MultiOpStep.subst {dfg : DFG} {s1 s2 s3 : State}
  --   (step : dfg.MultiOpStep s1 s2) (h : s2 = s3) : dfg.MultiOpStep s1 s3 :=
  --   h ▸ step

  theorem DFG.MultiStep.subst_right {dfg : DFG} {s1 s2 s3 : State}
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
      apply Relation.ReflTransGen.tail ih (.node node _ _)
      · exact List.mem_cons.mpr (.inr h_mem)
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

  theorem List.foldl_dual_induction {f₁ : α₁ → β₁ → α₁} {f₂ : α₂ → β₂ → α₂}
    (init₁ : α₁) (init₂ : α₂) (l₁ : List β₁) (l₂ : List β₂) (P : α₁ → α₂ → Prop)
    (h_length : l₁.length = l₂.length) (h : P init₁ init₂)
    (ih : ∀ agg₁, ∀ agg₂, ∀ x ∈ l₁.zip l₂, P agg₁ agg₂ → P (f₁ agg₁ x.1) (f₂ agg₂ x.2))
    : P (l₁.foldl f₁ init₁) (l₂.foldl f₂ init₂) :=
    match l₁, l₂ with
    | [], [] => h
    | hd₁ :: tl₁, hd₂ :: tl₂ => by
      apply List.foldl_dual_induction (f₁ init₁ hd₁) (f₂ init₂ hd₂) tl₁ tl₂
      · simp_all
      · exact ih init₁ init₂ (hd₁, hd₂) (by simp) h
      · intro agg₁ agg₂ x h_mem ih'
        apply ih
        · simp_all
        · exact ih'

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

  lemma compileAux_max_lt_ret {e : Exp} {maxId : Nid}
    : maxId < (compileAux maxId e).1.ret.node := by
    cases e with
    | var => simp
    | plus e1 e2 =>
      simp
      have h1 := @compile_maxId_lt e1 maxId
      have h2 : (compileAux maxId e1).2 < (compileAux (compileAux maxId e1).2 e2).2 := compile_maxId_lt
      have := Nat.lt_trans h1 h2
      exact Nat.lt_succ_of_lt this

  lemma compileAux_ret_lt_newMax {e : Exp} {maxId : Nid}
    : (compileAux maxId e).1.ret.node < (compileAux maxId e).2 := by
    cases e <;> simp

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

  lemma merge_maxId_le_id
    (ih1 : ∀ node ∈ (compileAux maxId e1).1.dfg, maxId ≤ node.id)
    (ih2 : ∀ node ∈ (compileAux (compileAux maxId e1).2 e2).1.dfg, maxId ≤ node.id)
    (h_mem : node ∈ (mergeTwo (compileAux maxId e1).1 (compileAux (compileAux maxId e1).2 e2).1 (compileAux (compileAux maxId e1).2 e2).2).1)
    : maxId ≤ node.id := by
    simp only [mergeTwo, Nid.snd, Nid.fst, List.map_map, List.mem_filter, List.mem_map,
      Function.comp_apply] at h_mem
    obtain ⟨⟨a, ⟨h_mem, h_eq⟩⟩, _⟩ := h_mem
    suffices h : maxId ≤ a.id by aesop
    apply (mergeVars_id_eq h_mem).elim
    <;> simp_all

  lemma compileAux_maxId_le_id {e : Exp} {maxId : Nid}
    : ∀ node ∈ (compileAux maxId e).1.dfg, maxId ≤ node.id := by
    intro node h_mem
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      simp only [compileAux] at h_mem
      cases h_mem
      · simp only
        trans (compileAux maxId e1).2
        <;> exact Nat.le_of_lt compile_maxId_lt
      · rename_i h_mem
        cases h_mem
        · simp only
          trans (compileAux maxId e1).2
          · exact Nat.le_of_lt compile_maxId_lt
          · trans (compileAux (compileAux maxId e1).2 e2).2
            · exact Nat.le_of_lt compile_maxId_lt
            · simp
        · have ih1 := @compileAux_maxId_le_id e1 maxId
          have ih2 : ∀ node ∈ (compileAux (compileAux maxId e1).2 e2).1.dfg, maxId ≤ node.id :=
            λ node h_mem =>
              Nat.le_trans (Nat.le_of_lt compile_maxId_lt) (@compileAux_maxId_le_id e2 (compileAux maxId e1).2 node h_mem)
          rename_i h_mem
          apply merge_maxId_le_id ih1 ih2 h_mem

  lemma merge_id_lt_max_compileAux {e1 e2 : Exp} {maxId : Nid}
    : dfg_id_lt_max
      (mergeTwo (compileAux maxId e1).1 (compileAux (compileAux maxId e1).2 e2).1 (compileAux (compileAux maxId e1).2 e2).2).1
      (compileAux (compileAux maxId e1).2 e2).2 := by
    apply merge_id_lt_max
    · intro node h_mem
      trans (compileAux maxId e1).2
      · exact compile_id_lt_max node h_mem
      · exact compile_maxId_lt
    · exact compile_id_lt_max

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

  lemma compileAux_output_if_ret {e : Exp} {maxId : Nid}
    : (compileAux maxId e).1.output_if_ret := by
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
          exfalso
          generalize h_max0 : (compileAux maxId e1).snd = maxId0 at *
          generalize h_max1 : (compileAux maxId0 e2).snd = maxId1 at *
          have e1_id_lt_max : dfg_id_lt_max (compileAux maxId e1).fst.dfg maxId0 := by
            rw [←h_max0]
            exact compile_id_lt_max
          have e2_id_lt_max : dfg_id_lt_max (compileAux maxId0 e2).fst.dfg maxId1 := by
            rw [←h_max1]
            exact compile_id_lt_max
          have max0_lt_max1 : maxId0 < maxId1 := by
            rw [←h_max1]
            exact compile_maxId_lt
          have e1_id_lt_max : dfg_id_lt_max (compileAux maxId e1).fst.dfg maxId1 :=
            λ node h_mem => LT.lt.trans (e1_id_lt_max node h_mem) max0_lt_max1
          have := merge_id_lt_max maxId1 (nid := maxId1) e1_id_lt_max e2_id_lt_max
          have := this node h
          rw [h_ret] at this
          exfalso
          rw [←h_max1] at this
          exact Nid.succ_lt_false this

  lemma compileAux_ret_iff_output {e : Exp} {maxId : Nid} : (compileAux maxId e).1.ret_iff_output :=
    λ node h_mem => Iff.intro (compileAux_output_if_ret node h_mem) (compileAux_ret_if_output node h_mem)

  lemma compile_ret_iff_output {e : Exp} : (compile e).ret_iff_output :=
    compileAux_ret_iff_output

  lemma compile_ret_is_fst {nid : Nid} {e : Exp}
    : (compile e).ret.node = nid → (compile e).ret = nid.fst := by
    simp only [compile, Nid.fst]
    cases e <;> aesop

  -- theorem DFG.MultiStep.step_transfer
  --   (step : DFG.MultiStep dfg1 s1 s2)
  --   (h : ⦃a b : State⦄ → ∀ node1 ∈ dfg1, node1.Step a b → ∃ node2 ∈ dfg2, node2.Step a b)
  --   : DFG.MultiStep dfg2 s1 s2 := by
  --   induction step with
  --   | refl => rfl
  --   | tail _ tl ih =>
  --     apply Relation.ReflTransGen.tail ih
  --     obtain ⟨node, h_mem, ns⟩ := tl
  --     obtain ⟨node, h_mem, ns⟩ := h node h_mem ns
  --     apply PredicatedStep.node node h_mem ns

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

  @[simp]
  def mergedState (dfg1 dfg2 : MarkedDFG) (nid : Nid) (s : State) : State :=
    λ t =>
      if t = nid.fst then
        s dfg1.ret
      else if t = nid.snd then
        s dfg2.ret
      else if t = dfg1.ret ∨ t = dfg2.ret then
        []
      else
        s t

  theorem mergedState_eq {dfg1 dfg2 : MarkedDFG} {nid : Nid} {s : State} {p : Port}
    (h_ne_nid : p.node ≠ nid) (h_ne_ret : ¬(p = dfg1.ret ∨ p = dfg2.ret))
    : mergedState dfg1 dfg2 nid s p = s p := by
    aesop

  theorem mergedState_pop_assoc {dfg1 dfg2 : MarkedDFG} {nid : Nid} {s : State} {p : Port}
    (h_ne_nid : p.node ≠ nid) (h_ne_ret : ¬(p = dfg1.ret ∨ p = dfg2.ret))
    : mergedState dfg1 dfg2 nid s ↤ p = mergedState dfg1 dfg2 nid (s ↤ p) := by
    aesop

  theorem mergedState_push_assoc {dfg1 dfg2 : MarkedDFG} {nid : Nid} {s : State} {v : Ty} {p : Port}
    (h_ne_nid : p.node ≠ nid) (h_ret_ne : dfg1.ret ≠ dfg2.ret)
    : mergedState dfg1 dfg2 nid s ↦ ⟨v, if p = dfg1.ret then nid.fst else if p = dfg2.ret then nid.snd else p⟩ = mergedState dfg1 dfg2 nid (s ↦ ⟨v, p⟩) := by
    aesop

  theorem List.zip_map_self_left {f : α → β} {l : List α}
    (h : x ∈ (l.map f).zip l) : x.1 = f x.2 := by
    rw [List.zip_map_left] at h
    simp_all only [List.mem_map, Prod.exists, Prod.map_apply, id_eq]
    obtain ⟨a, b, ⟨h_mem, h_eq⟩⟩ := h
    rw [←h_eq]
    simp only
    rw [List.zip_eq_zipWith, List.zipWith_same] at h_mem
    simp_all

  theorem mergedState_pushAll_assoc {dfg1 dfg2 : MarkedDFG} {nid : Nid} {s : State} {v : Ty} {ps : List Port}
    (h_ne_nid : ∀ p ∈ ps, p.node ≠ nid) (h_ret_ne : dfg1.ret ≠ dfg2.ret)
    : mergedState dfg1 dfg2 nid s ↦↦
        ⟨v, ps.map λ p => if p = dfg1.ret then nid.fst else if p = dfg2.ret then nid.snd else p⟩ =
      mergedState dfg1 dfg2 nid (s ↦↦ ⟨v, ps⟩) := by
    simp only [State.pushAll]
    apply List.foldl_dual_induction
      (P := λ agg₁ agg₂ =>
        agg₁ = mergedState dfg1 dfg2 nid agg₂)
    · simp
    · rfl
    · intro agg₁ agg₂ x h_mem h
      rw [h]
      have := List.zip_map_self_left h_mem
      rw [this]
      apply mergedState_push_assoc
      · apply h_ne_nid
        exact (List.of_mem_zip h_mem).right
      · exact h_ret_ne

  abbrev MergeTwo (e1 e2 : Exp) (maxId : Nid) : DFG × VarMap :=
    mergeTwo (compileAux maxId e1).1 (compileAux (compileAux maxId e1).2 e2).1
      (compileAux (compileAux maxId e1).2 e2).2

  abbrev MergedState (e1 e2 : Exp) (maxId : Nid) (s : State) : State :=
    mergedState (compileAux maxId e1).1 (compileAux (compileAux maxId e1).2 e2).1 (compileAux (compileAux maxId e1).2 e2).2 s

  theorem MergedState_pop_assoc {e1 e2 : Exp} {maxId: Nid} {s : State} {p : Port}
    (h_ne_nid : p.node ≠ (compileAux (compileAux maxId e1).2 e2).2)
    (h_ne_ret : ¬(p = (compileAux maxId e1).1.ret ∨ p = (compileAux (compileAux maxId e1).2 e2).1.ret))
    : MergedState e1 e2 maxId s ↤ p = MergedState e1 e2 maxId (s ↤ p) := by
    aesop

  theorem MergedState_pushAll_assoc {e1 e2 : Exp} {maxId: Nid} {s : State} {v : Ty} {ps : List Port}
    (h_ne_nid : ∀ p ∈ ps, p.node ≠ (compileAux (compileAux maxId e1).2 e2).2)
    : MergedState e1 e2 maxId s ↦↦
        ⟨v, ps.map λ p => if p = (compileAux maxId e1).1.ret then
                            (compileAux (compileAux maxId e1).2 e2).2.fst
                          else if p = (compileAux (compileAux maxId e1).2 e2).1.ret then
                            (compileAux (compileAux maxId e1).2 e2).2.snd
                          else
                            p⟩ =
      MergedState e1 e2 maxId (s ↦↦ ⟨v, ps⟩) :=
    have h : (compileAux maxId e1).1.ret ≠ (compileAux (compileAux maxId e1).2 e2).1.ret := by
      have h1 := @compileAux_ret_lt_newMax e1 maxId
      have h2 := @compileAux_max_lt_ret e2 (compileAux maxId e1).2
      have := Nat.lt_trans h1 h2
      have := Nat.ne_of_lt this
      aesop
    mergedState_pushAll_assoc h_ne_nid h

  abbrev NodeEq (dfg : DFG) : Prop :=
    ∀ node1 ∈ dfg, ∀ node2 ∈ dfg, node1.id = node2.id → node1 = node2

  abbrev CompileNodeEq (e : Exp) (maxId : Nid) : Prop :=
    NodeEq (compileAux maxId e).1.dfg

  lemma append_node_eq {dfg1 dfg2 : DFG} (h1 : NodeEq dfg1) (h2 : NodeEq dfg2)
    (h_disj : ∀ node1 ∈ dfg1, ∀ node2 ∈ dfg2, node1.id ≠ node2.id) : NodeEq (dfg1 ++ dfg2) := by
    intro node1 h_mem1 node2 h_mem2 h_eq
    apply (List.mem_append.mp h_mem1).elim <;> apply (List.mem_append.mp h_mem2).elim
    · aesop
    · aesop
    · intro h_mem1 h_mem2
      have := (h_disj node2 h_mem1 node1 h_mem2).symm
      contradiction
    · aesop

  lemma compile_seq_node_disj (e1 e2 : Exp) (maxId : Nid)
    : ∀ node1 ∈ (compileAux maxId e1).1.dfg, ∀ node2 ∈ (compileAux (compileAux maxId e1).2 e2).1.dfg, node1.id ≠ node2.id := by
    intro node1 h_mem1 node2 h_mem2
    have e1_lt := @compile_id_lt_max e1 maxId
    have e2_gt := @compileAux_maxId_le_id e2 (compileAux maxId e1).2
    suffices h : node1.id < node2.id from Nat.ne_of_lt h
    apply Nat.lt_of_lt_of_le
    · exact compile_id_lt_max node1 h_mem1
    · exact compileAux_maxId_le_id node2 h_mem2

  lemma compile_binop_consumer_lt_max {e : Exp} {maxId : Nid}
    (h : ⟨nid, .binOp op ps⟩ ∈ (compileAux maxId e).1.dfg) : ∀ p ∈ ps, p.node < (compileAux maxId e).2 := by
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      simp only [compileAux, Nid.fst, mergeTwo, Nid.snd, List.map_map, List.mem_cons, Node.mk.injEq,
        NodeOp.binOp.injEq, true_and, reduceCtorEq, and_false, List.mem_filter, List.mem_map,
        Function.comp_apply, and_true, false_or] at h
      apply h.elim
      · intro h
        simp_all
      · intro h
        obtain ⟨a, ⟨h_mem, h_eq⟩⟩ := h
        simp only [Node.updateReturn, Node.mk.injEq] at h_eq
        obtain ⟨h_id, h_eq⟩ := h_eq
        split at h_eq
        · contradiction
        · contradiction
        · rename_i _ _ ps1 h_eq1
          split at h_eq1
          · contradiction
          · contradiction
          · rename_i _ op ps2 h_eq2
            suffices h : ∀ p ∈ ps2, p.node < (compileAux maxId (e1.plus e2)).2 by aesop
            apply List.foldl_induction ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars) (compileAux (compileAux maxId e1).2 e2).1.vars
              (λ x => a ∈ x.1 → ∀ p ∈ ps2, p.node < (compileAux maxId (e1.plus e2)).2) _ _ h_mem
            have h_a_eq : a = ⟨nid, .binOp op ps2⟩ := by rw [←h_eq2, ←h_id]
            rw [h_a_eq] at *
            · intro h_mem
              apply (List.mem_append.mp h_mem).elim
              · intro h_mem
                intro p h_mem
                rename_i _ _ h_mem'
                trans (compileAux maxId e1).2
                · exact compile_binop_consumer_lt_max h_mem' p h_mem
                · trans (compileAux (compileAux maxId e1).2 e2).2
                  · exact compile_maxId_lt
                  · simp
              · intro h_mem
                intro p h_mem'
                trans (compileAux (compileAux maxId e1).2 e2).2
                · exact compile_binop_consumer_lt_max h_mem p h_mem'
                · simp
            · intro agg x h_mem_x ih h_mem_a
              intro p h_mem_p
              simp only [mergeVarsAux] at h_mem_a
              split at h_mem_a
              · split at h_mem_a
                · simp only [ne_eq, decide_not, List.mem_map, List.mem_filter,
                  Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_mem_a
                  obtain ⟨a1, ⟨⟨h_mem_a1, _⟩, h_eq_a1⟩⟩ := h_mem_a
                  split at h_eq_a1
                  · have h_a_eq : a = ⟨nid, .binOp op ps2⟩ := by rw [←h_id, ←h_eq2]
                    rw [h_a_eq] at h_eq_a1
                    split at h_eq_a1
                    · simp_all
                    · exact ih (h_a_eq ▸ h_eq_a1 ▸ h_mem_a1) p h_mem_p
                  · exact ih (h_eq_a1 ▸ h_mem_a1) p h_mem_p
                · exact ih h_mem_a p h_mem_p
              · exact ih h_mem_a p h_mem_p

  @[simp]
  lemma node_eq_mergeVars {e : Exp} {maxId : Nid} {dfgVars : DFG × VarMap}
    (h : NodeEq dfgVars.1) : NodeEq (mergeVarsAux (compileAux maxId e).1 dfgVars x).1 := by
    intro node1 h_mem1 node2 h_mem2 h_id_eq
    simp_all only [mergeVarsAux, Prod.fst]
    cases h_find? : List.find? (fun x_1 => decide (x_1.id = x.2.node)) dfgVars.1 with
    | none =>
      simp_all only [Prod.mk.eta, List.find?_eq_none, decide_eq_true_eq]
      apply h node1 h_mem1 node2 h_mem2 h_id_eq
    | some val =>
      obtain ⟨id, op⟩ := val
      cases op
      <;> try (simp_all only [Prod.mk.eta]; apply h <;> assumption)
      case input ts =>
        cases h_find? : List.find? (fun x_1 => decide (x_1.id = x.2.node)) dfgVars.1 with
        | some node =>
          simp_all only [ne_eq, decide_not, Prod.mk.eta, Option.some.injEq]
          cases h_find? : List.find? (fun x_1 => decide (x_1.1 = x.1)) (compileAux maxId e).1.vars with
          | some varPort =>
            simp_all only [List.mem_map, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not]
            obtain ⟨a, ⟨⟨h_mem_a, _⟩, h_eq_a⟩⟩ := h_mem1
            obtain ⟨b, ⟨⟨h_mem_b, _⟩, h_eq_b⟩⟩ := h_mem2
            rw [←h_eq_a, ←h_eq_b] at h_id_eq
            if h_a : a.id = varPort.2.node then
              if h_b : b.id = varPort.2.node then
                have := h a h_mem_a b h_mem_b (Eq.trans h_a h_b.symm)
                cases h_a_op: a.op <;> cases h_b_op : b.op
                <;> simp_all
              else
                cases h_a_op : a.op
                · simp only [h_a, ↓reduceIte, h_a_op, h_b] at h_id_eq
                  have := h_id_eq.symm
                  contradiction
                · simp_all
                · simp_all
            else
              if h_b : b.id = varPort.2.node then
                simp only [h_a, ↓reduceIte, h_b] at h_id_eq
                cases h_op : b.op
                · simp only [h_op] at h_id_eq
                  contradiction
                · simp_all
                · simp_all
              else
                simp_all only [implies_true, ite_self, not_false_eq_true]
                apply h <;> assumption
          | none =>
            simp_all only [List.find?_eq_none, decide_eq_true_eq, Prod.forall]
            apply h <;> assumption
        | none => simp_all

  lemma node_eq_mergeTwo
    (h1 : NodeEq (compileAux maxId e1).1.dfg)
    (h2 : NodeEq (compileAux (compileAux maxId e1).2 e2).1.dfg)
    : NodeEq (List.foldl (mergeVarsAux (compileAux maxId e1).1)
              ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars)
              (compileAux (compileAux maxId e1).2 e2).1.vars).1 := by
    apply List.foldl_induction ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars) (compileAux (compileAux maxId e1).2 e2).1.vars
      (λ x => NodeEq x.1)
    · apply append_node_eq h1 h2
      intro node1 h_mem1 node2 h_mem2
      suffices h : node1.id < node2.id from Nat.ne_of_lt h
      apply Nat.lt_of_lt_of_le
      · exact compile_id_lt_max node1 h_mem1
      · exact compileAux_maxId_le_id node2 h_mem2
    · intro _ _ _
      exact node_eq_mergeVars

  lemma compile_node_eq (e : Exp) (maxId : Nid) : CompileNodeEq e maxId := by
    cases e with
    | var _ => simp [CompileNodeEq, NodeEq]
    | plus e1 e2 =>
      simp only [CompileNodeEq, NodeEq]
      intro node1 h_mem1 node2 h_mem2 heq
      simp only [compileAux] at *
      cases h_mem1 <;> cases h_mem2
      · rfl
      · rename_i h_mem2
        cases h_mem2
        · simp at heq
        · simp only at heq
          rename_i h_mem2
          have := merge_id_lt_max_compileAux node2 h_mem2
          have := Nat.ne_of_lt this
          have := heq.symm
          contradiction
      · rename_i h_mem1
        cases h_mem1
        · simp at heq
        · simp only at heq
          rename_i h_mem1
          have := merge_id_lt_max_compileAux node1 h_mem1
          have := Nat.ne_of_lt this
          have := heq.symm
          contradiction
      · rename_i h_mem1 h_mem2
        cases h_mem1 <;> cases h_mem2
        · rfl
        · rename_i h_mem2
          have := merge_id_lt_max_compileAux node2 h_mem2
          simp only at heq
          rw [←heq] at this
          exfalso
          exact Nid.succ_lt_false this
        · rename_i h_mem1
          have := merge_id_lt_max_compileAux node1 h_mem1
          simp only at heq
          rw [heq] at this
          exfalso
          exact Nid.succ_lt_false this
        · rename_i h_mem1 h_mem2
          obtain ⟨h_mem1, _⟩ := List.mem_filter.mp h_mem1
          obtain ⟨h_mem2, _⟩ := List.mem_filter.mp h_mem2
          rw [←List.comp_map] at h_mem1
          rw [←List.comp_map] at h_mem2
          obtain ⟨a, ⟨h_mem_a, h_eq_a⟩⟩ := List.mem_map.mp h_mem1
          obtain ⟨b, ⟨h_mem_b, h_eq_b⟩⟩ := List.mem_map.mp h_mem2
          have := node_eq_mergeTwo (compile_node_eq _ _) (compile_node_eq _ _) a h_mem_a b h_mem_b
          suffices h : a.id = b.id by simp_all
          aesop

  -- theorem op_step_to_merged_left {e1 e2 : Exp} {maxId : Nid} {s1 s2 : State}
  --   (s : (compileAux maxId e1).1.dfg.OpStep s1 s2)
  --   : (MergeTwo e1 e2 maxId).1.OpStep (MergedState e1 e2 maxId s1) (MergedState e1 e2 maxId s2) :=
  --   match s with
  --   | .node ⟨nid, .binOp op ts⟩ _ h_mem s =>
  --     match s with
  --     | .binOp h1 h2 => by
  --       let newRet := (compileAux (compileAux maxId e1).2 e2).2
  --       let newTs :=
  --         (ts.map (λ t => if t = (compileAux maxId e1).1.ret then newRet.fst else t)).map
  --                 (λ t => if t = (compileAux (compileAux maxId e1).2 e2).1.ret then newRet.snd else t)
  --       have h_mem' : ⟨nid, .binOp op newTs⟩ ∈ (MergeTwo e1 e2 maxId).1 := by
  --         apply List.mem_filter.mpr
  --         apply And.intro
  --         · apply List.mem_map.mpr
  --           exists ⟨nid, .binOp op (ts.map (λ t => if t = (compileAux maxId e1).1.ret then newRet.fst else t))⟩
  --           apply And.intro
  --           · apply List.mem_map.mpr
  --             exists ⟨nid, .binOp op ts⟩
  --             apply And.intro
  --             · apply (List.foldl_induction
  --                 ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars)
  --                 (compileAux (compileAux maxId e1).2 e2).1.vars
  --                 (λ agg => NodeEq agg.1 ∧ ⟨nid, .binOp op ts⟩ ∈ (Prod.fst agg)) _ _).right
  --               · apply And.intro
  --                 · apply append_node_eq
  --                   · apply compile_node_eq
  --                   · apply compile_node_eq
  --                   · apply compile_seq_node_disj
  --                 · simp_all
  --               · intro agg x h_mem_x ih
  --                 apply And.intro
  --                 · exact node_eq_mergeVars ih.left
  --                 · simp only [mergeVarsAux]
  --                   split
  --                   next heq =>
  --                     rename_i _ id ts2
  --                     simp
  --                     split
  --                     next =>
  --                       apply List.mem_map.mpr
  --                       exists ⟨nid, .binOp op ts⟩
  --                       apply And.intro
  --                       · apply List.mem_filter.mpr
  --                         apply And.intro ih.right
  --                         simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  --                         intro h
  --                         suffices h : (⟨nid, .binOp op ts⟩ : Node) = ⟨nid, .input ts2⟩ by aesop
  --                         apply ih.left _ ih.right _ _ (by simp)
  --                         have : nid = id := by have := List.find?_some heq; aesop
  --                         rw [this]
  --                         apply List.mem_of_find?_eq_some heq
  --                       · aesop
  --                     next => aesop
  --                   next => aesop
  --             · simp only [Node.updateReturn]
  --           · simp only [Node.updateReturn]
  --         · simp
  --       have h_nid_ne_ret : nid ≠ (compileAux (compileAux maxId e1).2 e2).2 := by
  --         have h1 : nid < (compileAux maxId e1).2 := compile_id_lt_max _ h_mem
  --         have h2 : (compileAux maxId e1).2 < (compileAux (compileAux maxId e1).2 e2).2 := compile_maxId_lt
  --         have := Nat.lt_trans h1 h2
  --         intro heq
  --         apply (lt_self_iff_false nid).mp
  --         rw [←heq] at this
  --         exact this
  --       have h_fst_ne_ret : ¬(nid.fst = (compileAux maxId e1).1.ret ∨ nid.fst = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
  --         simp only [Nid.fst, not_or]
  --         apply And.intro
  --         · intro heq
  --           have h_id : nid = (compileAux maxId e1).1.ret.node := (Port.mk.inj heq).left
  --           have := compileAux_ret_iff_output ⟨nid, .binOp op ts⟩ h_mem
  --           have := this.mp h_id
  --           contradiction
  --         · intro heq
  --           have h_id : nid = (compileAux (compileAux maxId e1).2 e2).1.ret.node := (Port.mk.inj heq).left
  --           have h_lt : nid < (compileAux maxId e1).2 := compile_id_lt_max _ h_mem
  --           have := @compileAux_max_lt_ret e2 (compileAux maxId e1).2
  --           have := Nat.lt_trans h_lt this
  --           have := Nat.ne_of_lt this
  --           contradiction
  --       have h_snd_ne_ret : ¬(nid.snd = (compileAux maxId e1).1.ret ∨ nid.snd = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
  --         simp only [Nid.fst, not_or]
  --         apply And.intro
  --         · intro heq
  --           have h_id : nid = (compileAux maxId e1).1.ret.node := (Port.mk.inj heq).left
  --           have := compileAux_ret_iff_output ⟨nid, .binOp op ts⟩ h_mem
  --           have := this.mp h_id
  --           contradiction
  --         · intro heq
  --           have h_id : nid = (compileAux (compileAux maxId e1).2 e2).1.ret.node := (Port.mk.inj heq).left
  --           have h_lt : nid < (compileAux maxId e1).2 := compile_id_lt_max _ h_mem
  --           have := @compileAux_max_lt_ret e2 (compileAux maxId e1).2
  --           have := Nat.lt_trans h_lt this
  --           have := Nat.ne_of_lt this
  --           contradiction
  --       have h_fst_eq : MergedState e1 e2 maxId s1 nid.fst = s1 nid.fst := mergedState_eq h_nid_ne_ret h_fst_ne_ret
  --       have h_snd_eq : MergedState e1 e2 maxId s1 nid.snd = s1 nid.snd := mergedState_eq h_nid_ne_ret h_snd_ne_ret
  --       apply DFG.OpStep.subst
  --       · apply DFG.OpStep.node ⟨nid, .binOp op newTs⟩
  --         · simp
  --         · exact h_mem'
  --         · exact (.binOp (h_fst_eq ▸ h1) (h_snd_eq ▸ h2))
  --       · simp_rw [h_fst_eq, h_snd_eq]
  --         rw [MergedState_pop_assoc h_nid_ne_ret h_fst_ne_ret]
  --         rw [MergedState_pop_assoc h_nid_ne_ret h_snd_ne_ret]
  --         simp only [newTs, newRet]
  --         rw [←List.comp_map]
  --         have : ((fun t =>
  --                     if t = (compileAux (compileAux maxId e1).2 e2).1.ret then (compileAux (compileAux maxId e1).2 e2).2.snd
  --                     else t) ∘
  --                   fun t => if t = (compileAux maxId e1).1.ret then (compileAux (compileAux maxId e1).2 e2).2.fst else t) =
  --                 (fun p =>
  --               if p = (compileAux maxId e1).1.ret then (compileAux (compileAux maxId e1).2 e2).2.fst
  --               else
  --                 if p = (compileAux (compileAux maxId e1).2 e2).1.ret then (compileAux (compileAux maxId e1).2 e2).2.snd
  --                 else p) := by
  --           funext x
  --           if x = (compileAux maxId e1).1.ret then
  --             simp_all only [Nid.fst, ne_eq, Nid.snd, mergeTwo, List.map_map, List.mem_filter,
  --               List.mem_map, Function.comp_apply, and_true, not_or, mergedState, Port.mk.injEq,
  --               zero_ne_one, and_self, or_self, ite_false, one_ne_zero, ite_true, ite_eq_right_iff]
  --             intro h_ret_eq
  --             have h_lt := @compileAux_ret_lt_newMax e2 (compileAux maxId e1).2
  --             have h_eq := (Port.mk.inj h_ret_eq).left.symm
  --             have := Nat.ne_of_lt h_lt
  --             contradiction
  --           else
  --             aesop
  --         rw [this]
  --         apply @MergedState_pushAll_assoc e1 e2 maxId (s1 ↤ nid.fst ↤ nid.snd) (op.denote ((s1 nid.fst).head h1) ((s1 nid.snd).head h2)) ts
  --         have h_lt := @compile_maxId_lt e2 (compileAux maxId e1).2
  --         have := compile_binop_consumer_lt_max h_mem
  --         intro p h_mem
  --         have := this p h_mem
  --         have := Nat.lt_trans this h_lt
  --         apply Nat.ne_of_lt this

  -- theorem op_multi_step_to_merged_left {e1 e2 : Exp} {maxId : Nid} {s1 s2 : State}
  --   (step : (compileAux maxId e1).1.dfg.MultiOpStep s1 s2)
  --   : (MergeTwo e1 e2 maxId).1.MultiOpStep (MergedState e1 e2 maxId s1) (MergedState e1 e2 maxId s2) := by
  --   induction step with
  --   | refl => rfl
  --   | tail hd tl ih => exact Relation.ReflTransGen.tail ih (op_step_to_merged_left tl)

  -- theorem op_step_to_merged_right {e1 e2 : Exp} {maxId : Nid} {s1 s2 : State}
  --   (s : (compileAux (compileAux maxId e1).2 e2).1.dfg.OpStep s1 s2)
  --   : (MergeTwo e1 e2 maxId).1.OpStep (MergedState e1 e2 maxId s1) (MergedState e1 e2 maxId s2) :=
  --   match s with
  --   | .node ⟨nid, .binOp op ts⟩ _ h_mem s =>
  --     match s with
  --     | .binOp h1 h2 => by
  --       let newRet := (compileAux (compileAux maxId e1).2 e2).2
  --       let newTs :=
  --         (ts.map (λ t => if t = (compileAux maxId e1).1.ret then newRet.fst else t)).map
  --                 (λ t => if t = (compileAux (compileAux maxId e1).2 e2).1.ret then newRet.snd else t)
  --       have h_mem' : ⟨nid, .binOp op newTs⟩ ∈ (MergeTwo e1 e2 maxId).1 := by
  --         apply List.mem_filter.mpr
  --         apply And.intro
  --         · apply List.mem_map.mpr
  --           exists ⟨nid, .binOp op (ts.map (λ t => if t = (compileAux maxId e1).1.ret then newRet.fst else t))⟩
  --           apply And.intro
  --           · apply List.mem_map.mpr
  --             exists ⟨nid, .binOp op ts⟩
  --             apply And.intro
  --             · apply (List.foldl_induction
  --                 ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars)
  --                 (compileAux (compileAux maxId e1).2 e2).1.vars
  --                 (λ agg => NodeEq agg.1 ∧ ⟨nid, .binOp op ts⟩ ∈ (Prod.fst agg)) _ _).right
  --               · apply And.intro
  --                 · apply append_node_eq
  --                   · apply compile_node_eq
  --                   · apply compile_node_eq
  --                   · apply compile_seq_node_disj
  --                 · simp_all
  --               · intro agg x h_mem_x ih
  --                 apply And.intro
  --                 · exact node_eq_mergeVars ih.left
  --                 · simp only [mergeVarsAux]
  --                   split
  --                   next heq =>
  --                     rename_i _ id ts2
  --                     simp
  --                     split
  --                     next =>
  --                       apply List.mem_map.mpr
  --                       exists ⟨nid, .binOp op ts⟩
  --                       apply And.intro
  --                       · apply List.mem_filter.mpr
  --                         apply And.intro ih.right
  --                         simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  --                         intro h
  --                         suffices h : (⟨nid, .binOp op ts⟩ : Node) = ⟨nid, .input ts2⟩ by aesop
  --                         apply ih.left _ ih.right _ _ (by simp)
  --                         have : nid = id := by have := List.find?_some heq; aesop
  --                         rw [this]
  --                         apply List.mem_of_find?_eq_some heq
  --                       · aesop
  --                     next => aesop
  --                   next => aesop
  --             · simp only [Node.updateReturn]
  --           · simp only [Node.updateReturn]
  --         · simp
  --       have h_nid_ne_ret : nid ≠ (compileAux (compileAux maxId e1).2 e2).2 := by
  --         suffices h : nid < (compileAux (compileAux maxId e1).2 e2).2 from Nat.ne_of_lt h
  --         exact compile_id_lt_max _ h_mem
  --       have h_fst_ne_ret : ¬(nid.fst = (compileAux maxId e1).1.ret ∨ nid.fst = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
  --         simp only [Nid.fst, not_or]
  --         apply And.intro
  --         · intro heq
  --           apply Nat.not_le_of_lt
  --           · exact (Port.mk.inj heq).left ▸ compileAux_ret_lt_newMax
  --           · exact compileAux_maxId_le_id _ h_mem
  --         · intro heq
  --           have := (compileAux_ret_iff_output _ h_mem).mp
  --           simp only [NodeOp.isOutput, Bool.false_eq_true, imp_false] at this
  --           exact this (Port.mk.inj heq).left
  --       have h_snd_ne_ret : ¬(nid.snd = (compileAux maxId e1).1.ret ∨ nid.snd = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
  --         simp only [Nid.fst, not_or]
  --         apply And.intro
  --         · intro heq
  --           apply Nat.not_le_of_lt
  --           · exact (Port.mk.inj heq).left ▸ compileAux_ret_lt_newMax
  --           · exact compileAux_maxId_le_id _ h_mem
  --         · intro heq
  --           have := (compileAux_ret_iff_output _ h_mem).mp
  --           simp only [NodeOp.isOutput, Bool.false_eq_true, imp_false] at this
  --           exact this (Port.mk.inj heq).left
  --       have h_fst_eq : MergedState e1 e2 maxId s1 nid.fst = s1 nid.fst := mergedState_eq h_nid_ne_ret h_fst_ne_ret
  --       have h_snd_eq : MergedState e1 e2 maxId s1 nid.snd = s1 nid.snd := mergedState_eq h_nid_ne_ret h_snd_ne_ret
  --       apply DFG.OpStep.subst
  --       · apply DFG.OpStep.node ⟨nid, .binOp op newTs⟩
  --         · simp
  --         · exact h_mem'
  --         · exact (.binOp (h_fst_eq ▸ h1) (h_snd_eq ▸ h2))
  --       · simp_rw [h_fst_eq, h_snd_eq]
  --         rw [MergedState_pop_assoc h_nid_ne_ret h_fst_ne_ret]
  --         rw [MergedState_pop_assoc h_nid_ne_ret h_snd_ne_ret]
  --         simp only [newTs, newRet]
  --         rw [←List.comp_map]
  --         have : ((fun t =>
  --                     if t = (compileAux (compileAux maxId e1).2 e2).1.ret then (compileAux (compileAux maxId e1).2 e2).2.snd
  --                     else t) ∘
  --                   fun t => if t = (compileAux maxId e1).1.ret then (compileAux (compileAux maxId e1).2 e2).2.fst else t) =
  --                 (fun p =>
  --               if p = (compileAux maxId e1).1.ret then (compileAux (compileAux maxId e1).2 e2).2.fst
  --               else
  --                 if p = (compileAux (compileAux maxId e1).2 e2).1.ret then (compileAux (compileAux maxId e1).2 e2).2.snd
  --                 else p) := by
  --           funext x
  --           if x = (compileAux maxId e1).1.ret then
  --             simp_all only [Nid.fst, ne_eq, Nid.snd, mergeTwo, List.map_map, List.mem_filter,
  --               List.mem_map, Function.comp_apply, and_true, not_or, mergedState, Port.mk.injEq,
  --               zero_ne_one, and_self, or_self, ite_false, one_ne_zero, ite_true, ite_eq_right_iff]
  --             intro h_ret_eq
  --             have h_lt := @compileAux_ret_lt_newMax e2 (compileAux maxId e1).2
  --             have h_eq := (Port.mk.inj h_ret_eq).left.symm
  --             have := Nat.ne_of_lt h_lt
  --             contradiction
  --           else
  --             aesop
  --         rw [this]
  --         apply @MergedState_pushAll_assoc e1 e2 maxId (s1 ↤ nid.fst ↤ nid.snd) (op.denote ((s1 nid.fst).head h1) ((s1 nid.snd).head h2)) ts
  --         have h_lt := @compile_maxId_lt e2 (compileAux maxId e1).2
  --         have := compile_binop_consumer_lt_max h_mem
  --         intro p h_mem
  --         exact Nat.ne_of_lt (this p h_mem)

  -- theorem op_multi_step_to_merged_right {e1 e2 : Exp} {maxId : Nid} {s1 s2 : State}
  --   (step : (compileAux (compileAux maxId e1).2 e2).1.dfg.MultiOpStep s1 s2)
  --   : (MergeTwo e1 e2 maxId).1.MultiOpStep (MergedState e1 e2 maxId s1) (MergedState e1 e2 maxId s2) := by
  --   induction step with
  --   | refl => rfl
  --   | tail hd tl ih => exact Relation.ReflTransGen.tail ih (op_step_to_merged_right tl)

  -- lemma op_step_irrelevant_state {dfg : DFG} (h_disj : s3 nid.fst = [] ∧ s3 nid.snd = [] ∧ ∀ p ∈ ps, s3 p = [])
  --   (h_mem : ⟨nid, .binOp op ps⟩ ∈ dfg)
  --   (step : (⟨nid, .binOp op ps⟩ : Node).Step s1 s2) : dfg.OpStep (s1 ⊕ s3) (s2 ⊕ s3) := by
  --   apply DFG.OpStep.node ⟨nid, .binOp op ps⟩
  --   · simp
  --   · exact h_mem
  --   · cases step
  --     rename_i h1 h2
  --     have h1 : (s1 ⊕ s3) nid.fst ≠ [] := by simp_all
  --     have h2 : (s1 ⊕ s3) nid.snd ≠ [] := by simp_all
  --     have : ∀ v1 v2, v1 = v2 → (s1 ↤ nid.fst ↤ nid.snd ↦↦ ⟨v1, ps⟩).union s3 = (s1 ⊕ s3) ↤ nid.fst ↤ nid.snd ↦↦ ⟨v2, ps⟩ := by
  --       intro v1 v2 h_eq
  --       have : (s1 ⊕ s3) ↤ nid.fst = s1 ↤ nid.fst ⊕ s3 := by aesop
  --       rw [this]
  --       have : (s1 ↤ nid.fst).union s3 ↤ nid.snd = (s1 ↤ nid.fst ↤ nid.snd).union s3 := by aesop
  --       rw [this]
  --       rw [h_eq]
  --       apply List.foldl_dual_induction _ _ _ _
  --         (λ agg₁ agg₂ => (agg₁ ⊕ s3) = agg₂)
  --       · rfl
  --       · rfl
  --       · intro agg₁ agg₂ x h_mem h_eq
  --         have : x.1 = x.2 := by
  --           simp only [List.zip, List.zipWith_same, List.mem_map] at h_mem
  --           obtain ⟨a, h⟩ := h_mem
  --           aesop
  --         rw [this]
  --         have : s3 x.2 = [] := by
  --           simp only [List.zip, List.zipWith_same, List.mem_map] at h_mem
  --           obtain ⟨a, h⟩ := h_mem
  --           have : x.2 = a := by aesop
  --           rw [this]
  --           exact h_disj.right.right a h.left
  --         aesop
  --     rw [this]
  --     apply Node.Step.binOp (op := op) (ts := ps) h1 h2
  --     simp_all

  -- lemma compileAux_canonical_trace {e : Exp} {env : Env} {v : Ty} {maxId : Nid}
  --   (eval : Eval env e v) : (compileAux maxId e).1.dfg.Canonical ((compileAux maxId e).1.initialState env) ((compileAux maxId e).1.finalState v) :=
  --   match e with
  --   | .var s => by
  --     apply DFG.Canonical.mk
  --     · apply Relation.ReflTransGen.single
  --       apply DFG.InputStep.node ⟨maxId, .input [(maxId + 1).fst]⟩
  --       · simp
  --       · simp
  --       · apply Node.Step.input; simp
  --     · apply DFG.MultiOpStep.subst .refl
  --       have : env s = v := by cases eval; assumption
  --       aesop
  --   | .plus e1 e2 => by
  --     generalize maxId1_eq : (compileAux maxId e1).2 = maxId1 at *
  --     generalize maxId2_eq : (compileAux maxId1 e2).2 = maxId2 at *
  --     cases eval
  --     rename_i x y eval1 eval2
  --     obtain ⟨c1_s2, c1_t1, c1_t2⟩ := compileAux_canonical_trace (maxId := maxId) eval1
  --     obtain ⟨c2_s2, c2_t1, c2_t2⟩ := compileAux_canonical_trace (maxId := maxId1) eval2
  --     apply DFG.Canonical.mk (MergedState e1 e2 maxId (c1_s2 ⊕ c2_s2))
  --     · sorry
  --     · apply Relation.ReflTransGen.tail
  --         (b := .empty ↦ ⟨x, maxId2.fst⟩ ↦ ⟨y, maxId2.snd⟩)
  --       · have s1 := op_multi_step_to_merged_left c1_t2 (e1 := e1) (e2 := e2)
  --         have s2 := op_multi_step_to_merged_right (maxId1_eq ▸ c2_t2)
  --         trans (MergedState e1 e2 maxId ((compileAux maxId e1).1.finalState x)) ⊕ (MergedState e1 e2 maxId c2_s2)
  --         · have : MergedState e1 e2 maxId (c1_s2 ⊕ c2_s2) = (MergedState e1 e2 maxId c1_s2) ⊕ (MergedState e1 e2 maxId c2_s2) := by aesop
  --           rw [this]
  --           apply Relation.ReflTransGen.trans_induction_on s1
  --             (P := λ {a b} _ =>
  --               (compileAux maxId (e1.plus e2)).1.dfg.MultiOpStep (a ⊕ MergedState e1 e2 maxId c2_s2) (b ⊕ MergedState e1 e2 maxId c2_s2))
  --           · aesop
  --           · intro a b op_step
  --             match op_step with
  --             | .node ⟨nid, .binOp op ps⟩ h_op h_mem node_step =>
  --               match node_step with
  --               | .binOp h1 h2 =>

  --                 sorry
  --           ·
  --             sorry
  --         · sorry
  --       · apply DFG.OpStep.node
  --           ⟨(compileAux (compileAux maxId e1).2 e2).2, .binOp .plus [((compileAux (compileAux maxId e1).2 e2).2 + 1).fst]⟩
  --         · simp
  --         · simp
  --         · apply Node.Step.subst (.binOp (by aesop) (by aesop))
  --           aesop

  lemma compileAux_canonical_trace {e : Exp} {env : Env} {v : Ty} {maxId : Nid}
    (eval : Eval env e v) : (compileAux maxId e).1.dfg.Canonical maxId (compileAux maxId e).2 ((compileAux maxId e).1.initialState env) ((compileAux maxId e).1.finalState v) := by
    sorry

  theorem compile_value_correct {e : Exp} {env : Env} {v : Ty} (eval : Eval env e v)
    : (compile e).dfg.MultiStep ((compile e).initialState env) ((compile e).finalState v) :=
    (compileAux_canonical_trace eval).DFG.Canonical.to_multi_step

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
        exfalso
        rename_i nid ts
        have : nid.fst = (compile e).ret := by aesop
        have : nid = (compile e).ret.node := (Port.mk.inj this).left
        have := (compile_ret_iff_output _ h_mem).mp this
        simp at this
      | binOp h1 h2 =>
        exfalso
        rename_i _ _ nid _ _
        have : nid.fst ≠ (compile e).ret := by
          intro h
          have := (compile_ret_iff_output _ h_mem).mp (Port.mk.inj h).left
          simp_all
        apply this
        simp only [MarkedDFG.finalState, Nid.fst, compile, ne_eq, ite_eq_right_iff,
          List.cons_ne_self, imp_false, Decidable.not_not] at h1
        exact h1

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
