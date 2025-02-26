import Aesop
import Mathlib.Data.Vector.Basic
import Std.Data.DHashMap.Internal.WF
import Mathlib.Data.List.Sublists

open Mathlib

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
  structure Port where
    node : Nat
    port : Nat
  deriving DecidableEq

  theorem Port.node_ne {p1 p2 : Port} : p1.node ≠ p2.node → p1 ≠ p2 := by
    aesop

  structure Token where
    val : Ty
    tag : Port

  structure BToken where
    val : Ty
    tags : List Port

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
    id : Nat
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
  def State.Disjoint (s1 : State) (s2 : State) : Prop :=
    ∀ p, (s1 p ≠ [] → s2 p = []) ∧ (s2 p ≠ [] → s1 p = [])

  @[simp]
  def BinOp.denote : BinOp → Ty → Ty → Ty
    | plus => HAdd.hAdd

  infixl:100 " ↤ " => State.pop
  infixl:100 " ↦ " => State.push
  infixl:100 " ↦↦ " => State.pushAll
  infixl:100 " ⊕ " => State.union

  inductive Node.Step : Node → State → State → Prop
    | input : (h : s ⟨nid, 0⟩ ≠ [])
      → Node.Step ⟨nid, .input ts⟩ s (s ↤ ⟨nid, 0⟩ ↦↦ ⟨(s ⟨nid, 0⟩).head h, ts⟩)
    | binOp : {op : BinOp} → (h1 : s ⟨nid, 0⟩ ≠ []) → (h2 : s ⟨nid, 1⟩ ≠ [])
      → Node.Step ⟨nid, .binOp op ts⟩ s (s ↤ ⟨nid, 0⟩ ↤ ⟨nid, 1⟩ ↦↦ ⟨op.denote ((s ⟨nid, 0⟩).head h1) ((s ⟨nid, 1⟩).head h2), ts⟩)

  theorem State.union_disjoint_commute {s1 s2 : State} : s1.Disjoint s2 → (s1 ⊕ s2) = s2 ⊕ s1 := by
    intro h
    funext x
    if h_s1 : s1 x = [] then
      simp_all
    else
      simp_all

  theorem State.pop_union_disjoint_commute : s1.Disjoint s2 → s1 p ≠ [] → ((s1 ↤ p) ⊕ s2) = ((s1 ⊕ s2) ↤ p) := by
    aesop

  theorem State.push_nil_union_commutes : s2 p = [] → ((s1 ↦ ⟨val, p⟩) ⊕ s2) = (s1 ⊕ s2) ↦ ⟨val, p⟩ := by
    aesop

  theorem State.pushAll_cons {s : State} : s ↦↦ ⟨x, hd :: tl⟩ = (s ↦ ⟨x, hd⟩) ↦↦ ⟨x, tl⟩ := by
    aesop

  theorem State.pushAll_ne {s : State} (h : p ∈ ps) : (s ↦↦ ⟨x, ps⟩) p ≠ [] := by
    cases ps with
    | nil => contradiction
    | cons hd tl =>
      apply (List.mem_cons.mp h).elim
      · intro h
        apply List.foldl_induction (s ↦ { val := x, tag := hd }) tl (λ x => x p ≠ [])
        <;> aesop
      · intro h
        rw [State.pushAll_cons]
        exact State.pushAll_ne h

  theorem State.pushAll_union_disjoint_commute (h_disj : (s1 ↦↦ ts).Disjoint s2) : ((s1 ↦↦ ts) ⊕ s2) = ((s1 ⊕ s2) ↦↦ ts) := by
    obtain ⟨val, tags⟩ := ts
    have : ∀ p ∈ tags, s2 p = [] := by
      intro p h_mem
      have : (s1 ↦ ⟨val, p⟩) p ≠ [] := by aesop
      apply (h_disj p).left
      exact State.pushAll_ne h_mem
    apply List.foldl_dual_induction _ _ _ _ (λ x1 x2 => (x1 ⊕ s2) = x2) rfl rfl
    · intro agg1 agg2 x h_mem ih
      simp only [List.zip, List.zipWith_same, List.mem_map] at h_mem
      obtain ⟨a, ⟨h_mem_a, h_eq_a⟩⟩ := h_mem
      rw [←h_eq_a]
      simp only
      rw [State.push_nil_union_commutes (this _ h_mem_a)]
      aesop

  theorem Node.Step.disjoint_union_right {node : Node} (step : node.Step s1 s2) (h1 : s1.Disjoint s3) (h2 : s2.Disjoint s3) : node.Step (s1 ⊕ s3) (s2 ⊕ s3) := by
    cases step with
    | @input _ nid ts h =>
      rw [State.pushAll_union_disjoint_commute h2]
      rw [State.pop_union_disjoint_commute h1 h]
      have : s1 ⟨nid, 0⟩ = (s1 ⊕ s3) ⟨nid, 0⟩ := by aesop
      simp_rw [this]
      apply Node.Step.input
    | @binOp _ nid _ _ h_ne1 h_ne2 =>
      rw [State.pushAll_union_disjoint_commute h2]
      have h_pop_disj : (s1 ↤ ⟨nid, 0⟩).Disjoint s3 := by aesop
      have h_pop_ne_nil : (s1 ↤ ⟨nid, 0⟩) ⟨nid, 1⟩ ≠ [] := by aesop
      rw [State.pop_union_disjoint_commute h_pop_disj h_pop_ne_nil]
      rw [State.pop_union_disjoint_commute h1 h_ne1]
      have : s1 ⟨nid, 0⟩ = (s1 ⊕ s3) ⟨nid, 0⟩ := by aesop
      simp_rw [this]
      have : s1 ⟨nid, 1⟩ = (s1 ⊕ s3) ⟨nid, 1⟩ := by
        simp only [State.union, List.self_eq_append_right]
        exact (h1 _).left h_ne2
      simp_rw [this]
      apply Node.Step.binOp

  theorem Node.Step.disjoint_union_left {node : Node} (step : node.Step s1 s2) (h1 : s1.Disjoint s3) (h2 : s2.Disjoint s3) : node.Step (s3 ⊕ s1) (s3 ⊕ s2) := by
    rw [←State.union_disjoint_commute h1]
    rw [←State.union_disjoint_commute h2]
    exact step.disjoint_union_right h1 h2

  inductive DFG.Step : DFG → State → State → Prop
    | node : (node : Node) → node ∈ dfg → node.Step s1 s2 → DFG.Step dfg s1 s2

  abbrev DFG.MultiStep (dfg : DFG) : State → State → Prop :=
    Relation.ReflTransGen dfg.Step

  abbrev NodePredicate := Node → Prop

  abbrev StatePredicate := State → Prop

  structure Predicate where
    node : NodePredicate
    state : StatePredicate

  -- @[simp]
  -- def Predicate.And (p1 p2 : Predicate) : Predicate :=
  --   ⟨
  --     λ node => p1.node node ∧ p2.node node,
  --     λ state => p1.state state ∧ p2.state state
  --   ⟩
  -- infixr:100 " ∧ " => Predicate.And

  -- def Predicate.And.node_left {p1 p2 : Predicate} {n : Node} (h : (p1 ∧ p2).node n) : p1.node n := by
  --   simp_all

  -- def Predicate.And.state_left {p1 p2 : Predicate} {s : State} (h : (p1 ∧ p2).state s) : p1.state s := by
  --   simp_all

  -- def Predicate.And.node_right {p1 p2 : Predicate} {n : Node} (h : (p1 ∧ p2).node n) : p2.node n := by
  --   simp_all

  -- def Predicate.And.state_right {p1 p2 : Predicate} {s : State} (h : (p1 ∧ p2).state s) : p2.state s := by
  --   simp_all

  -- structure Predicate.Subtype (S P : Predicate) where
  --   node : ∀ node, S.node node → P.node node
  --   state : ∀ state, S.state state → P.state state
  -- infix:90 " ⊑ " => Predicate.Subtype

  -- def Predicate.And_subtype_left (p1 p2 : Predicate) : (p1 ∧ p2) ⊑ p1 :=
  --   ⟨
  --     λ node h => by simp_all,
  --     λ state h => by simp_all
  --   ⟩

  -- def Predicate.And_subtype_right (p1 p2 : Predicate) : (p1 ∧ p2) ⊑ p2 :=
  --   ⟨
  --     λ node h => by simp_all,
  --     λ state h => by simp_all
  --   ⟩

  inductive DFG.PredicatedMultiStep : DFG → Predicate → State → State → Prop
    | refl : P.state s → DFG.PredicatedMultiStep dfg P s s
    | head : (node : Node) → node ∈ dfg
              → node.Step s1 s2
              → P.node node → P.state s1 → P.state s2
              → DFG.PredicatedMultiStep dfg P s2 s3
              → DFG.PredicatedMultiStep dfg P s1 s3

  theorem DFG.PredicatedMultiStep.to_MultiStep (step : DFG.PredicatedMultiStep dfg P s1 s2) : DFG.MultiStep dfg s1 s2 := by
    induction step with
    | refl => rfl
    | head node h_mem hd _ _ _ _ ih =>
      exact Relation.ReflTransGen.head (.node node h_mem hd) ih

  theorem DFG.PredicatedMultiStep.single {dfg : DFG} {node : Node} (h_mem : node ∈ dfg) (h_node : P.node node)
    (h_s1 : P.state s1) (h_s2 : P.state s2) (step : node.Step s1 s2) : dfg.PredicatedMultiStep P s1 s2 :=
    .head node h_mem step h_node h_s1 h_s2 (.refl h_s2)

  theorem DFG.PredicatedMultiStep.append_node (step : DFG.PredicatedMultiStep dfg P s1 s2) (node : Node) : DFG.PredicatedMultiStep (node :: dfg) P s1 s2 := by
    induction step with
    | refl h => exact DFG.PredicatedMultiStep.refl h
    | head node h_mem =>
      apply DFG.PredicatedMultiStep.head node (List.mem_cons_of_mem _ h_mem)
      <;> assumption

  @[trans]
  theorem DFG.PredicatedMultiStep.trans {dfg : DFG} (step1 : dfg.PredicatedMultiStep P s1 s2) (step2 : dfg.PredicatedMultiStep P s2 s3)
    : dfg.PredicatedMultiStep P s1 s3 := by
    induction step1 with
    | refl => exact step2
    | head node h_mem hd h_node h_s1 h_s2 _ ih =>
      exact .head node h_mem hd h_node h_s1 h_s2 (ih step2)

  @[simp]
  def NidRange (low high : Nat) : StatePredicate :=
    λ s => ∀ port, port.node < low ∨ port.node ≥ high → s port = []

  @[simp]
  def NidRangePlusPort (low high : Nat) (p : Port) : StatePredicate :=
    λ s => ∀ port, (port.node < low ∨ port.node ≥ high) ∧ port ≠ p → s port = []

  @[simp]
  def NodePredicate.IsInput : NodePredicate :=
   (·.isInput = true)

  @[simp]
  def NodePredicate.IsOp : NodePredicate :=
   (·.isOp = true)

  macro "nid_range_by_omega " : tactic =>
    `(tactic|
     (intro port h
      simp only [State.union, List.append_eq_nil]
      apply And.intro <;> (apply_assumption; omega)))

  macro "nid_range_state_disjoint " : tactic =>
    `(tactic|
     (intro p
      apply And.intro
      <;> (intro h
           apply_assumption
           by_contra
           apply h
           apply_assumption
           omega)))

  theorem DFG.PredicatedMultiStep.merge_disjoint_nid_ranges {dfg : DFG}
    (step1 : dfg.PredicatedMultiStep ⟨P_node, NidRange low1 high1⟩ s1 s2)
    (step2 : dfg.PredicatedMultiStep ⟨P_node, NidRange low2 high2⟩ s3 s4)
    (h_lt1 : low1 < high1)
    (h_lt2 : low2 < high2)
    (h_le : high1 ≤ low2)
    : dfg.PredicatedMultiStep ⟨P_node, NidRange low1 high2⟩ (s1 ⊕ s3) (s2 ⊕ s4) := by
    trans (s2 ⊕ s3)
    · generalize h_P : (⟨P_node, NidRange low1 high1⟩ : Predicate) = range at *
      have s3_range : (NidRange low2 high2) s3 := by cases step2 <;> simp_all
      induction step1 with
      | refl h =>
        simp_rw [←h_P] at *
        apply DFG.PredicatedMultiStep.refl
        intro port h_nid
        simp only [State.union, List.append_eq_nil]
        apply And.intro
        <;> (apply h_nid.elim <;> (intro; apply_assumption; omega))
      | head node h_mem hd h_node h_s1 h_s2 _ ih =>
        simp_rw [←h_P] at *
        apply DFG.PredicatedMultiStep.head node h_mem _ h_node _ _ (ih trivial)
        rename_i s1 s2 _ _ _
        · apply hd.disjoint_union_right
          <;> nid_range_state_disjoint
        all_goals nid_range_by_omega
    · generalize h_P : (⟨P_node, NidRange low2 high2⟩ : Predicate) = range at *
      have s2_range : (NidRange low1 high1) s2 := by
        generalize h : (⟨P_node, NidRange low1 high1⟩ : Predicate) = range at *
        induction step1 <;> aesop
      induction step2 with
      | refl h =>
        apply DFG.PredicatedMultiStep.refl
        intro port h_nid
        simp only [State.union, List.append_eq_nil]
        apply And.intro
        · apply h_nid.elim <;> (intro; apply s2_range; omega)
        · apply h_nid.elim <;> (intro; rw [←h_P] at h; apply h; omega)
      | head node h_mem hd h_node h_s1 h_s2 _ ih =>
        simp_rw [←h_P] at *
        apply DFG.PredicatedMultiStep.head node h_mem _ h_node _ _ (ih trivial)
        rename_i s1 s3 _ _ _
        · apply hd.disjoint_union_left
          <;> nid_range_state_disjoint
        all_goals nid_range_by_omega

  macro "nid_range_plus_port_by_omega " : tactic =>
    `(tactic|
     (intro port h
      simp only [State.union, List.append_eq_nil]
      apply And.intro
      <;> (apply_assumption
           apply And.intro
           · omega
           · apply Port.node_ne
             simp only
             omega)))

  macro "nid_range_plus_port_state_disjoint " extraNid:term : tactic =>
    `(tactic|
     (intro p
      apply And.intro
      <;> (intro h
           apply_assumption
           apply And.intro
           · by_contra
             apply h
             apply_assumption
             apply And.intro
             · omega
             · apply Port.node_ne
               simp only
               omega
           · by_contra h_p
             apply h
             apply_assumption
             have : p.node = $extraNid := by simp_all
             apply And.intro
             · omega
             · by_contra
               simp_all)))

  macro "nid_range_plus_port_merge_disjoint_refl " h:term : tactic =>
    `(tactic|
     (simp_rw [←$h] at *
      apply DFG.PredicatedMultiStep.refl
      intro port h_nid
      simp only [State.union, List.append_eq_nil]
      apply And.intro
      <;> (apply_assumption
           apply h_nid.elim
           <;> (intro
                apply And.intro
                · omega
                · apply Port.node_ne
                  simp only
                  omega))))

  theorem DFG.PredicatedMultiStep.merge_disjoint_nid_ranges_plus_port {dfg : DFG}
    (step1 : dfg.PredicatedMultiStep ⟨P_node, NidRangePlusPort low1 high1 ⟨extraNid, pid1⟩⟩ s1 s2)
    (step2 : dfg.PredicatedMultiStep ⟨P_node, NidRangePlusPort low2 high2 ⟨extraNid, pid2⟩⟩ s3 s4)
    (h_lt1 : low1 < high1)
    (h_lt2 : low2 < high2)
    (h_lt3 : high2 ≤ extraNid)
    (h_ne : pid1 ≠ pid2)
    (h_le : high1 ≤ low2)
    : dfg.PredicatedMultiStep ⟨P_node, NidRange low1 (extraNid + 1)⟩ (s1 ⊕ s3) (s2 ⊕ s4) := by
    trans (s2 ⊕ s3)
    · generalize h_P : (⟨P_node, NidRangePlusPort low1 high1 ⟨extraNid, pid1⟩⟩ : Predicate) = range at *
      have s3_range : (NidRangePlusPort low2 high2 ⟨extraNid, pid2⟩) s3 := by
        cases step2 <;> assumption
      induction step1 with
      | refl => nid_range_plus_port_merge_disjoint_refl h_P
      | head node h_mem hd h_node _ _ _ ih  =>
        simp_rw [←h_P] at *
        apply DFG.PredicatedMultiStep.head node h_mem _ h_node _ _ (ih trivial)
        rename_i s1 s2 _ _ _
        · apply hd.disjoint_union_right
          <;> nid_range_plus_port_state_disjoint extraNid
        all_goals nid_range_plus_port_by_omega
    · generalize h_P : (⟨P_node, NidRangePlusPort low2 high2 ⟨extraNid, pid2⟩⟩ : Predicate) = range at *
      have s2_range : (NidRangePlusPort low1 high1 ⟨extraNid, pid1⟩) s2 := by
        generalize h : (⟨P_node, NidRangePlusPort low1 high1 ⟨extraNid, pid1⟩⟩ : Predicate) = range at *
        induction step1 <;> aesop
      induction step2 with
      | refl h => nid_range_plus_port_merge_disjoint_refl h_P
      | head node h_mem hd h_node _ _ _ ih =>
        simp_rw [←h_P] at *
        apply DFG.PredicatedMultiStep.head node h_mem _ h_node _ _ (ih trivial)
        rename_i s1 s2 _ _ _
        · apply hd.disjoint_union_left
          <;> nid_range_plus_port_state_disjoint extraNid
        all_goals nid_range_plus_port_by_omega

  theorem State.irrelevant_pop {s1 s2 : State} {p1 p2 : Port} (h_ne : p1 ≠ p2) (h_eq : s1 p1 = s2 p1) : s1 p1 = (s2 ↤ p2) p1 := by
    aesop

  theorem State.irrelevant_push {s1 s2 : State} {p1 p2 : Port} (h_ne : p1 ≠ p2) (h_eq : s1 p1 = s2 p1) : s1 p1 = (s2 ↦ ⟨val, p2⟩) p1 := by
    aesop

  theorem Node.Step.subst_right {node : Node} {s1 s2 s3 : State}
    (step : node.Step s1 s2) (heq : s2 = s3)
    : node.Step s1 s3 :=
    heq ▸ step

  inductive DFG.Canonical : DFG → (low high : Nat) → State → State → Prop
    | mk : (s2 : State)
      → dfg.PredicatedMultiStep ⟨NodePredicate.IsInput, NidRange low high⟩ s1 s2
      → dfg.PredicatedMultiStep ⟨NodePredicate.IsOp, NidRange low high⟩ s2 s3
      → DFG.Canonical dfg low high s1 s3

  -- theorem predicate_transfer {P1 P2 : Predicate} (h : ∀ node, ∀ a b, P1 node a b → P2 node a b)
  --   (step : Relation.ReflTransGen (PredicatedStep P1) s1 s2) : Relation.ReflTransGen (PredicatedStep P2) s1 s2 := by
  --   induction step with
  --   | refl => rfl
  --   | tail hd tl ih =>
  --     apply Relation.ReflTransGen.tail ih
  --     obtain ⟨node, p, step⟩ := tl
  --     exact PredicatedStep.node node (h _ _ _ p) step

  -- theorem PredicatedStep.subst_right (s : PredicatedStep P s1 s2) (heq : s2 = s3) : PredicatedStep P s1 s3 :=
  --   heq ▸ s

  theorem DFG.Canonical.to_MultiStep {dfg : DFG} {s1 s3 : State} : dfg.Canonical low high s1 s3 → dfg.MultiStep s1 s3
  | .mk s2 t1 t2 => by
    trans s2
    · exact PredicatedMultiStep.to_MultiStep t1
    · exact PredicatedMultiStep.to_MultiStep t2

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
  def mergeTwo (g1 g2 : MarkedDFG) (nid : Nat)
    : DFG × VarMap :=
    let (dfg, vars) := mergeVars g1 g2
    -- Update links to the original output nodes
    let dfg := dfg.map (Node.updateReturn g1.ret ⟨nid, 0⟩)
    let dfg := dfg.map (Node.updateReturn g2.ret ⟨nid, 1⟩)
    -- Remove all output nodes
    let dfg := dfg.filter (λ node => match node.op with | .output => false | _ => true)
    (dfg, vars)

  @[simp]
  def compileAux (maxNid : Nat) : Exp → MarkedDFG × Nat
    | .var s =>
      let inpId := maxNid
      let outId := maxNid + 1
      let dfg := [⟨inpId, .input [⟨outId, 0⟩]⟩, ⟨outId, .output⟩]
      let vars := [(s, ⟨maxNid, 0⟩)]
      (⟨dfg, vars, ⟨outId, 0⟩⟩, maxNid + 2)
    | .plus e1 e2 =>
      let (e1, maxNid) := compileAux maxNid e1
      let (e2, maxNid) := compileAux maxNid e2
      let plusId := maxNid
      let outId := maxNid + 1
      let (dfg, vars) := mergeTwo e1 e2 plusId
      let dfg := ⟨plusId, .binOp .plus [⟨outId, 0⟩]⟩ :: ⟨outId, .output⟩ :: dfg
      (⟨dfg, vars, ⟨outId, 0⟩⟩, maxNid + 2)

  @[simp]
  def compile (e : Exp) : MarkedDFG :=
    (compileAux 0 e).fst

  @[simp]
  def VarMap.initialState (vars : VarMap) (env : Env) : State :=
    vars.foldl (λ s (name, port) => s ↦ ⟨env name, port⟩) .empty

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

  abbrev dfg_id_lt_max (dfg : DFG) (max : Nat) :=
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

  lemma merge_id_lt_max {dfg1 dfg2 : MarkedDFG} {nid : Nat}
    (maxId : Nat) (h1 : dfg_id_lt_max dfg1.dfg maxId) (h2: dfg_id_lt_max dfg2.dfg maxId)
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

  lemma compile_maxId_lt {e : Exp} {initialMax : Nat}
    : initialMax < (compileAux initialMax e).snd := by
    cases e <;> simp [compileAux]
    rename_i e1 e2
    trans (compileAux initialMax e1).2
    exact compile_maxId_lt
    trans (compileAux (compileAux initialMax e1).2 e2).2
    exact compile_maxId_lt
    simp

  lemma compileAux_max_lt_ret {e : Exp} {maxId : Nat}
    : maxId < (compileAux maxId e).1.ret.node := by
    cases e with
    | var => simp
    | plus e1 e2 =>
      simp
      have h1 := @compile_maxId_lt e1 maxId
      have h2 : (compileAux maxId e1).2 < (compileAux (compileAux maxId e1).2 e2).2 := compile_maxId_lt
      have := Nat.lt_trans h1 h2
      exact Nat.lt_succ_of_lt this

  lemma compileAux_ret_lt_newMax {e : Exp} {maxId : Nat}
    : (compileAux maxId e).1.ret.node < (compileAux maxId e).2 := by
    cases e <;> simp

  lemma compile_id_lt_max {e : Exp} {initialMax : Nat}
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
    simp only [mergeTwo, List.map_map, List.mem_filter, List.mem_map,
      Function.comp_apply] at h_mem
    obtain ⟨⟨a, ⟨h_mem, h_eq⟩⟩, _⟩ := h_mem
    suffices h : maxId ≤ a.id by aesop
    apply (mergeVars_id_eq h_mem).elim
    <;> simp_all

  lemma compileAux_maxId_le_id {e : Exp} {maxId : Nat}
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

  lemma merge_id_lt_max_compileAux {e1 e2 : Exp} {maxId : Nat}
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

  lemma merge_no_output {dfg1 dfg2 : MarkedDFG} {nid : Nat}
    : dfg1.ret_if_output → dfg2.ret_if_output
      → ∀ node ∈ (mergeTwo dfg1 dfg2 nid).fst, node.op.isOutput = false := by
    aesop

  theorem Nat.succ_lt_false {x : Nat} : x + 1 < x → False := by simp
  theorem Nid.succ_lt_false {x : Nat} : x + 1 < x → False := Nat.succ_lt_false

  lemma compileAux_ret_if_output {e : Exp} {maxId : Nat}
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

  lemma compileAux_output_if_ret {e : Exp} {maxId : Nat}
    : (compileAux maxId e).1.output_if_ret := by
    intro node h_mem h_ret
    cases h_cases : e with
    | var _ =>
      simp_all only [compile, compileAux, zero_add, List.mem_cons,
        List.mem_singleton]
      cases h_mem <;> simp_all
    | plus e1 e2 =>
      simp_all only [compile, compileAux, List.mem_cons, NodeOp.isOutput]
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

  lemma compileAux_ret_iff_output {e : Exp} {maxId : Nat} : (compileAux maxId e).1.ret_iff_output :=
    λ node h_mem => Iff.intro (compileAux_output_if_ret node h_mem) (compileAux_ret_if_output node h_mem)

  lemma compile_ret_iff_output {e : Exp} : (compile e).ret_iff_output :=
    compileAux_ret_iff_output

  lemma compile_ret_is_fst {nid : Nat} {e : Exp}
    : (compile e).ret.node = nid → (compile e).ret = ⟨nid, 0⟩ := by
    simp only [compile]
    cases e <;> aesop

  lemma mergeVars_vars_id_lt {dfg1 dfg2 : MarkedDFG} {maxId : Nat}
    (h1 : ∀ var ∈ dfg1.vars, var.2.node < maxId)
    (h2 : ∀ var ∈ dfg2.vars, var.2.node < maxId)
    : ∀ var ∈ (mergeVars dfg1 dfg2).2, var.2.node < maxId := by
    intro var h_mem
    apply List.foldl_induction (f := mergeVarsAux dfg1) (dfg1.dfg ++ dfg2.dfg, dfg1.vars) dfg2.vars
      (λ x => ∀ var ∈ x.2, var.2.node < maxId) _ _ _ h_mem
    <;> aesop

  lemma merge_vars_id_lt {dfg1 dfg2 : MarkedDFG} {maxId : Nat}
    (h1 : ∀ var ∈ dfg1.vars, var.2.node < maxId)
    (h2 : ∀ var ∈ dfg2.vars, var.2.node < maxId)
    : ∀ var ∈ (mergeTwo dfg1 dfg2 maxId).2, var.2.node < maxId :=
    mergeVars_vars_id_lt h1 h2

  lemma compile_vars_id_ge_max {e : Exp} {maxId : Nat}
    : ∀ var ∈ (compileAux maxId e).1.vars, maxId ≤ var.2.node := by
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      intro var h_mem
      apply List.foldl_induction (f := mergeVarsAux (compileAux maxId e1).1)
        ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars)
        (compileAux (compileAux maxId e1).2 e2).1.vars
        (λ x => ∀ var ∈ x.2, maxId ≤ var.2.node) _ _ _ h_mem
      · intro var h_mem
        exact compile_vars_id_ge_max var h_mem
      · intro agg x h_mem_x ih var h_mem_var
        simp only [mergeVarsAux] at h_mem_var
        split at h_mem_var
        · split at h_mem_var
          · exact ih var h_mem_var
          · suffices maxId ≤ x.2.node by aesop
            simp at h_mem_x
            trans (compileAux maxId e1).2
            · exact Nat.le_of_lt compile_maxId_lt
            · exact compile_vars_id_ge_max x h_mem_x
        · aesop

  lemma compile_vars_id_lt_newMax {e : Exp} {maxId : Nat}
    : ∀ var ∈ (compileAux maxId e).1.vars, var.2.node < (compileAux maxId e).2 := by
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      intro var h_mem
      trans (compileAux (compileAux maxId e1).2 e2).2
      · apply mergeVars_vars_id_lt _ _ var h_mem
        · intro var h_mem
          trans (compileAux maxId e1).2
          · exact compile_vars_id_lt_newMax var h_mem
          · exact compile_maxId_lt
        · exact compile_vars_id_lt_newMax
      · simp

  lemma initial_final_eq_false {e : Exp} {maxId : Nat} {env : Env} {v : Ty}
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
      let ret : Port := ⟨((compileAux (compileAux maxId e1).2 e2).2 + 1), 0⟩
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
          · exact compile_vars_id_lt_newMax var h_mem
          · exact compile_maxId_lt
        · intro var h_mem
          exact compile_vars_id_lt_newMax var h_mem

  @[simp]
  def mergedState (dfg1 dfg2 : MarkedDFG) (nid : Nat) (s : State) : State :=
    λ t =>
      if t = ⟨nid, 0⟩ then
        s dfg1.ret
      else if t = ⟨nid, 1⟩ then
        s dfg2.ret
      else if t = dfg1.ret ∨ t = dfg2.ret then
        []
      else
        s t

  theorem mergedState_eq {dfg1 dfg2 : MarkedDFG} {nid : Nat} {s : State} {p : Port}
    (h_ne_nid : p.node ≠ nid) (h_ne_ret : ¬(p = dfg1.ret ∨ p = dfg2.ret))
    : mergedState dfg1 dfg2 nid s p = s p := by
    aesop

  theorem mergedState_pop_assoc {dfg1 dfg2 : MarkedDFG} {nid : Nat} {s : State} {p : Port}
    (h_ne_nid : p.node ≠ nid) (h_ne_ret : ¬(p = dfg1.ret ∨ p = dfg2.ret))
    : mergedState dfg1 dfg2 nid s ↤ p = mergedState dfg1 dfg2 nid (s ↤ p) := by
    aesop

  theorem mergedState_push_assoc {dfg1 dfg2 : MarkedDFG} {nid : Nat} {s : State} {v : Ty} {p : Port}
    (h_ne_nid : p.node ≠ nid) (h_ret_ne : dfg1.ret ≠ dfg2.ret)
    : mergedState dfg1 dfg2 nid s ↦ ⟨v, if p = dfg1.ret then ⟨nid, 0⟩ else if p = dfg2.ret then ⟨nid, 1⟩ else p⟩ = mergedState dfg1 dfg2 nid (s ↦ ⟨v, p⟩) := by
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

  theorem mergedState_pushAll_assoc {dfg1 dfg2 : MarkedDFG} {nid : Nat} {s : State} {v : Ty} {ps : List Port}
    (h_ne_nid : ∀ p ∈ ps, p.node ≠ nid) (h_ret_ne : dfg1.ret ≠ dfg2.ret)
    : mergedState dfg1 dfg2 nid s ↦↦
        ⟨v, ps.map λ p => if p = dfg1.ret then ⟨nid, 0⟩ else if p = dfg2.ret then ⟨nid, 1⟩ else p⟩ =
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

  abbrev MergeTwo (e1 e2 : Exp) (maxId : Nat) : DFG × VarMap :=
    mergeTwo (compileAux maxId e1).1 (compileAux (compileAux maxId e1).2 e2).1
      (compileAux (compileAux maxId e1).2 e2).2

  abbrev MergedState (e1 e2 : Exp) (maxId : Nat) (s : State) : State :=
    mergedState (compileAux maxId e1).1 (compileAux (compileAux maxId e1).2 e2).1 (compileAux (compileAux maxId e1).2 e2).2 s

  theorem MergedState_pop_assoc {e1 e2 : Exp} {maxId: Nat} {s : State} {p : Port}
    (h_ne_nid : p.node ≠ (compileAux (compileAux maxId e1).2 e2).2)
    (h_ne_ret : ¬(p = (compileAux maxId e1).1.ret ∨ p = (compileAux (compileAux maxId e1).2 e2).1.ret))
    : MergedState e1 e2 maxId s ↤ p = MergedState e1 e2 maxId (s ↤ p) := by
    aesop

  theorem MergedState_pushAll_assoc {e1 e2 : Exp} {maxId: Nat} {s : State} {v : Ty} {ps : List Port}
    (h_ne_nid : ∀ p ∈ ps, p.node ≠ (compileAux (compileAux maxId e1).2 e2).2)
    : MergedState e1 e2 maxId s ↦↦
        ⟨v, ps.map λ p => if p = (compileAux maxId e1).1.ret then
                            ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩
                          else if p = (compileAux (compileAux maxId e1).2 e2).1.ret then
                            ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩
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

  abbrev CompileNodeEq (e : Exp) (maxId : Nat) : Prop :=
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

  lemma compile_seq_node_disj (e1 e2 : Exp) (maxId : Nat)
    : ∀ node1 ∈ (compileAux maxId e1).1.dfg, ∀ node2 ∈ (compileAux (compileAux maxId e1).2 e2).1.dfg, node1.id ≠ node2.id := by
    intro node1 h_mem1 node2 h_mem2
    have e1_lt := @compile_id_lt_max e1 maxId
    have e2_gt := @compileAux_maxId_le_id e2 (compileAux maxId e1).2
    suffices h : node1.id < node2.id from Nat.ne_of_lt h
    apply Nat.lt_of_lt_of_le
    · exact compile_id_lt_max node1 h_mem1
    · exact compileAux_maxId_le_id node2 h_mem2

  lemma compile_binop_maxId_le_consumer {e : Exp} {maxId : Nat}
    (h : ⟨nid, .binOp op ps⟩ ∈ (compileAux maxId e).1.dfg) : ∀ p ∈ ps, maxId ≤ p.node := by
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      simp only [compileAux, mergeTwo, List.map_map, List.mem_cons, Node.mk.injEq,
        NodeOp.binOp.injEq, true_and, reduceCtorEq, and_false, List.mem_filter, List.mem_map,
        Function.comp_apply, and_true, false_or] at h
      apply h.elim
      · intro h
        intro p h_mem
        cases h.right
        rw [List.mem_singleton.mp h_mem]
        apply Nat.le_of_lt
        trans (compileAux (compileAux maxId e1).2 e2).2
        · trans (compileAux maxId e1).2
          <;> exact compile_maxId_lt
        · simp
      · intro h
        obtain ⟨a, ⟨h_mem_a, h_node⟩⟩ := h
        simp only [Node.updateReturn, Node.mk.injEq] at h_node
        obtain ⟨h_id, h_eq⟩ := h_node
        cases h_case : a.op
        · simp [h_case] at h_eq
        · simp [h_case] at h_eq
        · simp only [h_case, List.map_map, NodeOp.binOp.injEq, true_and] at h_eq
          simp [mergeVars] at h_mem_a
          rw [←h_eq]
          intro p h_mem_p
          obtain ⟨pp, ⟨h_mem_pp, h_pp_eq⟩⟩ := List.mem_map.mp h_mem_p
          rw [←h_pp_eq]
          simp only [Function.comp_apply]
          split
          · split
            <;> (trans (compileAux maxId e1).2 <;> exact Nat.le_of_lt compile_maxId_lt)
          · split
            · trans (compileAux maxId e1).2 <;> exact Nat.le_of_lt compile_maxId_lt
            · apply List.foldl_induction
                      ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars)
                      (compileAux (compileAux maxId e1).2 e2).1.vars
                      (λ x => ∀ node ∈ x.1, ∀ op, ∀ ps, node.op = .binOp op ps → ∀ p ∈ ps, maxId ≤ p.node)
                      _ _ _ h_mem_a _ _ h_case _ h_mem_pp
              · intro node h_mem_node op ps h_op_eq p h_mem_p
                apply (List.mem_append.mp h_mem_node).elim
                · intro h
                  cases node
                  simp only at h_op_eq
                  rw [h_op_eq] at h
                  exact compile_binop_maxId_le_consumer h p h_mem_p
                · intro h
                  cases node
                  simp only at h_op_eq
                  rw [h_op_eq] at h
                  trans (compileAux maxId e1).2
                  · exact Nat.le_of_lt compile_maxId_lt
                  · exact compile_binop_maxId_le_consumer h p h_mem_p
              · intro agg x h_mem_x ih node h_mem_node
                simp only [mergeVarsAux, ne_eq, decide_not, Prod.mk.eta] at h_mem_node
                split at h_mem_node
                · split at h_mem_node
                  · simp only [List.mem_map, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
                    decide_eq_false_iff_not] at h_mem_node
                    obtain ⟨a, ⟨⟨h_mem_a, h_ne⟩, h_node_eq⟩⟩ := h_mem_node
                    split at h_node_eq
                    · split at h_node_eq
                      · intro _ _ h_op_eq
                        cases node
                        rw [←h_node_eq] at h_op_eq
                        contradiction
                      · rw [h_node_eq] at h_mem_a
                        exact ih node h_mem_a
                    · rw [h_node_eq] at h_mem_a
                      exact ih node h_mem_a
                  · exact ih node h_mem_node
                · exact ih node h_mem_node

  lemma compile_binop_consumer_lt_max {e : Exp} {maxId : Nat}
    (h : ⟨nid, .binOp op ps⟩ ∈ (compileAux maxId e).1.dfg) : ∀ p ∈ ps, p.node < (compileAux maxId e).2 := by
    cases e with
    | var _ => aesop
    | plus e1 e2 =>
      simp only [compileAux,  mergeTwo, List.map_map, List.mem_cons, Node.mk.injEq,
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
  lemma node_eq_mergeVars {e : Exp} {maxId : Nat} {dfgVars : DFG × VarMap}
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

  lemma compile_node_eq (e : Exp) (maxId : Nat) : CompileNodeEq e maxId := by
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

  lemma plus_maxId_lt : maxId < ((compileAux (compileAux maxId e1).2 e2).2 + 2) := by
    trans (compileAux maxId e1).2
    · exact compile_maxId_lt
    · trans (compileAux (compileAux maxId e1).2 e2).2
      · exact compile_maxId_lt
      · simp

  theorem compile_plus_port_lt_false {P : Prop} {portId : Nat} {port : Port}
    (h_lt : port.node < maxId)
    (h_eq : port = ⟨(compileAux (compileAux maxId e1).2 e2).2, portId⟩)
    : P := by
    suffices h : maxId < (compileAux (compileAux maxId e1).2 e2).2 by
      have := (Port.mk.inj h_eq).left
      have := Nat.lt_trans h_lt h
      simp_all
    trans (compileAux maxId e1).2
    <;> exact compile_maxId_lt

  theorem compile_port_lt_maxId_ret_false {P : Prop} {port : Port}
    (h_lt : port.node < maxId) (h_eq : port = (compileAux maxId e1).1.ret)
    : P := by
    have := @compileAux_max_lt_ret e1 maxId
    have := Nat.lt_trans h_lt this
    have := (Port.mk.inj h_eq).left
    simp_all

  theorem compile_plus_port_lt_maxId_ret_false {P : Prop} {port : Port}
    (h_lt : port.node < maxId) (h_eq : port = (compileAux (compileAux maxId e1).2 e2).1.ret)
    : P := by
    have := @compileAux_max_lt_ret e2 (compileAux maxId e1).2
    have : port.node < (compileAux (compileAux maxId e1).2 e2).1.ret.node := by
      trans maxId
      · exact h_lt
      · trans (compileAux maxId e1).2
        · exact compile_maxId_lt
        · exact this
    have := (Port.mk.inj h_eq).left
    simp_all

  -- theorem op_step_to_merged_left {e1 e2 : Exp} {maxId : Nat} {s1 s2 : State}
  --   (s : PredicatedStep (DFGMem (compileAux maxId e1).1.dfg ∧ NidContained maxId (compileAux maxId e1).2 compile_maxId_lt ∧ Predicate.isOp) s1 s2)
  --   : PredicatedStep (DFGMem (MergeTwo e1 e2 maxId).1 ∧ NidContainedWithExtra maxId (compileAux maxId e1).2 ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩ compile_maxId_lt ∧ Predicate.isOp)
  --       (MergedState e1 e2 maxId s1) (MergedState e1 e2 maxId s2) :=
  --   match s with
  --   | .node ⟨nid, .binOp op ts⟩ ⟨h_mem, ⟨h_nid, _⟩⟩ s =>
  --     match s with
  --     | .binOp h1 h2 => by
  --       let newRet := (compileAux (compileAux maxId e1).2 e2).2
  --       let newTs :=
  --         (ts.map (λ t => if t = (compileAux maxId e1).1.ret then ⟨newRet, 0⟩ else t)).map
  --           (λ t => if t = (compileAux (compileAux maxId e1).2 e2).1.ret then ⟨newRet, 1⟩ else t)
  --       have h_mem' : ⟨nid, .binOp op newTs⟩ ∈ (MergeTwo e1 e2 maxId).1 := by
  --         apply List.mem_filter.mpr
  --         apply And.intro
  --         · apply List.mem_map.mpr
  --           exists ⟨nid, .binOp op (ts.map (λ t => if t = (compileAux maxId e1).1.ret then ⟨newRet, 0⟩ else t))⟩
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
  --             · aesop
  --           · simp only [Node.updateReturn]
  --             aesop
  --         · simp
  --       have h_nid_ne_ret : nid ≠ (compileAux (compileAux maxId e1).2 e2).2 := by
  --         have h1 : nid < (compileAux maxId e1).2 := compile_id_lt_max _ h_mem
  --         have h2 : (compileAux maxId e1).2 < (compileAux (compileAux maxId e1).2 e2).2 := compile_maxId_lt
  --         have := Nat.lt_trans h1 h2
  --         intro heq
  --         apply (lt_self_iff_false nid).mp
  --         rw [←heq] at this
  --         exact this
  --       have h_fst_ne_ret : ¬(⟨nid, 0⟩ = (compileAux maxId e1).1.ret ∨ ⟨nid, 0⟩ = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
  --         simp only [not_or]
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
  --       have h_snd_ne_ret : ¬(⟨nid, 1⟩ = (compileAux maxId e1).1.ret ∨ ⟨nid, 1⟩ = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
  --         simp only [not_or]
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
  --       have h_fst_eq : MergedState e1 e2 maxId s1 ⟨nid, 0⟩ = s1 ⟨nid, 0⟩ := mergedState_eq h_nid_ne_ret h_fst_ne_ret
  --       have h_snd_eq : MergedState e1 e2 maxId s1 ⟨nid, 1⟩ = s1 ⟨nid, 1⟩ := mergedState_eq h_nid_ne_ret h_snd_ne_ret
  --       apply PredicatedStep.subst_right (PredicatedStep.node ⟨nid, .binOp op newTs⟩ _ (.binOp (h_fst_eq ▸ h1) (h_snd_eq ▸ h2)))
  --       · simp_rw [h_fst_eq, h_snd_eq]
  --         rw [MergedState_pop_assoc h_nid_ne_ret h_fst_ne_ret]
  --         rw [MergedState_pop_assoc h_nid_ne_ret h_snd_ne_ret]
  --         simp only [newTs, newRet]
  --         rw [←List.comp_map]
  --         have : ((fun t =>
  --                     if t = (compileAux (compileAux maxId e1).2 e2).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩
  --                     else t) ∘
  --                   fun t => if t = (compileAux maxId e1).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩ else t) =
  --                 (fun p =>
  --               if p = (compileAux maxId e1).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩
  --               else
  --                 if p = (compileAux (compileAux maxId e1).2 e2).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩
  --                 else p) := by
  --           funext x
  --           if x = (compileAux maxId e1).1.ret then
  --             simp_all only [ne_eq, mergeTwo, List.map_map, List.mem_filter,
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
  --         apply @MergedState_pushAll_assoc e1 e2 maxId (s1 ↤ ⟨nid, 0⟩ ↤ ⟨nid, 1⟩) (op.denote ((s1 ⟨nid, 0⟩).head h1) ((s1 ⟨nid, 1⟩).head h2)) ts
  --         have h_lt := @compile_maxId_lt e2 (compileAux maxId e1).2
  --         have := compile_binop_consumer_lt_max h_mem
  --         intro p h_mem
  --         have := this p h_mem
  --         have := Nat.lt_trans this h_lt
  --         apply Nat.ne_of_lt this
  --       · apply And.intro
  --         · aesop
  --         · apply And.intro
  --           · intro port h_port
  --             apply Or.elim h_port.left
  --             · intro h_port_node_id
  --               simp only [mergedState]
  --               split
  --               next h => exact compile_plus_port_lt_false h_port_node_id h
  --               next =>
  --                 split
  --                 next h => exact compile_plus_port_lt_false h_port_node_id h
  --                 next =>
  --                   split
  --                   next h =>
  --                     apply Or.elim h
  --                     · intro h
  --                       exact compile_port_lt_maxId_ret_false h_port_node_id h
  --                     · intro h
  --                       exact compile_plus_port_lt_maxId_ret_false h_port_node_id h
  --                   next h =>
  --                     simp only [State.pushAll]
  --                     apply List.foldl_induction (MergedState e1 e2 maxId s1 ↤ ⟨nid, 0⟩ ↤ ⟨nid, 1⟩) newTs (P := λ x => (s1 port = [] ∧ x port = []))
  --                     · sorry
  --                       -- apply State.irrelevant_pop
  --                       -- · intro h
  --                       --   suffices h_le : maxId ≤ nid by
  --                       --     have h_eq := (Port.mk.inj h).left
  --                       --     have h_le : port.node < nid := Nat.lt_of_lt_of_le h_port_node_id h_le
  --                       --     simp_all
  --                       --   exact compileAux_maxId_le_id _ h_mem
  --                       -- · apply State.irrelevant_pop
  --                       --   · intro h
  --                       --     suffices h_le : maxId ≤ nid by
  --                       --       have h_eq := (Port.mk.inj h).left
  --                       --       have h_le : port.node < nid := Nat.lt_of_lt_of_le h_port_node_id h_le
  --                       --       simp_all
  --                       --     exact compileAux_maxId_le_id _ h_mem
  --                       --   · aesop
  --                     · intro agg x h_mem ih
  --                       sorry
  --                       -- apply State.irrelevant_push _ ih
  --                       -- apply Port.node_ne
  --                       -- simp only [List.map_map, List.mem_map, Function.comp_apply, newTs,
  --                       --   newRet] at h_mem
  --                       -- obtain ⟨a, ⟨h_mem_a, h_x⟩⟩ := h_mem
  --                       -- rw [←h_x]
  --                       -- split
  --                       -- next =>
  --                       --   split
  --                       --   <;> (apply Nat.ne_of_lt
  --                       --        trans maxId
  --                       --        · exact h_port_node_id
  --                       --        · trans (compileAux maxId e1).2
  --                       --          <;> exact compile_maxId_lt)
  --                       -- next =>
  --                       --   split
  --                       --   next =>
  --                       --     apply Nat.ne_of_lt
  --                       --     trans maxId
  --                       --     · exact h_port_node_id
  --                       --     · trans (compileAux maxId e1).2
  --                       --       <;> exact compile_maxId_lt
  --                       --   next =>
  --                       --     apply Nat.ne_of_lt
  --                       --     apply Nat.lt_of_lt_of_le
  --                       --     · exact h_port_node_id
  --                       --     · exact compile_binop_maxId_le_consumer h_mem a h_mem_a
  --             · intro h_port_node_id
  --               simp only [mergedState]
  --               split
  --               next h =>
  --                 have := (Port.mk.inj h).left
  --                 subst h
  --                 simp_all only [State.pushAll, BinOp.denote, DFGMem, NidContained, ge_iff_le, Predicate.isOp,
  --                   Node.isOp, mergeTwo, List.map_map, List.mem_filter, List.mem_map, Function.comp_apply, and_true,
  --                   ne_eq, or_true, not_true_eq_false, and_false, newRet, newTs]
  --               next =>
  --                 split
  --                 next h =>
  --                   sorry
  --                   -- apply List.foldl_induction (MergedState e1 e2 maxId s1 ↤ ⟨nid, 0⟩ ↤ ⟨nid, 1⟩) newTs
  --                   --   (λ x => s1 (compileAux (compileAux maxId e1).2 e2).1.ret = x port)
  --                   -- · simp [h, h_nid_ne_ret.symm]
  --                   -- · intro agg x h_mem_x ih
  --                   --   split
  --                   --   next h =>
  --                   --     have := (Port.mk.inj h).left
  --                   --     contradiction
  --                   --   next =>
  --                   --     simp only [List.map_map, List.mem_map, Function.comp_apply, newTs,
  --                   --       newRet] at h_mem_x
  --                   --     obtain ⟨a, ⟨h_mem_a, h_a⟩⟩ := h_mem_x
  --                   --     split at h_a
  --                   --     next =>
  --                   --       split at h_a
  --                   --       next h =>
  --                   --         simp
  --                   --         have := (Port.mk.inj h).left
  --                   --         suffices (compileAux (compileAux maxId e1).2 e2).2 ≠ (compileAux (compileAux maxId e1).2 e2).1.ret.node by contradiction
  --                   --         symm
  --                   --         exact Nat.ne_of_lt compileAux_ret_lt_newMax
  --                   --       next =>
  --                   --         have : port ≠ x := by simp_all
  --                   --         simp only [State.push, this, ↓reduceIte, newRet, newTs]
  --                   --         exact ih
  --                   --     next =>
  --                   --       split at h_a
  --                   --       next h =>
  --                   --         suffices a ≠ (compileAux (compileAux maxId e1).2 e2).1.ret by contradiction
  --                   --         apply Port.node_ne
  --                   --         apply Nat.ne_of_lt
  --                   --         trans (compileAux maxId e1).2
  --                   --         · exact compile_binop_consumer_lt_max h_mem a h_mem_a
  --                   --         · exact compileAux_max_lt_ret
  --                   --       next =>
  --                   --         suffices h_ne : port ≠ x by
  --                   --           simp only [State.push, h_ne, ↓reduceIte, newRet, newTs]
  --                   --           exact ih
  --                   --         apply Port.node_ne
  --                   --         rw [h, ←h_a]
  --                   --         symm
  --                   --         apply Nat.ne_of_lt
  --                   --         trans (compileAux maxId e1).2
  --                   --         · exact compile_binop_consumer_lt_max h_mem a h_mem_a
  --                   --         · exact compile_maxId_lt
  --                 next =>
  --                   split
  --                   next h =>
  --                     apply Or.elim h
  --                     · intro h
  --                       have := @compileAux_ret_lt_newMax e1 maxId
  --                       rw [←(Port.mk.inj h).left] at this
  --                       omega
  --                     · intro h
  --                       sorry
  --                       -- apply List.foldl_induction (MergedState e1 e2 maxId s1 ↤ ⟨nid, 0⟩ ↤ ⟨nid, 1⟩) newTs
  --                       --   (λ x => [] = x port)
  --                       -- · simp_all
  --                       -- · intro agg x h_mem_x ih
  --                       --   suffices h_ne : port ≠ x by
  --                       --     simp only [State.push, h_ne, ↓reduceIte, List.nil_eq, newRet, newTs]
  --                       --     exact ih.symm
  --                       --   simp only [List.map_map, List.mem_map, Function.comp_apply, newTs,
  --                       --     newRet] at h_mem_x
  --                       --   obtain ⟨a, ⟨h_mem_a, h_a⟩⟩ := h_mem_x
  --                       --   split at h_a
  --                       --   next =>
  --                       --     split at h_a
  --                       --     <;> (apply Port.node_ne; rw [h, ←h_a]; exact Nat.ne_of_lt compileAux_ret_lt_newMax)
  --                       --   next =>
  --                       --     split at h_a
  --                       --     next =>
  --                       --       apply Port.node_ne
  --                       --       rw [h, ←h_a]
  --                       --       exact Nat.ne_of_lt compileAux_ret_lt_newMax
  --                       --     next =>
  --                       --       rw [←h_a, h]
  --                       --       symm
  --                       --       apply Port.node_ne
  --                       --       apply Nat.ne_of_lt
  --                       --       trans (compileAux maxId e1).2
  --                       --       · exact compile_binop_consumer_lt_max h_mem a h_mem_a
  --                       --       · exact compileAux_max_lt_ret
  --                   next =>
  --                     simp only [State.pushAll]
  --                     apply List.foldl_induction (MergedState e1 e2 maxId s1 ↤ ⟨nid, 0⟩ ↤ ⟨nid, 1⟩) newTs (P := λ x => (s1 port = [] ∧ x port = []))
  --                     have h_nid_lt : nid < (compileAux maxId e1).2 := compile_id_lt_max _ h_mem
  --                     · sorry
  --                       -- apply State.irrelevant_pop
  --                       -- · apply Port.node_ne
  --                       --   apply Nat.ne_of_gt
  --                       --   apply Nat.lt_of_lt_of_le
  --                       --   · exact h_nid_lt
  --                       --   · exact h_port_node_id
  --                       -- · apply State.irrelevant_pop
  --                       --   · apply Port.node_ne
  --                       --     apply Nat.ne_of_gt
  --                       --     apply Nat.lt_of_lt_of_le
  --                       --     · exact h_nid_lt
  --                       --     · exact h_port_node_id
  --                       --   · aesop
  --                     · intro agg x h_mem_x ih
  --                       sorry
  --                       -- apply State.irrelevant_push
  --                       -- · simp only [List.map_map, List.mem_map, Function.comp_apply, newTs,
  --                       --   newRet] at h_mem_x
  --                       --   obtain ⟨a, ⟨h_mem_a, h_a_eq⟩⟩ := h_mem_x
  --                       --   rw [←h_a_eq]
  --                       --   split
  --                       --   · split <;> assumption
  --                       --   · split
  --                       --     · assumption
  --                       --     · symm
  --                       --       apply Port.node_ne
  --                       --       apply Nat.ne_of_lt
  --                       --       apply Nat.lt_of_lt_of_le
  --                       --       · exact compile_binop_consumer_lt_max h_mem a h_mem_a
  --                       --       · exact h_port_node_id
  --                       -- · exact ih
  --           · simp

  lemma new_op_node_in_MergeTwo_left
    (h_mem : ⟨nid, .binOp op ts⟩ ∈ (compileAux maxId e1).1.dfg)
    : ⟨nid, .binOp op ((ts.map
                        (λ t => if t = (compileAux maxId e1).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩ else t)).map
                        (λ t => if t = (compileAux (compileAux maxId e1).2 e2).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩ else t))⟩
        ∈ (MergeTwo e1 e2 maxId).1 := by
    apply List.mem_filter.mpr
    apply And.intro
    · apply List.mem_map.mpr
      exists ⟨nid, .binOp op (ts.map (λ t => if t = (compileAux maxId e1).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩ else t))⟩
      apply And.intro
      · apply List.mem_map.mpr
        exists ⟨nid, .binOp op ts⟩
        apply And.intro
        · apply (List.foldl_induction
            ((compileAux maxId e1).1.dfg ++ (compileAux (compileAux maxId e1).2 e2).1.dfg, (compileAux maxId e1).1.vars)
            (compileAux (compileAux maxId e1).2 e2).1.vars
            (λ agg => NodeEq agg.1 ∧ ⟨nid, .binOp op ts⟩ ∈ (Prod.fst agg)) _ _).right
          · apply And.intro
            · apply append_node_eq
              · apply compile_node_eq
              · apply compile_node_eq
              · apply compile_seq_node_disj
            · simp_all
          · intro agg x h_mem_x ih
            apply And.intro
            · exact node_eq_mergeVars ih.left
            · simp only [mergeVarsAux]
              split
              next heq =>
                rename_i _ id ts2
                simp
                split
                next =>
                  apply List.mem_map.mpr
                  exists ⟨nid, .binOp op ts⟩
                  apply And.intro
                  · apply List.mem_filter.mpr
                    apply And.intro ih.right
                    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
                    intro h
                    suffices h : (⟨nid, .binOp op ts⟩ : Node) = ⟨nid, .input ts2⟩ by aesop
                    apply ih.left _ ih.right _ _ (by simp)
                    have : nid = id := by have := List.find?_some heq; aesop
                    rw [this]
                    apply List.mem_of_find?_eq_some heq
                  · aesop
                next => aesop
              next => aesop
        · aesop
      · simp only [Node.updateReturn]
    · simp

  macro "port_ne_ret_in_op_step_merge " maxId:term ", " e1:term ", " e2:term ", " op:term ", " ts:term ", " nid:term ", " h_mem:term : tactic =>
    `(tactic|
     (rw [not_or]
      apply And.intro
      · intro heq
        suffices h : $nid = (compileAux $maxId $e1).1.ret.node by
          have := (compileAux_ret_iff_output ⟨$nid, .binOp $op $ts⟩ $h_mem).mp h
          contradiction
        exact (Port.mk.inj heq).left
      · intro heq
        suffices $nid = (compileAux (compileAux $maxId $e1).2 $e2).1.ret.node by
          suffices $nid ≠ (compileAux (compileAux $maxId $e1).2 $e2).1.ret.node  by
            contradiction
          apply Nat.ne_of_lt
          trans
          · exact compile_id_lt_max _ $h_mem
          · exact compileAux_max_lt_ret
        exact (Port.mk.inj heq).left))

  macro "state_pred_in_op_step_merge " maxId:term ", " e1:term ", " e2:term ", " s:term ", " hs:term : tactic =>
    `(tactic|
      (intro port h
       have : $s (compileAux (compileAux $maxId $e1).2 $e2).1.ret = [] :=
         $hs _ (Or.intro_right _ (ge_iff_le.mp (Nat.le_of_lt compileAux_max_lt_ret)))
       aesop))

  theorem op_multi_step_to_merged_left {e1 e2 : Exp} {maxId : Nat} {s1 s2 : State}
    (step : (compileAux maxId e1).1.dfg.PredicatedMultiStep ⟨NodePredicate.IsOp, NidRange maxId (compileAux maxId e1).2⟩ s1 s2)
    : (MergeTwo e1 e2 maxId).1.PredicatedMultiStep
        ⟨NodePredicate.IsOp, NidRangePlusPort maxId (compileAux maxId e1).2 ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩⟩
        (MergedState e1 e2 maxId s1) (MergedState e1 e2 maxId s2) := by
    generalize h_dfg : (compileAux maxId e1).1.dfg = dfg at *
    generalize h_Pred : (⟨NodePredicate.IsOp, NidRange maxId (compileAux maxId e1).2⟩ : Predicate) = Pred at *
    induction step with
    | refl h_s =>
      rename_i s
      simp_rw [←h_Pred] at *
      apply DFG.PredicatedMultiStep.refl
      intro port h
      have := h_s port (by omega)
      have : s (compileAux (compileAux maxId e1).2 e2).1.ret = [] := by
        apply h_s
        apply Or.intro_right
        apply ge_iff_le.mpr
        apply le_of_lt
        exact compileAux_max_lt_ret
      aesop
    | head node h_mem hd h_node h_s1 h_s2 tl ih =>
      rename_i s1 s2 _ s3
      simp_rw [←h_Pred, ←h_dfg] at *
      match node, h_node with
      | ⟨nid, .binOp op ts⟩, _ =>
        let newRet := (compileAux (compileAux maxId e1).2 e2).2
        let newTs :=
          (ts.map (λ t => if t = (compileAux maxId e1).1.ret then ⟨newRet, 0⟩ else t)).map
            (λ t => if t = (compileAux (compileAux maxId e1).2 e2).1.ret then ⟨newRet, 1⟩ else t)
        apply DFG.PredicatedMultiStep.head ⟨nid, .binOp op newTs⟩ (new_op_node_in_MergeTwo_left h_mem) _ _ _ _ (ih trivial)
        · cases hd with
          | binOp h1 h2 =>
            have h_nid_ne_ret : nid ≠ (compileAux (compileAux maxId e1).2 e2).2 := by
              apply Nat.ne_of_lt
              trans (compileAux maxId e1).2
              · exact compile_id_lt_max _ h_mem
              · exact compile_maxId_lt
            have h_fst_ne_ret : ¬(⟨nid, 0⟩ = (compileAux maxId e1).1.ret ∨ ⟨nid, 0⟩ = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
              port_ne_ret_in_op_step_merge maxId, e1, e2, op, ts, nid, h_mem
            have h_snd_ne_ret : ¬(⟨nid, 1⟩ = (compileAux maxId e1).1.ret ∨ ⟨nid, 1⟩ = (compileAux (compileAux maxId e1).2 e2).1.ret) := by
              port_ne_ret_in_op_step_merge maxId, e1, e2, op, ts, nid, h_mem
            have h_fst_eq : MergedState e1 e2 maxId s1 ⟨nid, 0⟩ = s1 ⟨nid, 0⟩ := mergedState_eq h_nid_ne_ret h_fst_ne_ret
            have h_snd_eq : MergedState e1 e2 maxId s1 ⟨nid, 1⟩ = s1 ⟨nid, 1⟩ := mergedState_eq h_nid_ne_ret h_snd_ne_ret
            apply Node.Step.subst_right (.binOp (h_fst_eq ▸ h1) (h_snd_eq ▸ h2))
            simp_rw [h_fst_eq, h_snd_eq]
            rw [MergedState_pop_assoc h_nid_ne_ret h_fst_ne_ret]
            rw [MergedState_pop_assoc h_nid_ne_ret h_snd_ne_ret]
            simp only [newTs, newRet]
            rw [←List.comp_map]
            have : ((fun t =>
                        if t = (compileAux (compileAux maxId e1).2 e2).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩
                        else t) ∘
                      fun t => if t = (compileAux maxId e1).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩ else t) =
                    (fun p =>
                  if p = (compileAux maxId e1).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩
                  else
                    if p = (compileAux (compileAux maxId e1).2 e2).1.ret then ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩
                    else p) := by
              funext x
              if x = (compileAux maxId e1).1.ret then
                simp_all only [ne_eq, mergeTwo, List.map_map, List.mem_filter,
                  List.mem_map, Function.comp_apply, and_true, not_or, mergedState, Port.mk.injEq,
                  zero_ne_one, and_self, or_self, ite_false, one_ne_zero, ite_true, ite_eq_right_iff]
                intro h_ret_eq
                have h_eq := (Port.mk.inj h_ret_eq).left.symm
                have h_ne := Nat.ne_of_lt (@compileAux_ret_lt_newMax e2 (compileAux maxId e1).2)
                contradiction
              else
                aesop
            rw [this]
            apply @MergedState_pushAll_assoc e1 e2 maxId (s1 ↤ ⟨nid, 0⟩ ↤ ⟨nid, 1⟩) (op.denote ((s1 ⟨nid, 0⟩).head h1) ((s1 ⟨nid, 1⟩).head h2)) ts
            have h_lt := @compile_maxId_lt e2 (compileAux maxId e1).2
            have := compile_binop_consumer_lt_max h_mem
            intro p h_mem
            have := this p h_mem
            have := Nat.lt_trans this h_lt
            apply Nat.ne_of_lt this
        · simp
        · state_pred_in_op_step_merge maxId, e1, e2, s1, h_s1
        · state_pred_in_op_step_merge maxId, e1, e2, s2, h_s2

  theorem op_multi_step_to_merged_right {e1 e2 : Exp} {maxId : Nat} {s1 s2 : State}
   (step : (compileAux (compileAux maxId e1).2 e2).1.dfg.PredicatedMultiStep
             ⟨NodePredicate.IsOp, NidRange (compileAux maxId e1).2 (compileAux (compileAux maxId e1).2 e2).2⟩ s1 s2)
   : (MergeTwo e1 e2 maxId).1.PredicatedMultiStep
       ⟨NodePredicate.IsOp, NidRangePlusPort (compileAux maxId e1).2 (compileAux (compileAux maxId e1).2 e2).2 ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩⟩
       (MergedState e1 e2 maxId s1) (MergedState e1 e2 maxId s2) := by
   sorry

  lemma compileAux_initial_state_id_range {env : Env} (e : Exp) (maxId : Nat)
    : ∀ port, port.node < maxId ∨ port.node ≥ (compileAux maxId e).2 → (compileAux maxId e).1.initialState env port = [] := by
    intro port h_or
    apply h_or.elim
    · intro h
      apply List.foldl_induction State.empty (compileAux maxId e).1.vars
        (λ x => x port = [])
      · simp
      · intro agg x h_mem ih
        suffices port.node ≠ x.2.node by aesop
        apply Nat.ne_of_lt
        apply Nat.lt_of_lt_of_le
        · exact h
        · exact compile_vars_id_ge_max _ h_mem
    · intro h
      apply List.foldl_induction State.empty (compileAux maxId e).1.vars
        (λ x => x port = [])
      · simp
      · intro agg x h_mem ih
        suffices port.node ≠ x.2.node by aesop
        symm
        apply Nat.ne_of_lt
        apply Nat.lt_of_lt_of_le
        · exact compile_vars_id_lt_newMax _ h_mem
        · exact h

  lemma compileAux_canonical_trace {e : Exp} {env : Env} {v : Ty} {maxId : Nat} (eval : Eval env e v)
    : (compileAux maxId e).1.dfg.Canonical maxId (compileAux maxId e).2 ((compileAux maxId e).1.initialState env) ((compileAux maxId e).1.finalState v) := by
    cases e with
    | var s =>
      apply DFG.Canonical.mk (s2 := (compileAux maxId (Exp.var s)).1.finalState v)
      · apply DFG.PredicatedMultiStep.single (node := ⟨maxId, .input [⟨maxId + 1, 0⟩]⟩)
        · simp
        · simp
        repeat (intro port h
                simp_all only [compileAux, MarkedDFG.initialState, VarMap.initialState, MarkedDFG.finalState,
                  List.foldl_cons, List.foldl_nil, State.push, State.empty, List.concat_eq_append,
                  List.nil_append, ite_eq_right_iff, List.cons_ne_self]
                apply Port.node_ne
                simp only
                omega)
        · apply Node.Step.subst_right (Node.Step.input (by aesop))
          · cases eval
            aesop
      · apply DFG.PredicatedMultiStep.refl
        intro port h
        simp only [MarkedDFG.finalState, compileAux, ite_eq_right_iff, List.cons_ne_self, imp_false]
        apply Port.node_ne
        apply h.elim <;> (simp_all only [compileAux]; omega)
    | plus e1 e2 =>
      cases eval with
      | plus eval1 eval2 =>
        rename_i x y
        obtain ⟨e1_s2, e1_inp, e1_ops⟩ := compileAux_canonical_trace eval1 (maxId := maxId)
        obtain ⟨e2_s2, e2_inp, e2_ops⟩ := compileAux_canonical_trace eval2 (maxId := (compileAux maxId e1).2)
        apply DFG.Canonical.mk ((MergedState e1 e2 maxId e1_s2) ⊕ (MergedState e1 e2 maxId e1_s2))
        · sorry
        · have ih1 := op_multi_step_to_merged_left (e2 := e2) e1_ops
          have ih2 := op_multi_step_to_merged_right e2_ops
          have ih1
            : (compileAux maxId (e1.plus e2)).1.dfg.PredicatedMultiStep
                ⟨NodePredicate.IsOp, NidRangePlusPort maxId (compileAux maxId e1).2 ⟨(compileAux (compileAux maxId e1).2 e2).2, 0⟩⟩
                (MergedState e1 e2 maxId e1_s2) (MergedState e1 e2 maxId ((compileAux maxId e1).1.finalState x)) :=
            DFG.PredicatedMultiStep.append_node (DFG.PredicatedMultiStep.append_node ih1 _) _
          have ih2
            : (compileAux maxId (e1.plus e2)).1.dfg.PredicatedMultiStep
                ⟨NodePredicate.IsOp, NidRangePlusPort (compileAux maxId e1).2 (compileAux (compileAux maxId e1).2 e2).2 ⟨(compileAux (compileAux maxId e1).2 e2).2, 1⟩⟩
                (MergedState e1 e2 maxId e2_s2) (MergedState e1 e2 maxId ((compileAux (compileAux maxId e1).2 e2).1.finalState y)) :=
            DFG.PredicatedMultiStep.append_node (DFG.PredicatedMultiStep.append_node ih2 _) _
          have := DFG.PredicatedMultiStep.merge_disjoint_nid_ranges_plus_port ih1 ih2
                    compile_maxId_lt compile_maxId_lt (le_refl _) (by simp) (le_refl _)

          sorry

  theorem compile_value_correct {e : Exp} {env : Env} {v : Ty} (eval : Eval env e v)
    : (compile e).dfg.MultiStep ((compile e).initialState env) ((compile e).finalState v) :=
    (compileAux_canonical_trace eval).to_MultiStep

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
        have : ⟨nid, 0⟩ = (compile e).ret := by aesop
        have : nid = (compile e).ret.node := (Port.mk.inj this).left
        have := (compile_ret_iff_output _ h_mem).mp this
        simp at this
      | binOp h1 h2 =>
        exfalso
        rename_i _ _ nid _ _
        have : ⟨nid, 0⟩ ≠ (compile e).ret := by
          intro h
          have := (compile_ret_iff_output _ h_mem).mp (Port.mk.inj h).left
          simp_all
        apply this
        simp only [MarkedDFG.finalState, compile, ne_eq, ite_eq_right_iff,
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
