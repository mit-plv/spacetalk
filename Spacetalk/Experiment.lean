import Mathlib.Data.Vector.Basic

open Mathlib

abbrev Ty := Nat

namespace Arith
  inductive Exp
    | const : Ty → Exp
    | var : String → Exp
    | plus : Exp → Exp → Exp

  abbrev Env := String → Ty

  inductive Eval : Env → Exp → Ty → Prop
    | const : Eval env (.const v) v
    | var : env s = v → Eval env (.var s) v
    | plus : Eval env e1 x
      → Eval env e2 y
      → Eval env (.plus e1 e2) (x + y)
end Arith

namespace Df
  abbrev Nid := Nat
  abbrev Pid := Nat

  structure Tag where
    node : Nid
    port : Pid
  deriving DecidableEq

  structure Token where
    val : Ty
    tag : Tag

  structure BToken where
    val : Ty
    tags : List Tag

  @[simp]
  def Nid.fst (n : Nid) : Tag := ⟨n, 0⟩

  @[simp]
  def Nid.snd (n : Nid) : Tag := ⟨n, 1⟩

  inductive Inp
    | port
    | const : Ty → Inp

  inductive NodeOp
    | input : List Tag → NodeOp
    | output : Inp → NodeOp
    | plus : Inp → Inp → List Tag → NodeOp

  @[simp]
  def NodeOp.isOutput : NodeOp → Bool
    | .output _ => true
    | _ => false

  structure Node where
    id : Nid
    op : NodeOp

  abbrev DFG := List Node

  abbrev State := Tag → List Ty

  def State.empty : State := λ _ => []

  def State.pop (s : State) (t : Tag) : State :=
    λ t' => if t' = t then (s t).tail else s t'

  def State.push (s : State) (tok : Token) : State :=
    λ t' => if t' = tok.tag then (s tok.tag).concat tok.val else (s t')

  def State.pushAll (s : State) (tok : BToken) : State :=
    tok.tags.foldl (λ s tag => s.push ⟨tok.val, tag⟩) s

  infixl:100 " ↤ " => State.pop
  infixl:100 " ↦ " => State.push
  infixl:100 " ↦↦ " => State.pushAll

  inductive Node.Step : Node → State → State → Prop
    | input : {nid : Nid} → {ts : List Tag} → {s : State}
      → (h : s nid.fst ≠ [])
      → Node.Step ⟨nid, .input ts⟩ s (s ↤ nid.fst ↦↦ ⟨(s nid.fst).head h, ts⟩)
    | outputConst : {nid : Nid} → {s : State} → {c : Ty}
      → s nid.fst = []
      → Node.Step ⟨nid, .output (.const c)⟩ s (s ↦ ⟨c, nid.fst⟩)
    | plusConstConst : {nid : Nid} → {ts : List Tag} → {s : State} → {e1 e2 : Inp}
      → (h1 : e1 = .const x) → (h2 : e2 = .const y)
      → Node.Step ⟨nid, .plus e1 e2 ts⟩ s (s ↦↦ ⟨x + y, ts⟩)
    | plusPortConst : {nid : Nid} → {ts : List Tag} → {s : State} → {e1 e2 : Inp}
      → (h1 : s nid.fst ≠ []) → (h2 : e2 = .const y)
      → Node.Step ⟨nid, .plus e1 e2 ts⟩ s (s ↤ nid.fst ↦↦ ⟨((s nid.fst).head h1) + y, ts⟩)
    | plusConstPort : {nid : Nid} → {ts : List Tag} → {s : State} → {e1 e2 : Inp}
      → (h1 : e1 = .const x) → (h2 : s nid.snd ≠ [])
      → Node.Step ⟨nid, .plus e1 e2 ts⟩ s (s ↤ nid.snd ↦↦ ⟨x + ((s nid.snd).head h2), ts⟩)
    | plusPortPort : {nid : Nid} → {ts : List Tag} → {s : State} → {e1 e2 : Inp}
      → (h1 : s nid.fst ≠ []) → (h2 : s nid.snd ≠ [])
      → Node.Step ⟨nid, .plus e1 e2 ts⟩ s (s ↤ nid.fst ↤ nid.snd ↦↦ ⟨((s nid.fst).head h1) + ((s nid.snd).head h2), ts⟩)

  inductive DFG.Step : DFG → State → State → Prop
    | refl : DFG.Step dfg s s
    | step : {dfg : DFG} → {node : Node}
      → node ∈ dfg
      → node.Step s1 s2
      → DFG.Step dfg s2 s3
      → DFG.Step dfg s1 s3
end Df

namespace Compiler
  abbrev VarMap := Std.HashMap String Df.Tag

  structure MarkedDFG where
    dfg : Df.DFG
    vars : VarMap
    ret : Df.Tag

  def getRetInp (dfg : Df.DFG) (nid : Df.Nid) : Df.Inp :=
    match dfg.find? (·.id = nid) with
    | some ⟨_, .output i⟩ => i
    | _ => .port

  def Df.Node.updateReturn (ret : Df.Tag) (newRet : Df.Tag) (node : Df.Node) : Df.Node :=
    let replace t := if t = ret then newRet else t
    {node with op :=
      match node.op with
      | .input ts => .input (ts.map replace)
      | .output i => .output i
      | .plus e1 e2 ts => .plus e1 e2 (ts.map replace)
    }

  def merge (g1 : MarkedDFG) (g2 : MarkedDFG) (nid : Df.Nid)
    : Df.DFG × VarMap × Df.Inp × Df.Inp :=
    let (dfg, vars) := g2.vars.fold (
      λ (dfg, vars) s t2 =>
        match dfg.find? (·.id = t2.node) with
        | some ⟨_, .input ts2⟩ =>
          match g1.vars.get? s with
          | some t1 =>
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
          | none => (dfg, vars.insert s t2)
        | _ => (dfg, vars)
    ) (g1.dfg ++ g2.dfg, g1.vars)

    -- Find the input edge of the orignal output nodes
    let ret1 := getRetInp dfg g1.ret.node
    let ret2 := getRetInp dfg g2.ret.node

    -- Update links to the original output nodes
    let updateReturn dfg ret := match ret with
      | .port => dfg.map (Df.Node.updateReturn g1.ret nid.fst)
      | .const _ => dfg
    let dfg := updateReturn dfg ret1
    let dfg := updateReturn dfg ret2

    -- Remove all output nodes
    let dfg := dfg.filter (λ node => match node.op with | .output _ => false | _ => true)

    (dfg, vars, ret1, ret2)

  def compileAux (maxNid : Df.Nid) : Arith.Exp → MarkedDFG × Df.Nid
    | .const c =>
      let dfg := [⟨maxNid, .output (.const c)⟩]
      (⟨dfg, .empty, maxNid.fst⟩, maxNid + 1)
    | .var s =>
      let inpId := maxNid
      let outId := maxNid + 1
      let dfg := [⟨inpId, .input []⟩, ⟨outId, .output .port⟩]
      let vars := Std.HashMap.empty.insert s maxNid.fst
      (⟨dfg, vars, outId.fst⟩, maxNid + 2)
    | .plus e1 e2 =>
      let (e1, maxNid) := compileAux maxNid e1
      let (e2, maxNid) := compileAux maxNid e2
      let plusId := maxNid
      let outId := maxNid + 1
      let (dfg, vars, i1, i2) := merge e1 e2 plusId
      let dfg := ⟨plusId, .plus i1 i2 [outId.fst]⟩ :: ⟨outId, .output .port⟩ :: dfg
      (⟨dfg, vars, outId.fst⟩, maxNid + 2)

  def compile (e : Arith.Exp) : MarkedDFG :=
    (compileAux 0 e).fst

  def MarkedDFG.initialState (dfg : MarkedDFG) (env : Arith.Env) : Df.State :=
    dfg.vars.fold (λ s name tag => s ↦ ⟨env name, tag⟩) .empty

  @[simp]
  def MarkedDFG.finalState (dfg : MarkedDFG) (v : Ty) : Df.State :=
    λ t => if t = dfg.ret then [v] else []

  -- Proofs

  lemma ret_is_output {e : Arith.Exp}
    : ∀ node, node ∈ (compile e).dfg ∧ node.id = (compile e).ret.node → node.op.isOutput = true := by
    intro node h_mem
    sorry

  theorem compile_value_correct {e : Arith.Exp} {env : Arith.Env} {v : Ty}
    : Arith.Eval env e v
      → (compile e).dfg.Step ((compile e).initialState env) ((compile e).finalState v) :=
    sorry

  theorem compile_confluence {e : Arith.Exp} {a b c : Df.State}
    : (compile e).dfg.Step a b → (compile e).dfg.Step a c
        → ∃ d, (compile e).dfg.Step b d ∧ (compile e).dfg.Step c d
    | .refl, .refl => ⟨a, .intro .refl .refl⟩
    | .refl, s => ⟨c, .intro s .refl⟩
    | s, .refl => ⟨b, .intro .refl s⟩
    | .step n1 n1s gs1, .step n2 n2s gs2 => by
      cases n1s <;> cases n2s
      all_goals sorry

  lemma final_state_halts {e : Arith.Exp} {v : Ty}
    : ∀ s, (compile e).dfg.Step ((compile e).finalState v) s → s = (compile e).finalState v := by
    intro s step
    cases step with
    | refl => rfl
    | step h_mem ns gs =>
      cases ns with
      | input h =>
        rename_i nid ts
        have : nid.fst = (compile e).ret := by simp at h; exact h
        have : nid = (compile e).ret.node := (Df.Tag.mk.inj this).left
        have := ret_is_output ⟨nid, .input ts⟩ ⟨h_mem, this⟩
        simp at this
      | outputConst h => sorry
      | plusConstConst h1 h2 => sorry
      | plusPortConst h1 h2 => sorry
      | plusConstPort h1 h2 => sorry
      | plusPortPort h1 h2 => sorry

  theorem compile_correct {e : Arith.Exp} {env : Arith.Env} {v : Ty}
    : Arith.Eval env e v
      → ∀ s, (compile e).dfg.Step ((compile e).initialState env) s
              → (compile e).dfg.Step s ((compile e).finalState v) := by
    intro as s ds
    have := compile_confluence ds (compile_value_correct as)
    obtain ⟨w, h⟩ := this
    obtain ⟨left, right⟩ := h
    have := final_state_halts w right
    rw [this] at left
    exact left

end Compiler
