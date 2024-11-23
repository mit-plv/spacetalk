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

  def Nid.fst (n : Nid) : Tag := ⟨n, 0⟩
  def Nid.snd (n : Nid) : Tag := ⟨n, 1⟩

  inductive Inp
    | port
    | const : Ty → Inp

  inductive NodeOp
    | input : List Tag → NodeOp
    | output : Inp → NodeOp
    | plus : Inp → Inp → List Tag → NodeOp

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
      → (h : (s nid.fst) ≠ [])
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

  theorem DFG.confluence {a b c : State} (dfg : DFG)
    : dfg.Step a b → dfg.Step a c → ∃ d, dfg.Step b d ∧ dfg.Step c d
    | .refl, .refl => ⟨a, .intro .refl .refl⟩
    | .refl, s => ⟨c, .intro s .refl⟩
    | s, .refl => ⟨b, .intro .refl s⟩
    | .step n1 n1s gs1, .step n2 n2s gs2 => by
      cases n1s <;> cases n2s
      all_goals sorry

  inductive Node.final : Node → State → Prop
    | input : {nid : Nid} → {ts : List Tag} → {s : State}
      → s nid.fst = []
      → Node.final ⟨nid, .input ts⟩ s
    | outputConst : {nid : Nid} → {s : State} → {c : Ty}
      → Node.final ⟨nid, .output (.const c)⟩ s
    | outputPort : {nid : Nid} → {s : State} → {ret : Ty}
      → s nid.fst = [ret]
      → Node.final ⟨nid, .output .port⟩ s
    | plusConstConst : {nid : Nid} → {ts : List Tag} → {s : State} → {x y : Ty}
      → Node.final ⟨nid, .plus (.const x) (.const y) ts⟩ s
    | plusPortConst : {nid : Nid} → {ts : List Tag} → {s : State} → {y : Ty}
      → s nid.fst = []
      → Node.final ⟨nid, .plus .port (.const y) ts⟩ s
    | plusConstPort : {nid : Nid} → {ts : List Tag} → {s : State} → {x : Ty}
      → s nid.snd = []
      → Node.final ⟨nid, .plus (.const x) .port ts⟩ s
    | plusPortPort : {nid : Nid} → {ts : List Tag} → {s : State}
      → s nid.fst = [] ∧ s nid.snd = []
      → Node.final ⟨nid, .plus .port .port ts⟩ s

  def DFG.final (dfg : DFG) (s : State) : Prop :=
    ∀ n ∈ dfg, n.final s
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

  def initialState (env : Arith.Env) (vars : VarMap) : Df.State :=
    vars.fold (λ s name tag => s ↦ ⟨env name, tag⟩) Df.State.empty

  theorem compile_correct {e : Arith.Exp} {env : Arith.Env} {v : Ty}
    (eval : Arith.Eval env e v) (finalState : Df.State) :
    Df.DFG.Step (compile e).dfg (initialState env (compile e).vars) finalState
      ∧ finalState (compile e).ret = [v] :=
    sorry

end Compiler
