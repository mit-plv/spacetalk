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

  def Exp.notConst : Exp → Bool
    | .const _ => false
    | _ => true
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
    | output
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
    : dfg.Step a b → dfg.Step a c → ∃ d, dfg.Step b d ∧ dfg.Step c d := by
    sorry

  inductive Node.final : Node → State → Prop
    | input : {nid : Nid} → {ts : List Tag} → {s : State}
      → s nid.fst = []
      → Node.final ⟨nid, .input ts⟩ s
    | output : {nid : Nid} → {s : State} → {ret : Ty}
      → s nid.fst = [ret]
      → Node.final ⟨nid, .output⟩ s
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
    ret : Tag

  def compileAux (maxNid : Df.Nid) (e : Arith.Exp) (h : e.notConst = true) : MarkedDFG :=
    match e, h with
    | .var s, _ =>
      sorry
    | .plus e1 e2, _ => sorry

  def compile (e : Arith.Exp) (h : e.notConst = true) : MarkedDFG :=
    compileAux 0 e h

  def initialState (env : Arith.Env) (vars : VarMap) : Df.State :=
    vars.fold (λ s name tag => s ↦ ⟨env name, tag⟩) Df.State.empty

  theorem compile_correct {e : Arith.Exp} {env : Arith.Env} {v : Ty}
    (h : e.notConst = true) (eval : Arith.Eval env e v) (finalState : Df.State) :
    Df.DFG.Step (compile e h).dfg (initialState env (compile e h).vars) finalState
      ∧ finalState (compile e h).ret = [v] :=
    sorry

end Compiler
