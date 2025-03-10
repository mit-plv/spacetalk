import Mathlib.Logic.Relation
import Aesop

namespace DF

-- Syntax
structure Port where
  node : Nat
  port : Nat
deriving DecidableEq

theorem Port.node_ne {p1 p2 : Port} : p1.node ≠ p2.node → p1 ≠ p2 := by
  aesop

inductive BinOp
  | plus

inductive NodeOp
  | input : String → List Port → NodeOp
  | output : NodeOp
  | binOp : BinOp → List Port → NodeOp

structure Node where
  id : Nat
  op : NodeOp

@[simp]
def Node.isInput : Node → Bool
  | ⟨_, .input _ _⟩ => true
  | _ => false

@[simp]
def Node.isOutput : Node → Bool
  | ⟨_, .output⟩ => true
  | _ => false

@[simp]
def Node.notOutput : Node → Bool
  | ⟨_, .output⟩ => false
  | _ => true

@[simp]
def Node.opTypeEq : Node → Node → Bool
  | ⟨_, .input _ _⟩, ⟨_, .input _ _⟩
  | ⟨_, .output⟩, ⟨_, .output⟩
  | ⟨_, .binOp _ _⟩, ⟨_, .binOp _ _⟩ => true
  | _, _ => false

theorem Node.opTypeEq_refl {node : Node} : Node.opTypeEq node node := by
  obtain ⟨nid, op⟩ := node
  cases op <;> rfl

abbrev DFG := List Node

-- Semantics
abbrev State := Port → List Nat

structure Token where
  val : Nat
  port : Port

structure BToken where
  val : Nat
  ports : List Port

@[simp]
def State.empty : State := λ _ => []

@[simp]
def State.pop (s : State) (p : Port) : State :=
  λ p' => if p' = p then (s p).tail else s p'

@[simp]
def State.push (s : State) (tok : Token) : State :=
  λ p => if p = tok.port then (s tok.port).concat tok.val else (s p)

@[simp]
def State.pushAll (s : State) (tok : BToken) : State :=
  tok.ports.foldl (λ s port => s.push ⟨tok.val, port⟩) s

@[simp]
def BinOp.denote : BinOp → Nat → Nat → Nat
  | plus => HAdd.hAdd

infixl:100 " ↤ " => State.pop
infixl:100 " ↦ " => State.push
infixl:100 " ↦↦ " => State.pushAll

inductive Node.Step : Node → State → State → Prop
  | input : (h : s ⟨nid, 0⟩ ≠ [])
    → Node.Step ⟨nid, .input var ports⟩
      s
      (s
        ↤ ⟨nid, 0⟩
        ↦↦ ⟨(s ⟨nid, 0⟩).head h, ports⟩)
  | binOp : {op : BinOp} → (h1 : s ⟨nid, 0⟩ ≠ []) → (h2 : s ⟨nid, 1⟩ ≠ [])
    → Node.Step ⟨nid, .binOp op ports⟩
      s
      (s
        ↤ ⟨nid, 0⟩
        ↤ ⟨nid, 1⟩
        ↦↦ ⟨op.denote ((s ⟨nid, 0⟩).head h1) ((s ⟨nid, 1⟩).head h2), ports⟩)

inductive DFG.Step : DFG → State → State → Prop
  | node : (node : Node) → node ∈ dfg → node.Step s1 s2 → DFG.Step dfg s1 s2

abbrev DFG.MultiStep (dfg : DFG) : State → State → Prop :=
  Relation.ReflTransGen dfg.Step

end DF
