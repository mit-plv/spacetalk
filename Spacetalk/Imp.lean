import Mathlib.Data.Stream.Defs

import Spacetalk.HList
import Spacetalk.Vector

--------------------- Common ----------------------------------
inductive Ty
  | unit
  | bool
  | nat

inductive BinOp : Ty → Ty → Ty → Type
  | add : BinOp .nat .nat .nat
  | mul : BinOp .nat .nat .nat

@[simp, reducible]
def Ty.denote : Ty → Type
  | unit => Unit
  | bool => Bool
  | nat => Nat

@[simp]
abbrev Ty.streamDenote : Ty → Type := Stream' ∘ Ty.denote

def BinOp.denote : BinOp α β γ → α.denote → β.denote → γ.denote
  | add => Nat.add
  | mul => Nat.mul

--------------------- Imperative Language ---------------------
inductive Imp (C M : Ty → Type) : Ty → Type
  | const (n : Nat) : Imp C M .nat
  | var (v : C α) : Imp C M α
  | alloc (init : Imp C M α) (body : M α → Imp C M β) : Imp C M β
  | read (v : M α) : Imp C M α
  | write (v : M α) (e : Imp C M α) : Imp C M .unit
  | binop (op : BinOp α β γ) (arg1 : Imp C M α) (arg2 : Imp C M β) : Imp C M γ
  | seq (e1 : Imp C M α) (e2 : Imp C M β) : Imp C M β
  | for_ (start stop : Nat) (body : C .nat → Imp C M .unit) : Imp C M .unit

inductive Ref
  | unit
  | bool (b : Bool)
  | nat (n : Nat)
deriving Repr

def mkRef {t : Ty} (v : t.denote) : Ref :=
  match t with
  | .unit => .unit
  | .bool => .bool v
  | .nat => .nat v

abbrev Store := List Ref

def Imp.denote {t : Ty} : Imp Ty.denote (λ _ ↦ Nat) t → StateT Store Option t.denote
  | const n => pure n
  | var v => pure v
  | alloc val body => do
    let val ← val.denote
    let store ← .get
    .set (store.concat (mkRef val))
    let res ← (body store.length).denote
    .modifyGet λ store =>
    (res, store.dropLast)
  | read idx => do
    let store ← .get
    let ref ← store[idx]?
    match t, ref with
    | .unit, .unit => pure ()
    | .bool, .bool b => pure b
    | .nat, .nat n => pure n
    | _, _ => none
  | write idx e => do
    let store ← .get
    let val ← e.denote
    .set (store.set idx (mkRef val))
  | binop op e1 e2 => do
    let x ← e1.denote
    let y ← e2.denote
    pure (op.denote x y)
  | seq e1 e2 => do
    let _ ← e1.denote
    e2.denote
  | for_ start stop body => do
    let _ ← (List.range' start stop).forM (λ idx => (body idx).denote)
    pure ()

----------------- Dataflow Graphs ----------------------
-- single output only
inductive Node (rep : Ty → Type) : List Ty → Ty → Type
  | id : Node rep [α] α
  | const : Nat → Node rep [] .nat
  | binop : BinOp α β γ → Node rep [α, β] γ

inductive Graph (rep : Ty → Type) : List Ty → Ty → Type
  | node (node : Node rep inps out) (inpVals : HList rep inps) : Graph rep [] out
  | μClosed (node : Node rep inps out) (inpVals : HList rep inps) (c : rep out → Graph rep cInps cOut) : Graph rep cInps cOut
  | μOpen (node : Node rep inps out) (c : rep out → Graph rep cInps cOut) : Graph rep (cInps ++ inps) cOut

def Node.denote {inps : List Ty} {out : Ty} : Node Ty.streamDenote inps out → HList Ty.streamDenote inps → Stream' out.denote
  | id, hl => hl.get .head
  | const v, _ => .const v
  | binop op, hl => Stream'.zip op.denote (hl.get .head) (hl.get (.tail .head))

def Graph.denote {inps : List Ty} {out : Ty} : Graph Ty.streamDenote inps out → HList Ty.streamDenote inps → Stream' out.denote
  | node n inp, _ => n.denote inp
  | μClosed n μInp f, fInp => (f (n.denote μInp)).denote fInp
  | μOpen n f, vInp =>
    let (fInp, μNodeInp) := vInp.split
    (f (n.denote μNodeInp)).denote fInp


  ---------------------- Compiler ------------------------------
def Imp.compileAux (cont : rep out → Graph rep cInp cOut) : Imp rep rep out → Graph rep cInp cOut
  | const n => .μClosed (.const n) [] cont
  | var v => cont v
  | alloc init body => sorry
  | read v => sorry
  | write v e => sorry
  | binop op arg1 arg2 => sorry
  | seq e1 e2 => sorry
  | for_ start stop body => sorry


def Imp.compile (prog : Imp C M out) : Graph rep [] out :=

  sorry


---------------------- DFG Utilities ------------------------------
-- def Node.toString (nid : Nat) (inp : Vector String n) : Node String n → String
-- | id => s!"{nid}: id #{inp[0]}"
-- | const v => s!"{nid}: const {v}"
-- | plus => s!"{nid}: #{inp[0]} + #{inp[1]}"

-- def Graph.toStringAux : Graph String n → StateM Nat String
-- | node n inp =>
--   .modifyGet λ nid => (n.toString nid inp, nid + 1)
-- | μClosed n inp f => do
--   let nid ← .get
--   .set (nid + 1)
--   let c ← (f nid.repr).toStringAux
--   let n := n.toString nid inp
--   return s!"{n}\n{c}"
-- | @μOpen _ nNode nCont n f => do
--   let nid ← .get
--   .set (nid + 1)
--   let c ← (f nid.repr).toStringAux
--   let n := n.toString nid ((Vector.range' nCont nNode).map (s!"ext_{·.repr}"))
--   return s!"{n}\n{c}"

-- def Graph.toString (g : Graph String n) : String :=
--   (g.toStringAux.run 0).1

-- instance : Repr (Graph String n) where
--   reprPrec g _ := g.toString



------------------- Examples --------------------------
def impDotProd (n : Nat) : Imp C M .nat :=
  .alloc (.const 0) λ acc =>
  .seq
    (.for_ 0 n λ i =>
      .write acc
        (.binop .add
          (.read acc)
          (.binop .mul (.var i) (.var i))))
    (.read acc)

def dotProd (n : Nat) := (impDotProd n).denote.run []

#eval dotProd 100000
