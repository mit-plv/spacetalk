import Mathlib.Data.Stream.Defs

import Spacetalk.Vector

inductive Exp : Nat → Type
  | val : Nat → Exp n
  | var : Fin n → Exp n
  | plus : Exp n → Exp n → Exp n

def Exp.eval : Exp n → Vector Nat n → Nat
| val v, _ => v
| var idx, inp => inp[idx]
| plus e1 e2, inp => (e1.eval inp) + (e2.eval inp)

def Vector.packStreams (ss : Vector (Stream' α) len) : Stream' (Vector α len) :=
  λ n => ss.map (·.get n)

def Exp.denote (e : Exp inp) (inpVals : Vector (Stream' Nat) inp) : Stream' Nat :=
  λ n => (e.eval) (inpVals.packStreams n)

-- single output only
inductive Node (α : Type) : Nat → Type
  | id : Node α 1
  | const : Nat → Node α 0
  | plus : Node α 2

inductive Graph (α : Type) : Nat → Type
  | var : α → (α → Graph α n) → Graph α n
  | node : Node α inp → Vector α inp → Graph α 0
  | μClosed : Node α inp → Vector α inp → (α → Graph α n) → Graph α n
  | μOpenLeft : Node α inp → (α → Graph α n) → Graph α (inp + n)
  | μOpenRight : Node α inp → (α → Graph α n) → Graph α (n + inp)

def Node.denote : Node α inp → (Vector (Stream' Nat) inp → Stream' Nat)
| id => λ v => v[0]
| const v => λ _ => .const v
| plus => λ inp => Stream'.zip HAdd.hAdd inp[0] inp[1]

def Graph.denote : Graph (Stream' Nat) nInp → (Vector (Stream' Nat) nInp) → Stream' Nat
| var s c, inp => (c s).denote inp
| node n inp, _ => n.denote inp
| μClosed n μInp f, fInp => (f (n.denote μInp)).denote fInp
| μOpenLeft n f, vInp =>
  let (μNodeInp, fInp) := vInp.split
  (f (n.denote μNodeInp)).denote fInp
| μOpenRight n f, vInp =>
  let (fInp, μNodeInp) := vInp.split
  (f (n.denote μNodeInp)).denote fInp

def addInputs : (n : Nat) → (Vector α n → Graph α 0) → Graph α n
| 0, c => c #v[]
| n + 1, c =>
  .μOpenRight .id λ last =>
  addInputs n λ front =>
  c (front.push last)

def Exp.compileC (inputs : Vector α n) (cont : α → Graph α 0) : Exp n → Graph α 0
| val v => .μClosed (.const v) #v[] cont
| var idx => .var inputs[idx] cont
| plus e1 e2 =>
  e1.compileC inputs λ e1Out =>
  e2.compileC inputs λ e2Out =>
  .μClosed .plus #v[e1Out, e2Out] cont

def Exp.compile (e : Exp n) : Graph α n :=
  addInputs n λ inputs =>
  e.compileC inputs λ out => .node .id #v[out]

theorem graph_cast_denote {n m : Nat} {h : n = m} {g1 : Graph (Stream' Nat) n} {inp : Vector (Stream' Nat) m}
  : (h ▸ g1).denote inp = g1.denote (h ▸ inp) := by
  subst h
  simp_all only

lemma compileC_correct
  : ∀ e : Exp n, ∀ c : Stream' Nat → Graph _ 0,
    ∀ inpVec : Vector (Stream' Nat) n,
    (c (e.denote inpVec)).denote = (e.compileC inpVec c).denote := by
  intro e c inpVec
  induction e generalizing c with
  | val v => rfl
  | var idx =>
    unfold Exp.denote
    simp only [Exp.eval, Vector.packStreams, Fin.getElem_fin, Vector.getElem_map, Exp.compileC,
      Graph.denote]
    rfl
  | plus e1 e2 ih1 ih2 =>
    simp only [Exp.compileC]
    rw [←ih1]
    rw [←ih2]
    rfl

lemma addInputs_eq
  : ∀ n, ∀ c : Vector (Stream' Nat) n → Graph _ 0, ∀ inpVec : Vector (Stream' Nat) n,
    (c inpVec).denote #v[] = (addInputs n λ inputs => c inputs).denote inpVec := by
  intro n
  induction n with
  | zero =>
    intro c inpVec
    simp only [Vector.size_zero_eq, addInputs]
  | succ n ih =>
    intro c inpVec
    simp [addInputs, Graph.denote, Node.denote]
    rw [←ih]
    rw [Vector.split_last_push_eq]

theorem compile_correct : ∀ e : Exp n, e.denote = e.compile.denote := by
  intro e
  funext inp
  simp only [Exp.compile]
  have := compileC_correct e (λ out => .node .id #v[out]) inp
  simp only [Graph.denote] at this
  have := congr (a₁ := #v[]) this rfl
  simp only [Node.denote, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at this
  rw [this]
  rw [←addInputs_eq]
