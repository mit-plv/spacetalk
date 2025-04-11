import Mathlib.Data.Stream.Defs

import Spacetalk.Vector

inductive Exp : Nat → Type
  | val : Nat → Exp 0
  | var : Exp 1
  | plus : Exp inp1 → Exp inp2 → Exp (inp1 + inp2)

def Exp.eval : Exp inp → Vector Nat inp → Nat
| (.val v), _ => v
| .var, inp => inp[0]
| (.plus e1 e2), inp =>
  let (inp1, inp2) := inp.split
  (e1.eval inp1) + (e2.eval inp2)

def Vector.packStreams (ss : Vector (Stream' α) len) : Stream' (Vector α len) :=
  λ n => ss.map (·.get n)

def Exp.denote (e : Exp inp) (inpVals : Vector (Stream' Nat) inp) : Stream' Nat :=
  λ n => (e.eval) (inpVals.packStreams n)

-- single output only
inductive Node (α : Type) : Nat → Type
  | id : Node α 1
  | val : Nat → Node α 0
  | plus : Node α 2

inductive Graph (α : Type) : Nat → Type
  | nodeClosed : Node α inp → Vector α inp → Graph α 0
  | μClosed : Node α inp → Vector α inp → (α → Graph α n) → Graph α n
  | μOpen : Node α inp → (α → Graph α n) → Graph α (inp + n)

def Node.denote : Node α inp → (Vector (Stream' Nat) inp → Stream' Nat)
| .id => λ v => v[0]
| .val v => λ _ => .const v
| .plus => λ inp => Stream'.zip HAdd.hAdd inp[0] inp[1]

def Graph.denote : Graph (Stream' Nat) nInp → (Vector (Stream' Nat) nInp) → Stream' Nat
| (.nodeClosed n inp), _ => n.denote inp
| (.μClosed n μInp f), fInp => (f (n.denote μInp)).denote fInp
| (.μOpen n f), vInp =>
  let (μNodeInp, fInp) := vInp.split
  (f (n.denote μNodeInp)).denote fInp

def Exp.compileC (cont : α → Graph α nCont) : Exp nExp → Graph α (nExp + nCont)
| .val v => (Nat.zero_add nCont).symm ▸ .μClosed (.val v) #v[] cont
| .var => .μOpen .id cont
| @Exp.plus inp1 inp2 e1 e2 =>
  have : inp1 + (inp2 + nCont) = inp1 + inp2 + nCont := by omega
  this ▸
    (e1.compileC λ e1Out =>
     e2.compileC λ e2Out =>
     .μClosed .plus #v[e1Out, e2Out] cont)

theorem graph_cast_denote {n m : Nat} {h : n = m} {g1 : Graph (Stream' Nat) n} {inp : Vector (Stream' Nat) m}
  : (h ▸ g1).denote inp = g1.denote (h ▸ inp) := by
  subst h
  simp_all only

def Exp.compile (e : Exp n) : Graph α n :=
  e.compileC λ out => .nodeClosed .id #v[out]

theorem compileC_correct
  : ∀ e : Exp nExp, ∀ c : Stream' Nat → Graph _ nCont,
    ∀ vInpExp : Vector (Stream' Nat) nExp, ∀ vInpCont : Vector (Stream' Nat) nCont,
    (c (e.denote vInpExp)).denote vInpCont = (e.compileC c).denote (vInpExp ++ vInpCont) := by
  intro e c vInpExp vInpCont
  induction e generalizing c nCont with
  | val v =>
    -- Get rid of all castings first
    simp only [Exp.compileC, graph_cast_denote]
    conv =>
      rhs
      arg 2
      simp only [Vector.nil_append, Eq.rec_eq_cast, cast_cast, cast_eq]
    -- rfl closes the goal now
    rfl
  | var =>
    unfold Exp.denote
    simp only [Exp.eval, Vector.packStreams, Vector.getElem_map, Exp.compileC, Graph.denote,
      Node.denote, Vector.append_split_left_eq, Vector.append_split_right_eq]
    rfl
  | plus e1 e2 ih1 ih2 =>
    -- Get rid of all casts
    simp only [Exp.compileC, graph_cast_denote]
    obtain ⟨vInp1, vInp2, h_inp⟩ := Vector.add_eq_append vInpExp
    rw [h_inp]
    conv =>
      rhs
      arg 2
      simp only [Vector.append_assoc, Eq.rec_eq_cast, cast_cast, cast_eq]
    -- No more casts!
    rw [←(ih1 _ vInp1)]
    rw [←(ih2 _ vInp2)]
    simp only [Graph.denote, Node.denote, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
    unfold Stream'.zip
    unfold Exp.denote
    simp only [Exp.eval, Vector.packStreams, Vector.append_split_map_left_eq,
      Vector.append_split_map_right_eq]
    subst h_inp
    rfl

theorem compile_correct : ∀ e : Exp nExp, e.denote = e.compile.denote := by
  intro e
  funext inp
  simp only [Exp.compile]
  have := compileC_correct e (λ out => .nodeClosed .id #v[out]) inp #v[]
  rw [Vector.append_nil] at this
  rw [←this]
  rfl
