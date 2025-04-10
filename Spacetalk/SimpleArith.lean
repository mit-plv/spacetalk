import Mathlib.Data.Stream.Defs
import Mathlib.Data.Vector3
import Mathlib.Tactic.SimpRw
import Aesop

def Vector.nil_append : ∀ vNil : Vector α 0, ∀ v : Vector α n, vNil.append v = v.cast (Nat.zero_add n).symm := by
  intro vNil v
  simp only [Vector.append, mk_eq, toArray_cast, Array.append_left_eq_self, toArray_eq_empty_iff]

def Vector.split (v : Vector α (n + m)) : Vector α n × Vector α m :=
  have h_min_eq : min n (n + m) = n := Nat.min_add_right
  have h_minus_eq : n + m - n = m := by omega
  (h_min_eq ▸ (v.take n), h_minus_eq ▸ (v.drop n))

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

theorem graph_subst {n m : Nat} {h : n = m} {g1 : Graph (Stream' Nat) n}
  : (h ▸ g1).denote = h ▸ g1.denote := by
  subst h
  simp_all only

def Exp.compile (e : Exp n) : Graph α n :=
  e.compileC λ out => .nodeClosed .id #v[out]

theorem compileC_correct
  : ∀ e : Exp nExp, ∀ f : Stream' Nat → Graph _ nCont,
    ∀ vInpExp : Vector (Stream' Nat) nExp, ∀ vInpCont : Vector (Stream' Nat) nCont,
    (f (e.denote vInpExp)).denote vInpCont = (e.compileC f).denote (vInpExp.append vInpCont) := by
  intro e f vInpExp vInpCont
  induction e generalizing f with
  | val v =>
    funext i
    simp only [Exp.denote, Stream'.const, Exp.eval, Exp.compileC, Graph.denote, Node.denote,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
    rw [Eq.rec_eq_cast]
    -- induction nCont with
    -- | zero =>
    --   cases congr_arg (Graph (Stream' ℕ)) Exp.compileC.proof_6
    --   simp [Graph.denote, Node.denote]
    --   unfold Exp.denote
    --   simp [Exp.eval]
    --   unfold Stream'.const
    --   cases vInpCont
    --   cases vInpExp
    --   simp [Vector.append]
    --   rename_i heq
    --   simp_rw [Array.size_eq_zero_iff.mp heq]
    --   simp_rw [Array.empty_append]
    -- | succ n ih =>
    -- cases (congr_arg (Graph (Stream' ℕ)) Exp.compileC.proof_6)
    cases h : Graph.μClosed (Node.val v) #v[] f
    · contradiction
    · rename_i node inpVec cont
      rw [Vector.nil_append vInpExp vInpCont]
      -- cases Eq.symm (Nat.zero_add nCont)
      -- cases congr_arg (Graph (Stream' ℕ)) Exp.compileC.proof_6
      -- have : 0 + nCont = nCont := by aesop
      -- rw [this]
      -- cases @cast (Graph (Stream' ℕ) nCont) (Graph (Stream' ℕ) (0 + nCont)) (congr_arg (Graph (Stream' ℕ)) Exp.compileC.proof_6) (Graph.μClosed node inpVec cont)
      sorry
    · contradiction

  | var => sorry
  | plus e1 e2 ih1 ih2 =>
    simp only [Exp.denote, Exp.eval, Exp.compile, Stream'.const, Exp.compileC]
    sorry
