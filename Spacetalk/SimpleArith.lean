import Mathlib.Data.Stream.Defs
import Aesop

def Vector.split (v : Vector α (n + m)) : Vector α n × Vector α m :=
  have h_min_eq : min n (n + m) = n := Nat.min_add_right
  have h_minus_eq : n + m - n = m := by omega
  (h_min_eq ▸ (v.take n), h_minus_eq ▸ (v.drop n))

inductive Exp
  | val : Nat → Exp
  | plus : Exp → Exp → Exp

def Exp.eval : Exp → Nat
| .val v => v
| .plus e1 e2 => e1.eval + e2.eval

def Exp.denote (e : Exp) : Stream' Nat := .const (e.eval)

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

def Exp.compileC (cont : α → Graph α n) : Exp → Graph α n
| .val v => .μClosed (.val v) #v[] cont
| .plus e1 e2 =>
  e1.compileC λ e1Out =>
  e2.compileC λ e2Out =>
  .μClosed .plus #v[e1Out, e2Out] cont

def Exp.compile (e : Exp) : Graph α 0 :=
  e.compileC λ out => .nodeClosed .id #v[out]

theorem compileC_correct
  : ∀ e : Exp, ∀ f : _ → Graph _ n,
    (f e.denote).denote = (e.compileC f).denote := by
  intro e f
  induction e generalizing f with
  | val v =>
    simp only [Exp.denote, Stream'.const, Exp.eval, Exp.compileC, Graph.denote, Node.denote,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
  | plus e1 e2 ih1 ih2 =>
    simp only [Exp.denote, Exp.eval, Exp.compile, Stream'.const, Exp.compileC]
    rw [←ih1]
    rw [←ih2]
    simp only [Graph.denote]
    rfl

theorem compile_correct : ∀ e : Exp, e.denote = e.compile.denote #v[] := by
  intro e
  simp only [Exp.compile]
  have := compileC_correct e (λ out => .nodeClosed .id #v[out])
  rw [←this]
  simp only [Graph.denote, Node.denote, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero]
