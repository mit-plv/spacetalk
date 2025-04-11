import Mathlib.Data.Stream.Defs
import Mathlib.Data.Vector3
import Mathlib.Tactic.SimpRw
import Aesop

theorem Vector.cast_toArray {h : arr.size = n} {heq : n = m} : (heq ▸ ⟨arr, h⟩ : Vector α m).toArray = arr := by
  subst h heq
  simp_all only

def Vector.nil_append : ∀ vNil : Vector α 0, ∀ v : Vector α n, vNil ++ v = (Nat.zero_add n).symm ▸ v := by
  intro vNil v
  obtain ⟨_, h_size⟩ := vNil
  simp_rw [Array.size_eq_zero_iff.mp h_size]
  simp only [HAppend.hAppend, append, mk_eq]
  rw [Vector.cast_toArray]
  rw [Append.append, Array.instAppend]
  simp only [Array.append_eq_append, Array.empty_append]

def Vector.split (v : Vector α (n + m)) : Vector α n × Vector α m :=
  have h_min_eq : min n (n + m) = n := Nat.min_add_right
  have h_minus_eq : n + m - n = m := by omega
  (h_min_eq ▸ v.take n, h_minus_eq ▸ v.drop n)

theorem Vector.plus_eq_append
  : ∀ v : Vector α (n + m), ∃ (v1 : Vector α n) (v2 : Vector α m), v = v1 ++ v2 := by
  intro v
  have h_min_eq : min n (n + m) = n := Nat.min_add_right
  have h_minus_eq : n + m - n = m := by omega
  exists (h_min_eq ▸ v.take n)
  exists (h_minus_eq ▸ v.drop n)
  obtain ⟨arr, h⟩ := v
  simp only [take_eq_extract, extract_mk, Nat.sub_zero, drop_eq_cast_extract, cast_mk, mk_eq,
    toArray_append, cast_toArray, Array.extract_append_extract, Nat.zero_le, inf_of_le_left,
    Nat.le_add_right, sup_of_le_right]
  rw [←h]
  simp only [Array.extract_size]

theorem Vector.append_split_left_eq {v1 : Vector α n} {v2 : Vector α m} : (v1 ++ v2).split.1 = v1 := by
  obtain ⟨arr1, h1⟩ := v1
  obtain ⟨arr2, h2⟩ := v2
  subst h1
  subst h2
  simp only [split, mk_append_mk, take_eq_extract, extract_mk, Nat.sub_zero, Array.extract_append,
    Array.extract_size, Nat.zero_le, Nat.sub_eq_zero_of_le, Nat.sub_self, drop_eq_cast_extract,
    Array.extract_size_left, Nat.add_sub_cancel_left, Array.empty_append, cast_mk, eq_mk,
    cast_toArray, Array.append_right_eq_self, Array.extract_eq_empty_iff, inf_of_le_left, le_refl]

theorem Vector.append_split_right_eq {v1 : Vector α n} {v2 : Vector α m} : (v1 ++ v2).split.2 = v2 := by
  obtain ⟨arr1, h1⟩ := v1
  obtain ⟨arr2, h2⟩ := v2
  subst h1
  subst h2
  simp only [split, mk_append_mk, take_eq_extract, extract_mk, Nat.sub_zero, Array.extract_append,
    Array.extract_size, Nat.zero_le, Nat.sub_eq_zero_of_le, Nat.sub_self, drop_eq_cast_extract,
    Array.extract_size_left, Nat.add_sub_cancel_left, Array.empty_append, cast_mk, eq_mk,
    cast_toArray]

theorem Vector.append_split_map_left_eq {v1 : Vector α n} {v2 : Vector α m} {f : α → β}
  : ((v1 ++ v2).map f).split.1 = v1.map f := by
  obtain ⟨arr1, h1⟩ := v1
  obtain ⟨arr2, h2⟩ := v2
  subst h1
  subst h2
  simp only [split, mk_append_mk, map_mk, Array.map_append, take_eq_extract, extract_mk,
    Nat.sub_zero, Array.extract_append, Array.size_map, Nat.zero_le, Nat.sub_eq_zero_of_le,
    Nat.sub_self, drop_eq_cast_extract, Nat.add_sub_cancel_left, cast_mk, eq_mk, cast_toArray]
  rw [Array.map_extract.symm]
  simp only [Array.extract_size, Array.append_right_eq_self, Array.extract_eq_empty_iff,
    Array.size_map, Nat.zero_le, inf_of_le_left, le_refl]

theorem Vector.append_split_map_right_eq {v1 : Vector α n} {v2 : Vector α m} {f : α → β}
  : ((v1 ++ v2).map f).split.2 = v2.map f := by
  obtain ⟨arr1, h1⟩ := v1
  obtain ⟨arr2, h2⟩ := v2
  subst h1
  subst h2
  simp only [split, mk_append_mk, map_mk, Array.map_append, take_eq_extract, extract_mk,
    Nat.sub_zero, Array.extract_append, Array.size_map, Nat.zero_le, Nat.sub_eq_zero_of_le,
    Nat.sub_self, drop_eq_cast_extract, Nat.add_sub_cancel_left, cast_mk, eq_mk, cast_toArray]
  rw [Array.map_extract.symm]
  simp only [Array.extract_size_left, List.map_toArray, List.map_nil, Array.empty_append,
    Array.extract_eq_self_iff, Array.size_map, List.length_eq_zero_iff, Array.toList_eq_nil_iff,
    le_refl, and_self, or_true]

theorem Vector.append_assoc {v1 : Vector α n} {v2 : Vector α m} {v3 : Vector α k} : v1 ++ v2 ++ v3 = (Nat.add_assoc n m k) ▸ (v1 ++ (v2 ++ v3)) := by
  obtain ⟨arr1, h1⟩ := v1
  obtain ⟨arr2, h2⟩ := v2
  obtain ⟨arr3, h3⟩ := v3
  simp only [mk_append_mk, Array.append_assoc, mk_eq]
  rw [Vector.cast_toArray]

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
    obtain ⟨vInp1, vInp2, h_inp⟩ := Vector.plus_eq_append vInpExp
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
