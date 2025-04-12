import Mathlib.Order.Lattice
import Aesop

theorem Vector.size_zero_eq {v : Vector α 0} : v = #v[] := by
  simp_all only [eq_mk, toArray_eq_empty_iff]

theorem Vector.cast_toArray {h : arr.size = n} {heq : n = m} : (heq ▸ ⟨arr, h⟩ : Vector α m).toArray = arr := by
  subst h heq
  simp_all only

def Vector.append_nil {v : Vector α n} {vNil : Vector α 0} : v ++ vNil = v := by
  obtain ⟨arrNil, h_nil⟩ := vNil
  obtain ⟨arr, h⟩ := v
  simp only [Nat.add_zero, eq_mk]
  simp only [HAppend.hAppend, append, Nat.add_zero]
  subst h
  simp_all only [List.length_eq_zero_iff, Array.toList_eq_nil_iff]
  subst h_nil
  rfl

def Vector.nil_append {vNil : Vector α 0} {v : Vector α n} : vNil ++ v = (Nat.zero_add n).symm ▸ v := by
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

theorem Vector.add_eq_append
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

theorem Vector.split_last_push_eq {v : Vector α (n + 1)} : v.split.1.push v.split.2[0] = v := by
  obtain ⟨arr, h⟩ := v
  simp only [Vector.split, Vector.drop_mk]
  rw [Vector.getElem_mk]
  simp only [take_eq_extract, Nat.add_one_sub_one, extract_eq_pop, Nat.sub_zero, pop_mk, cast_mk,
    cast_toArray, Array.getElem_extract, Nat.add_zero, eq_mk, toArray_push]
  obtain ⟨l⟩ := arr
  simp only [List.pop_toArray, List.getElem_toArray, List.push_toArray, Array.mk.injEq]
  simp at h
  have h_ne_nil : l ≠ [] := by aesop
  have : n = l.length - 1 := by aesop
  simp_rw [this]
  rw [←(List.getLast_eq_getElem l h_ne_nil)]
  exact List.dropLast_concat_getLast (l := l) h_ne_nil
