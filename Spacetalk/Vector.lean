import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Vector.Basic

theorem Vector.get_append_left {xs : Vector α n} {ys : Vector α m} {i : Fin n}
  : (xs.append ys).get ⟨i, by apply Nat.lt_add_right; exact i.isLt⟩ = xs.get i := by
  apply List.get_append_left

theorem Vector.get_append_right {xs : Vector α n} {ys : Vector α m} {i : Fin m}
  : (xs.append ys).get ⟨i + n, by have := i.isLt; linarith⟩ = ys.get i := by
  simp_rw [Vector.get_eq_get]
  have := Vector.toList_append xs ys
  rw [List.get_of_eq this]
  simp [Fin.cast]
  have := List.get_append_right xs.toList ys.toList (i := i + n)
  have h_i_lt_append : ↑i + n < (xs.toList ++ ys.toList).length := by have := i.isLt; simp; linarith
  have h_i_sub_xs_lt_ys : ↑i + n - xs.toList.length < ys.toList.length := by simp
  have : List.get (xs.toList ++ ys.toList) ⟨↑i + n, h_i_lt_append⟩ = List.get ys.toList ⟨i + n - xs.toList.length, h_i_sub_xs_lt_ys⟩ := this (by rw [Vector.toList_length xs]; linarith)
  have h_eq : (⟨↑i + n - xs.toList.length, h_i_sub_xs_lt_ys⟩ : Fin ys.toList.length) = ⟨↑i, Fin.cast.proof_1 (toList_length ys).symm i⟩ := by simp
  rw [←h_eq]
  exact this

-- @[simp]
-- theorem Vector.length_append (as : Vector α n) (bs : Vector α m) : (as.append bs).length = n + m := by
--   simp
