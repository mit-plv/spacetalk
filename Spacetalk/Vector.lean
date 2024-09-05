import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Vector.Basic

open Mathlib
open Vector

theorem Vector.get_append_left {xs : Vector α n} {ys : Vector α m} {i : Fin n}
  : (xs.append ys).get ⟨i, Nat.lt_add_right _ i.isLt⟩ = xs.get i := by
  apply List.getElem_append_left

theorem Vector.toList_get {v : Vector α n} {i : Fin n} : v.get i = v.toList.get ⟨i, v.toList_length.symm ▸ i.isLt⟩ := by
  cases v; simp [Vector.get]

theorem Vector.get_append_right {xs : Vector α n} {ys : Vector α m} {i : Fin m}
  : (xs.append ys).get ⟨i + n, by omega⟩ = ys.get i :=
  match xs, ys with
  | ⟨xsl, xeq⟩, ⟨ysl, yeq⟩ => by
    simp [Vector.get]
    have := List.getElem_append_right (i := i + n) xsl ysl
    rw [xeq] at this
    simp at this
    apply this
    omega
    rw [yeq]
    exact i.isLt
