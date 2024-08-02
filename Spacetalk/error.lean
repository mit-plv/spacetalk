import Mathlib.Data.Vector.Defs
open Mathlib

inductive EdgeType {n : Nat} (self target : Fin n) where
  | forward : target < self → EdgeType self target
  | initialized : (value : Nat) -> EdgeType self target

structure Edge (n : Nat) where
  self : Fin n
  target : Fin n
  type : EdgeType self target

def graphTraversal {n : Nat} (nodes : Vector Nat n) (edges : List (Edge n)) (acc : Nat) : Nat → Fin n → Nat :=
  λ iter start =>
    match hm : edges.find? (·.self = start) with
    | .some edge =>
      match edge.type with
      | .forward h =>
        have h_decide := List.find?_some hm
        have h_eq := of_decide_eq_true h_decide
        have decreasing : edge.target < start := h_eq ▸ h
        graphTraversal nodes edges acc iter edge.target
      | .initialized v =>
        match iter with
        | 0 => acc + v
        | n' + 1 => graphTraversal nodes edges (acc + v) n' edge.target
    | none => 0

theorem graphTraversal_zero {n : Nat} (nodes : Vector Nat n) (edges : List (Edge n))
  : graphTraversal nodes edges acc 0 =
  (
    λ start =>
      match edges.find? (·.self = start) with
      | .some edge =>
        match edge.type with
        | .forward _ => graphTraversal nodes edges acc 0 edge.target
        | .initialized v => acc + v
      | none => 0
  ) := by
  rw [graphTraversal.eq_def]
  sorry
