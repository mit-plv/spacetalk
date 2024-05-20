import Aesop
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil : HList β []
  | cons : β i → HList β is → HList β (i::is)

infixr:67 " ::ₕ " => HList.cons
notation "[" "]ₕ" => HList.nil

syntax (priority := high) "[" term,+ "]ₕ" : term

macro_rules
  | `([$x]ₕ) => `(HList.cons $x .nil)
  | `([$x, $xs:term,*]ₕ) => `(HList.cons $x [$xs,*]ₕ)

inductive Member {α : Type u} : α → List α → Type u
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)
deriving BEq, DecidableEq

theorem Member.to_mem : Member a l → a ∈ l
  | .head => List.mem_of_mem_head? rfl
  | .tail i => List.mem_of_mem_tail i.to_mem

def Member.append_left {l₁ : List α} {l₂ : List α} : Member a l₁ → Member a (l₁ ++ l₂)
  | .head => .head
  | .tail i' => .tail i'.append_left

def Member.append_right {l₁ : List α} {l₂ : List α} (ia : Member a l₂) : Member a (l₁ ++ l₂) :=
  match l₁ with
  | [] => ia
  | _::_ => .tail ia.append_right

def List.replaceMember {α : Type u} {a : α} : (l : List α) → Member a l → α → List α
  | [], _, _ => []
  | _::t, .head, x => x :: t
  | h::t, .tail m, x => h :: t.replaceMember m x

def List.nthMember : (l : List α) → (n : Fin l.length) → Member (l.get n) l
  | _::_, ⟨0, _⟩ => .head
  | _::t, ⟨n'+1, _⟩ => .tail (t.nthMember ⟨n', _⟩)

namespace HList

  def length : HList β is → Nat
    | []ₕ => 0
    | _ ::ₕ t => 1 + t.length

  @[simp]
  def get : HList β is → Member i is → β i
    | a ::ₕ as, .head => a
    | _ ::ₕ as, .tail h => as.get h

  def getNth : (l : HList β is) → (n : Fin is.length) → β (is.get n)
    | h ::ₕ _, ⟨0, _⟩ => h
    | _ ::ₕ t, ⟨n + 1, _⟩ => t.getNth ⟨n, _⟩

  def append (hl₁ : HList β is1) (hl₂ : HList β is2) : HList β (is1 ++ is2) :=
    match hl₁, hl₂ with
    | []ₕ, l => l
    | (h ::ₕ s), t => h ::ₕ s.append t

  def replace : HList β is → Member i is → β i → HList β is
    | []ₕ, _, _ => []ₕ
    | _::ₕt, .head, x => x ::ₕ t
    | h::ₕt, .tail m, x => h ::ₕ t.replace m x

  def head : HList β (i::is) → β i
    | h ::ₕ _ => h

  def tail : HList β (i::is) → HList β is
    | _ ::ₕ t => t

  def split {α : Type v} {β : α → Type u} {is1 is2 : List α} (hl : HList β (is1 ++ is2)) : HList β is1 × HList β is2 :=
    match is1 with
      | [] => ([]ₕ, hl)
      | _::_ => let (l, r) := hl.tail.split; (hl.head ::ₕ l, r)

end HList

infixr:67 " ++ₕ " => HList.append

-- Given a List α, a function f : α → β,
-- return a HList with indices of type β and values of β-indexed type δ
-- using the mapping function g : (a : α) → δ (f a).
def List.toHList {α : Type v1} {β : Type v2} {δ : β → Type u}
                  (f : α → β) (g : (a : α) → δ (f a))
                  : (l : List α) → HList δ (l.map f)
  | [] => []ₕ
  | h :: t => g h ::ₕ t.toHList f g
