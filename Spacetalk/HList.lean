-- import Aesop
-- import Mathlib.Data.List.Basic
-- import Mathlib.Data.List.Infix

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

@[simp]
def Member.compare : Member a as → Member b bs → Bool
  | .head, .head => true
  | .tail a, .tail b => a.compare b
  | _, _ => false

theorem Member.to_mem : Member a l → a ∈ l
  | .head => List.mem_of_mem_head? rfl
  | .tail i => List.mem_of_mem_tail i.to_mem

@[simp]
def Member.append_left {l₁ : List α} {l₂ : List α} : Member a l₁ → Member a (l₁ ++ l₂)
  | .head => .head
  | .tail i' => .tail i'.append_left

@[simp]
def Member.append_right {l₁ : List α} {l₂ : List α} (ia : Member a l₂) : Member a (l₁ ++ l₂) :=
  match l₁ with
  | [] => ia
  | _::_ => .tail ia.append_right

@[simp]
def List.replaceMember {α : Type u} {a : α} : (l : List α) → Member a l → α → List α
  | [], _, _ => []
  | _::t, .head, x => x :: t
  | h::t, .tail m, x => h :: t.replaceMember m x

@[simp]
def List.nthMember : (l : List α) → (n : Fin l.length) → Member (l.get n) l
  | _::_, ⟨0, _⟩ => .head
  | _::t, ⟨n'+1, _⟩ => .tail (t.nthMember ⟨n', _⟩)

namespace HList

  @[simp]
  def length : HList β is → Nat := λ_ ↦ is.length

  @[simp]
  def get : HList β is → Member i is → β i
    | a ::ₕ as, .head => a
    | _ ::ₕ as, .tail h => as.get h

  @[simp]
  def getNth : (l : HList β is) → (n : Fin is.length) → β (is.get n)
    | h ::ₕ _, ⟨0, _⟩ => h
    | _ ::ₕ t, ⟨n + 1, _⟩ => t.getNth ⟨n, _⟩

  @[simp]
  def append (hl₁ : HList β is1) (hl₂ : HList β is2) : HList β (is1 ++ is2) :=
    match hl₁, hl₂ with
    | []ₕ, l => l
    | (h ::ₕ s), t => h ::ₕ s.append t

  @[simp]
  def replace : HList β is → Member i is → β i → HList β is
    | []ₕ, _, _ => []ₕ
    | _::ₕt, .head, x => x ::ₕ t
    | h::ₕt, .tail m, x => h ::ₕ t.replace m x

  @[simp]
  def head : HList β (i::is) → β i
    | h ::ₕ _ => h

  @[simp]
  def tail : HList β (i::is) → HList β is
    | _ ::ₕ t => t

  @[simp]
  def split {α : Type v} {β : α → Type u} {is1 is2 : List α} (hl : HList β (is1 ++ is2)) : HList β is1 × HList β is2 :=
    match is1 with
      | [] => ([]ₕ, hl)
      | _::_ => let (l, r) := hl.tail.split; (hl.head ::ₕ l, r)

  -- def map {α : Type v} {β : α → Type u} {γ : Type w} {δ : γ → Type x} {is : List α}
  --   (f : α → γ) (g : {a : α} → β a → δ (f a)) : HList β is → HList δ (is.map f)
  --   | []ₕ => []ₕ
  --   | h ::ₕ t => g h ::ₕ map f g t

end HList

infixr:67 " ++ₕ " => HList.append

-- Given a List α, a function f : α → β,
-- return a HList with indices of type β and values of β-indexed type δ
-- using the mapping function g : (a : α) → δ (f a).
@[simp]
def List.toHList {α : Type v1} {β : Type v2} {δ : β → Type u}
                  (f : α → β) (g : (a : α) → δ (f a))
                  : (l : List α) → HList δ (l.map f)
  | [] => []ₕ
  | h :: t => g h ::ₕ t.toHList f g
