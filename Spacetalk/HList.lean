
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil : HList β []
  | cons : β i → HList β is → HList β (i::is)

infix:67 " :: " => HList.cons

syntax (name := hlist) "[" term,* "]"  : term
macro_rules (kind := hlist)
  | `([ ])           => `(HList.nil)
  | `([ $a ])        => `(HList.cons $a HList.nil)
  | `([ $a, $as,* ]) => `(HList.cons $a [$as,*])

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
| a::as, .head => a
| _::as, .tail h => as.get h

def HList.split (hl : HList β (as ++ bs)) : HList β as × HList β bs :=
  match as, hl with
  | [], hl => (.nil, hl)
  | _::_, hd::tl =>
    let (hd', tl) := tl.split
    (.cons hd hd', tl)
