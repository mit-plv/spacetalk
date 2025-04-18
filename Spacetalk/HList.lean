
inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil : HList β []
  | cons : β i → HList β is → HList β (i::is)

inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

def HList.get : HList β is → Member i is → β i
| .cons a as, .head => a
| .cons _ as, .tail h => as.get h

def HList.split (hl : HList β (as ++ bs)) : HList β as × HList β bs :=
  match as, hl with
  | [], hl => (.nil, hl)
  | _::_, .cons hd tl =>
    let (hd', tl) := tl.split
    (.cons hd hd', tl)
