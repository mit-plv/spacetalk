
inductive Ty
  | unit
  | bool
  | nat

@[simp, reducible]
def Ty.denote : Ty → Type
  | unit => Unit
  | bool => Bool
  | nat => Nat

inductive BinOp : Ty → Ty → Ty → Type
  | add : BinOp .nat .nat .nat
  | mul : BinOp .nat .nat .nat

def BinOp.denote : BinOp α β γ → α.denote → β.denote → γ.denote
  | add => Nat.add
  | mul => Nat.mul

inductive Mem (rep : Ty → Type) : Ty → Type
  | const (n : Nat) : Mem rep .nat
  | alloc (init : α.denote) (body : rep α → Mem rep β) : Mem rep β
  | read (v : rep α) : Mem rep α
  | write (v : rep α) (e : Mem rep α) : Mem rep .unit
  | binop (op : BinOp α β γ) (arg1 : Mem rep α) (arg2 : Mem rep β) : Mem rep γ
  | seq (e1 : Mem rep α) (e2 : Mem rep β) : Mem rep β

inductive Ref
  | unit
  | bool (b : Bool)
  | nat (n : Nat)
deriving Repr

def mkRef {t : Ty} (v : t.denote) : Ref :=
  match t with
  | .unit => .unit
  | .bool => .bool v
  | .nat => .nat v

abbrev Store := List Ref

def Mem.denote {t : Ty} : Mem (λ _ ↦ Nat) t → StateT Store Option t.denote
  | const n => pure n
  | alloc val body => do
    let store ← .get
    .set (store.concat (mkRef val))
    let res ← (body store.length).denote
    .modifyGet λ store =>
    (res, store.dropLast)
  | read idx => do
    let store ← .get
    let ref ← store[idx]?
    match t, ref with
    | .unit, .unit => pure ()
    | .bool, .bool b => pure b
    | .nat, .nat n => pure n
    | _, _ => none
  | write idx e => do
    let store ← .get
    let val ← e.denote
    .set (store.set idx (mkRef val))
  | binop op e1 e2 => do
    let x ← e1.denote
    let y ← e2.denote
    pure (op.denote x y)
  | seq e1 e2 => do
    let _ ← e1.denote
    e2.denote
