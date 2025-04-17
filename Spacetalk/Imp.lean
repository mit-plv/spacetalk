
inductive Ty
  | unit
  | bool
  | nat

inductive Imp (C M : Ty → Type) : Ty → Type
  | const (n : Nat) : Imp C M .nat
  | var (v : C α) : Imp C M α
  | alloc (init : Imp C M α) (body : M α → Imp C M β) : Imp C M β
  | read (v : M α) : Imp C M α
  | write (v : M α) (e : Imp C M α) : Imp C M .unit
  | add (arg1 arg2 : Imp C M .nat) : Imp C M .nat
  | seq (e1 : Imp C M α) (e2 : Imp C M β) : Imp C M β
  | for_ (start stop : Imp C M .nat) (body : C .nat → Imp C M .unit) : Imp C M .unit

@[simp, reducible]
def Ty.denote : Ty → Type
| unit => Unit
| bool => Bool
| nat => Nat

inductive Ref
  | unit
  | bool (b : Bool)
  | nat (n : Nat)

def mkRef {t : Ty} (v : t.denote) : Ref :=
  match t with
  | .unit => .unit
  | .bool => .bool v
  | .nat => .nat v

abbrev Store := List Ref

def Imp.denote {t : Ty} : Imp Ty.denote (λ _ ↦ Nat) t → StateT Store Option t.denote
| const n => pure n
| var v => pure v
| alloc val body => do
  let val ← val.denote
  let store ← .get
  .set (store.concat (mkRef val))
  (body store.length).denote
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
| add e1 e2 => do
  let x ← e1.denote
  let y ← e1.denote
  pure (x + y)
| seq e1 e2 => do
  let _ ← e1.denote
  e2.denote
| for_ start stop body => do
  let start ← start.denote
  let stop ← stop.denote
  let _ ← (List.range' start stop).forM (λ idx => (body idx).denote)
  pure ()
