import Spacetalk.Stream
import Spacetalk.Graph

-- Source Lang
namespace Step

------------------ Types ------------------

inductive Ty
  | bitVec : Nat → Ty
deriving DecidableEq

@[reducible]
def Ty.denote : Ty → Type
  | bitVec w => BitVec w

def Ty.default : (t : Ty) → t.denote
  | bitVec _ => 0

instance : Denote Ty where
  denote := Ty.denote
  default := Ty.default

abbrev BitVecTy (w : Nat) := Ty.bitVec w
abbrev BoolTy := BitVecTy 1

------------------ Syntax ------------------

inductive BinaryOp : Ty → Ty → Ty → Type
  | add : {w : Nat} → BinaryOp (BitVecTy w) (BitVecTy w) (BitVecTy w)
  | mul : {w : Nat} → BinaryOp (BitVecTy w) (BitVecTy w) (BitVecTy w)

inductive UnaryOp : Ty → Ty → Type
  | addConst : {w : Nat} → BitVec w → UnaryOp (BitVecTy w) (BitVecTy w)
  | mulConst : {w : Nat} → BitVec w → UnaryOp (BitVecTy w) (BitVecTy w)

inductive Prog : List Ty → Ty → Type
  | const : {α : Ty} → Prog [α] α
  | zip : BinaryOp α β γ → Prog aInp α → Prog bInp β → Prog (aInp ++ bInp) γ
  | map : UnaryOp α β → Prog inp α → Prog inp β
  | reduce : BinaryOp α β α → Nat → α.denote → Prog inp β → Prog inp α

------------------ Semantics ------------------

def BinaryOp.denote : BinaryOp α β γ → α.denote → β.denote → γ.denote
  | BinaryOp.add => BitVec.add
  | BinaryOp.mul => BitVec.mul

def UnaryOp.denote : UnaryOp α β → α.denote → β.denote
  | UnaryOp.addConst c => BitVec.add c
  | UnaryOp.mulConst c => BitVec.mul c

def Prog.denote {inputs : List Ty} {α : Ty} : Prog inputs α → (DenoStreamsList inputs → DenoStreamsList [α])
  | .const => λ ([a]ₕ) ↦ [a]ₕ
  | .zip op as bs => λ inp ↦ let (aInp, bInp) := inp.split; [Stream'.zip op.denote (as.denote aInp).head (bs.denote bInp).head]ₕ
  | .map op as => λ inp ↦ [Stream'.map op.denote (as.denote inp).head]ₕ
  | .reduce op n init bs => λ inp ↦ [Stream'.reduce op.denote n init (bs.denote inp).head]ₕ

------------------ Parser ------------------

declare_syntax_cat step

syntax "const_32" : step
syntax "const_64" : step

syntax:50 step:50 " +z " step:51 : step
syntax:60 step:60 " *z " step:61 : step

syntax:40 term "+r" " start " term " on (" step ") " : step
syntax:40 term "*r" " start " term " on (" step ") " : step

syntax " ( "step " ) " : step

syntax " 〚 " step " 〛 " : term

macro_rules
  | `(〚 const_32 〛) => `(@Prog.const (BitVecTy 32))
  | `(〚 const_64 〛) => `(@Prog.const (BitVecTy 64))
  | `(〚 $a:step +z $b:step 〛) => `(Prog.zip .add 〚 $a 〛 〚 $b 〛)
  | `(〚 $a:step *z $b:step 〛) => `(Prog.zip .mul 〚 $a 〛 〚 $b 〛)
  | `(〚 $n:term +r start $init:term on ($a:step) 〛) => `(Prog.reduce .add $n $init 〚 $a 〛)
  | `(〚 $n:term *r start $init:term on ($a:step) 〛) => `(Prog.reduce .mul $n $init 〚 $a 〛)
  | `(〚 ( $x ) 〛) => `(〚 $x 〛)
  | `(〚 $x 〛) => `(〚 $x 〛)

#check 〚 const_32 +z (10 +r start 0 on ((const_32 +z const_32) *z const_32)) 〛

end Step
