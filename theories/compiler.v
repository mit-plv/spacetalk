From Coq Require Import Unicode.Utf8.
Require Import ExtLib.Structures.Monad.


CoInductive ctree {E : Type → Type} {R : Type} : Type :=
| ret : R → ctree
| tau : ctree → ctree
| vis {X} : E X → (X → ctree) → ctree
| zero : ctree
| choice : ctree → ctree → ctree.

Infix "⊕" := choice (at level 80, right associativity).

Arguments ctree : clear implicits.

CoFixpoint ctree_bind {E} {R1 R2} (ct : ctree E R1) (f : R1 → ctree E R2) : ctree E R2 :=
match ct with
| ret v => f v
| tau ct => tau (ctree_bind ct f)
| vis e k => vis e (λ x, ctree_bind (k x) f)
| zero => zero
| p ⊕ q => (ctree_bind p f) ⊕ (ctree_bind q f)
end.

Instance ctree_Monad {E} : Monad (ctree E) :=
{
    ret _ v := ret v;
    bind _ _ ct f := ctree_bind ct f
}.
