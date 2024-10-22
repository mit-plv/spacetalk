
def BoundedQueue (α : Type u) (len : Nat) :=
  {q : Std.Queue α // q.toArray.size ≤ len}

namespace BoundedQueue

def empty (len : Nat) : BoundedQueue α len :=
  ⟨.empty, by simp [Std.Queue.empty, Std.Queue.toArray]⟩

end BoundedQueue
