namespace sli
universe u

/-!
  # Variables
  - **C** configuration
  - **A** action
  - **E** diagnosis expression
  - **R** reduction expression
  - **α** the target type of the reduction
-/
variables (C A E R V α : Type)

/-!
  # Semantics Language Interface
-/
structure STR :=
  (initial: set C)
  (actions:     C → set A)
  (execute: A → C → set C)

structure iSTR (C A E I V: Type) (eval : E → I → V) :=
  (initial:             set C)
  (actions:     I → C → set A)
  (execute: A → I → C → set C)

inductive MaybeStutter (A : Type)
| stutter : MaybeStutter
| enabled (val : A) : MaybeStutter
open MaybeStutter
def Step (C A : Type) := (C × MaybeStutter A × C)

class Evaluate :=
  (state : E → C → V)
  (step : E → (C × MaybeStutter A × C) → V)

class Reduce :=
  (state : R → C → α)

namespace toTR

/-!
   # Going down to a simple transition relation
-/
structure TR :=
    (initial : set C)
    (next : C -> set C) 
    (accepting : C → bool)

def STR2TR 
    {C A : Type}
    (str : STR C A)
    (accepting : C → bool) 
: TR C  := 
{ 
    initial := { c | c ∈ str.initial },
    next := λ c, { t | ∀ a ∈ (str.actions c), t ∈ str.execute a c },
    accepting := accepting
}

end toTR

end sli