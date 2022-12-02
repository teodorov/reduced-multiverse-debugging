import data.set.basic
import sli.sli
namespace composition
universe u


/-!
  # Composition for model-checking and finder
-/
open prod
open sli
open sli.MaybeStutter
def StateSynchronousComposition 
  {C₁ C₂ A₁ A₂ E : Type}
  [∀ S : set (A₁ × C₁), decidable (S = ∅)]
  [eval : Evaluate C₁ A₁ E bool]
  (lhs : STR C₁ A₁)
  (rhs : iSTR C₂ A₂ E C₁ bool eval.state)
 : STR (option C₁ × C₂) (option (MaybeStutter A₁) × A₂) := 
 {
   initial := {c | ∀ (c₂ ∈ rhs.initial), c = (none, c₂)},
   actions := λ c, match c with 
    | (none, c₂)      := { a | ∀ (t₁ ∈ lhs.initial)
                           (a₂ ∈ rhs.actions t₁ c₂), a = (none, a₂) }
    | (some c₁, c₂)   := let S₁ := { s₁ | ∀ (a₁ ∈ lhs.actions c₁) (t₁ ∈ lhs.execute a₁ c₁), s₁ = (a₁, t₁)}
                          in if (S₁ ≠ ∅) 
                            then { a | ∀ (s₁ ∈ S₁), ∀ (a₂ ∈ rhs.actions (snd s₁) c₂), a = (some (enabled s₁.1), a₂) } 
                            -- add stutter if lhs deadlock
                            else {a | ∀ a₂ ∈ rhs.actions c₁ c₂, a = (some stutter, a₂)}                      
   end,
   execute := λ a c, match a, c with
    -- initial
    | (none, a₂), (none, c₂) := { t | ∀ (t₁ ∈ lhs.initial)
                                       (a₂ ∈ rhs.actions t₁ c₂)
                                       (t₂ ∈ rhs.execute a₂ t₁ c₂), t = (t₁, t₂)}
    -- stutter
    | (some stutter, a₂), (some c₁, c₂) := {t | ∀ t₂ ∈ rhs.execute a₂ c₁ c₂, t = (c₁, t₂)}
    -- normal case
    | (some (enabled a₁), a₂), (some c₁, c₂) := {t | ∀ (t₁ ∈ lhs.execute a₁ c₁) (t₂ ∈ rhs.execute a₂ t₁ c₂), t = (t₁, t₂)} 
    | (none, _), (some _, _) := ∅ -- cannot get here, actions cannot generate this case
    | (some _, _), (none, _) := ∅ -- cannot get here, actions cannot generate this case
   end
 }

def StepSynchronousComposition 
  {C₁ C₂ A₁ A₂ E : Type}
  [∀ actions : set (C₁ × MaybeStutter A₁ × C₁), decidable (actions = ∅)]
  [eval : Evaluate C₁ A₁ E bool]
  (lhs : STR C₁ A₁)
  (rhs : iSTR C₂ A₂ E (Step C₁ A₁) bool eval.step)
  : STR (C₁ × C₂) (MaybeStutter A₁ × A₂) := 
  { 
    initial := { c | ∀ (c₁ ∈ lhs.initial) (c₂ ∈ rhs.initial), c = (c₁, c₂) },
    actions := λ c, 
      match c with
      | (c₁, c₂) := let S₁ := { s₁ | 
                            ∀ (a₁ ∈ lhs.actions c₁) 
                              (t₁ ∈ lhs.execute a₁ c₁), s₁ = (c₁, enabled a₁, t₁)}
                    in if S₁ ≠ ∅
                        then { a | ∀ (s₁ ∈ S₁) (a₂ ∈ rhs.actions s₁ c₂), a = (s₁.2.1, a₂)  }
                        -- add stutter if lhs deadlock
                        else { a | ∀ a₂ ∈ rhs.actions (c₁, stutter, c₁) c₂, a = (stutter, a₂)}
      end,
    execute := λ a c, { t |
      match a, c with 
      | (stutter, a₂), (c₁, c₂) := ∀ t₂ ∈ rhs.execute a₂ (c₁, stutter, c₁) c₂, t = (c₁, t₂)
      | (enabled a₁, a₂), (c₁, c₂) := 
        ∀ (t₁ ∈ lhs.execute a₁ c₁) 
          (t₂ ∈ rhs.execute a₂ (c₁, enabled a₁, t₁) c₂), t = (t₁, t₂)
      end
    }
  }

  end composition