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
  [eval : Evaluate C₁ A₁ E bool]
  [h :  (∀ S : set (A₁ × C₁), decidable (S = ∅))]
  (lhs : STR C₁ A₁)
  (rhs : iSTR C₂ A₂ E C₁ bool eval.state)
 : STR (option C₁ × C₂) (option (MaybeStutter A₁) × A₂) := 
 {
   initial := {c | ∀ (c₂ ∈ rhs.initial), c = (none, c₂)},
   actions := λ c, match c with 
    | (none, c₂)      := { a | ∀ (t₁ ∈ lhs.initial)
                           (a₂ ∈ rhs.actions c₂ t₁), a = (none, a₂) }
    | (some c₁, c₂)   := let S₁ := { s₁ | ∀ (a₁ ∈ lhs.actions c₁) (t₁ ∈ lhs.execute c₁ a₁), s₁ = (a₁, t₁)}
                          in if (S₁ ≠ ∅)
                            then { a | ∀ (s₁ ∈ S₁), ∀ (a₂ ∈ rhs.actions c₂ (snd s₁)), a = (some (enabled s₁.1), a₂) } 
                            -- add stutter if lhs deadlock
                            else {a | ∀ a₂ ∈ rhs.actions c₂ c₁, a = (some stutter, a₂)}                      
   end,
   execute := λ c a, match c, a with
    -- initial
    | (none, c₂), (none, a₂) := { t | ∀ (t₁ ∈ lhs.initial)
                                       (a₂ ∈ rhs.actions c₂ t₁)
                                       (t₂ ∈ rhs.execute c₂ t₁ a₂), t = (t₁, t₂)}
    -- stutter
    | (some c₁, c₂), (some stutter, a₂) := {t | ∀ t₂ ∈ rhs.execute c₂ c₁ a₂, t = (c₁, t₂)}
    -- normal case
    | (some c₁, c₂), (some (enabled a₁), a₂) := {t | ∀ (t₁ ∈ lhs.execute c₁ a₁) (t₂ ∈ rhs.execute c₂ t₁ a₂), t = (t₁, t₂)} 
    | (some _, _), (none, _) := ∅ -- cannot get here, actions cannot generate this case
    | (none, _), (some _, _) := ∅ -- cannot get here, actions cannot generate this case
   end
   ,
 }

def StepSynchronousComposition 
  {C₁ C₂ A₁ A₂ E : Type}
  [eval : Evaluate C₁ A₁ E bool]
  [h :  (∀ actions : set (C₁ × (MaybeStutter A₁) × C₁), decidable (actions = ∅))]
  (lhs : STR C₁ A₁)
  (rhs : iSTR C₂ A₂ E (Step C₁ A₁) bool eval.step)
  : STR (C₁ × C₂) (MaybeStutter A₁ × A₂) := 
  { 
    initial := { c | ∀ (c₁ ∈ lhs.initial) (c₂ ∈ rhs.initial), c = (c₁, c₂) },
    actions := λ c, 
      match c with
      | (c₁, c₂) := let S₁ := { s₁ | 
                            ∀ (a₁ ∈ lhs.actions c₁) 
                              (t₁ ∈ lhs.execute c₁ a₁), s₁ = (c₁, enabled a₁, t₁)}
                    in if S₁ ≠ ∅
                        then { a | ∀ (s₁ ∈ S₁) (a₂ ∈ rhs.actions c₂ s₁), a = (s₁.2.1, a₂)  }
                        -- add stutter if lhs deadlock
                        else { a | ∀ a₂ ∈ rhs.actions c₂ (c₁, stutter, c₁), a = (stutter, a₂)}
      end,
    execute := λ c a, { t |
      match c, a with 
      | (c₁, c₂), (stutter, a₂) := ∀ t₂ ∈ rhs.execute c₂ (c₁, stutter, c₁) a₂, t = (c₁, t₂)
      | (c₁, c₂), (enabled a₁, a₂) := 
        ∀ (t₁ ∈ lhs.execute c₁ a₁) 
          (t₂ ∈ rhs.execute c₂ (c₁, enabled a₁, t₁) a₂), t = (t₁, t₂)
      end
    }
  }

  end composition