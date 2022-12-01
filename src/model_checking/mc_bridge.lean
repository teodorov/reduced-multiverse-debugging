import sli.sli composition.synchronous
namespace model_checking

open sli
open sli.toTR
open composition

def ModelCheckingStateBridge
  (C₁ C₂ A₁ A₂ E : Type)
  [eval : Evaluate C₁ A₁ E bool]
  [h :  (∀ S : set (A₁ × C₁), decidable (S = ∅))]
  (lhs : STR C₁ A₁)
  (accepting₁ : C₁ → bool)
  (rhs : iSTR C₂ A₂ E C₁ bool eval.state)
  (accepting₂ : C₂ → bool)
  : TR (option C₁ × C₂) :=
    STR2TR 
      (StateSynchronousComposition lhs rhs) 
      (λ c, match c.1 with 
            | none := accepting₂ c.2 
            | some c₁ := accepting₁ c₁ ∧ accepting₂ c.2 
            end)

def ModelCheckingStepBridge
  (C₁ C₂ A₁ A₂ E : Type)
  [eval : Evaluate C₁ A₁ E bool]
  [h :  (∀ actions : set (C₁ × (MaybeStutter A₁) × C₁), decidable (actions = ∅))]
  (lhs : STR C₁ A₁)
  (accepting₁ : C₁ → bool)
  (rhs : iSTR C₂ A₂ E (Step C₁ A₁) bool eval.step)
  (accepting₂ : C₂ → bool)
  : TR (C₁ × C₂) :=
    STR2TR 
      (StepSynchronousComposition lhs rhs) 
      (λ c, accepting₁ c.1 ∧ accepting₂ c.2)

end model_checking