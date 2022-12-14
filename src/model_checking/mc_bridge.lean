import sli.sli composition.synchronous
namespace model_checking

open sli
open sli.toTR
open composition

def ModelCheckingStateBridge
  (C₁ C₂ A₁ A₂ E𝕔 E𝕤 : Type)
  [∀ S : set (A₁ × C₁), decidable (S = ∅)]
  [eval : Evaluate C₁ A₁ bool E𝕔 E𝕤]
  (lhs : STR C₁ A₁)
  (accepting₁ : C₁ → bool)
  (rhs : iSTR C₂ A₂ E𝕔 C₁ bool eval.configuration)
  (accepting₂ : C₂ → bool)
  : TR (option C₁ × C₂) :=
    STR2TR 
      (StateSynchronousComposition lhs rhs) 
      (λ c, match c.1 with 
            | none := accepting₂ c.2 
            | some c₁ := accepting₁ c₁ ∧ accepting₂ c.2 
            end)

def ModelCheckingStepBridge
  (C₁ C₂ A₁ A₂ E𝕔 E𝕤 : Type)
  [∀ actions : set (C₁ × MaybeStutter A₁ × C₁), decidable (actions = ∅)]
  [eval : Evaluate C₁ A₁ bool E𝕔 E𝕤]
  (lhs : STR C₁ A₁)
  (accepting₁ : C₁ → bool)
  (rhs : iSTR C₂ A₂ E𝕤 (Step C₁ A₁) bool eval.step)
  (accepting₂ : C₂ → bool)
  : TR (C₁ × C₂) :=
    STR2TR 
      (StepSynchronousComposition lhs rhs) 
      (λ c, accepting₁ c.1 ∧ accepting₂ c.2)

end model_checking