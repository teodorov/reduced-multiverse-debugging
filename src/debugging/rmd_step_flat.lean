import data.set.basic
import sli.sli model_checking.mc_bridge debugging.rmd_bridge 
 composition.synchronous debugging.rmd_search

namespace rmd_step
universe u
variables {S C A E𝕔 E𝕤 R V α : Type}

open sli
open sli.toTR
open model_checking
open rmd_bridge
open rmd_search

/-! 
  # A bridge from the subject semantics with breakpoints to a transition relation
  The breakpoint is a **temporal** step-based 
-/ 
open composition
def FinderFnTemporalStep'' {C₂ A₂ BE E𝕔: Type}
  [h: ∀ actions : set (C × MaybeStutter A × C), decidable (actions = ∅)]
  [has_evaluate: Evaluate C A bool E𝕔 E𝕤]
  [has_reduce:   Reduce (C×C₂) R α]
  (
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E𝕤 (Step C A) bool (has_evaluate.step))  -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      × EmptinessChecker (C × C₂) α 
  )
    : Finder C A R BE 
| o initial breakpoint reduction :=  
let 
  (istr, accepting, search_breakpoint) := inject breakpoint 
in
  (list.map
    (λ (c: C × C₂), match c with | (c₁, c₂) := c₁ end) 
    (search_breakpoint
      (@STR2TR (C×C₂) (MaybeStutter A×A₂)
        (StepSynchronousComposition (ReplaceInitial C A o initial) (istr)) 
        (λ c, accepting c.2))
      (Reduce.state reduction))
)

def TemporalStepRMD {BE C₂ A₂: Type}
  [decidable_eq C]
  [∀ actions : set (C × MaybeStutter A × C), decidable (actions = ∅)]
  [has_evaluate: Evaluate C A bool E𝕔 E𝕤]
  [has_reduce:   Reduce (C × C₂) R α]
  [
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E𝕤 (Step C A) bool (has_evaluate.step))  -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      × EmptinessChecker (C × C₂) α 
  ]
 := ReducedMultiverseDebugger S C A R (FinderFnTemporalStep'' inject)

end rmd_step