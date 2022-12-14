import sli.sli model_checking.mc_bridge debugging.rmd_bridge debugging.rmd_search

namespace rmd_state
universe u
variables (S C A E𝕔 E𝕤 R V α : Type)

open sli
open sli.toTR
open model_checking
open rmd_bridge
open rmd_search

/-! 
  # A bridge from the subject semantics with breakpoints to a transition relation
  The breakpoint is a **temporal** state-based 
-/ 

def FinderBridgeTemporalState {C₂ A₂ BE: Type}
  [∀ S : set (A × C), decidable (S = ∅)]
  [has_evaluate: Evaluate C A bool E𝕔 E𝕤]
  (istr: iSTR C₂ A₂ E𝕔 C bool (has_evaluate.configuration)) -- semantique du breakpoint
  (accepting: C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
  (o : STR C A)       -- underlying STR
  (initial : set C)   -- initial configurations
  (breakpoint : BE)    
  : TR ( option C × C₂) := 
    ModelCheckingStateBridge C C₂ A A₂ E𝕔 E𝕤 
      (ReplaceInitial C A o initial)
      (λ c, true)
      istr
      accepting

def FinderFnTemporalState {C₂ A₂ BE: Type}
  [h: ∀ S : set (A × C), decidable (S = ∅)]
  [has_evaluate: Evaluate C A bool E𝕔 E𝕤]
  [has_reduce:   Reduce (option C×C₂) R α]
  (
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E𝕔 C bool (has_evaluate.configuration))           -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      × EmptinessChecker (option C × C₂) α 
  )
    : Finder C A R BE 
| o initial breakpoint reduction :=  
let 
  (istr, accepting, search_breakpoint) := inject breakpoint 
in
  list.filter_map
  (λ c: option C × C₂, match c with (c₁, c₂) := c₁ end )
  (
      (search_breakpoint 
        (@FinderBridgeTemporalState C A E𝕔 E𝕤 C₂ A₂ BE h has_evaluate istr accepting o initial breakpoint) 
        (Reduce.state reduction))
  )

/-!
  # The top-level semantics of the debugger
  it needs :
  * a subject semantics
  * a breakpoint
  * an abstraction of C
-/
def TopReducedMultiverseDebuggerTemporalState {BE C₂ A₂: Type}
  [decidable_eq C]
  [∀ S : set (A × C), decidable (S = ∅)]
  [has_evaluate: Evaluate C A bool E𝕔 E𝕤]
  [has_reduce:   Reduce (option C × C₂) R α]
  (
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E𝕔 C bool (has_evaluate.configuration))  -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      × EmptinessChecker (option C × C₂) α 
  )
  (o : STR C A) (breakpoint : BE) (reduction : R) 
: STR (DebugConfig C A) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A R o 
      (FinderFnTemporalState C A E𝕔 E𝕤 R α inject) breakpoint reduction

def TemporalStateRMD {BE C₂ A₂: Type}
  [decidable_eq C]
  [∀ S : set (A × C), decidable (S = ∅)]
  [has_evaluate: Evaluate C A bool E𝕔 E𝕤]
  [has_reduce:   Reduce (option C × C₂) R α]
  [
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E𝕔 C bool (has_evaluate.configuration))  -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      × EmptinessChecker (option C × C₂) α 
  ]
 := ReducedMultiverseDebugger S C A R (FinderFnTemporalState C A E𝕔 E𝕤 R α inject)

end rmd_state