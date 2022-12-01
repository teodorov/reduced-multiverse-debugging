import sli.sli model_checking.mc_bridge debugging.rmd_bridge debugging.rmd_search

namespace rmd_state
universe u
variables (C A E R V α : Type)

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
  [has_evaluate: Evaluate C A E bool]
  [h : ∀ (S : set (A × C)), decidable (S = ∅)]
  [
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E C bool (has_evaluate.state)) -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
  ]
  (o : STR C A)       -- underlying STR
  (initial : set C)   -- initial configurations
  (breakpoint : BE)    
  : TR ( option C × C₂) := 
    let 
      (istr, accepting) := inject breakpoint 
    in
      ModelCheckingStateBridge C C₂ A A₂ E 
        (ReplaceInitial C A o initial)
        (λ c, true)
        istr
        accepting

def FinderFnTemporalState {C₂ A₂ BE: Type}
      [has_evaluate: Evaluate C A E bool]
      [has_reduce:   Reduce (option C×C₂) R α]
      [h: Π (S : set (A × C)), decidable (S = ∅)]
      (
        inject : BE →                                             -- le model (code, expression) du breakpoint
            (iSTR C₂ A₂ E C bool (has_evaluate.state))           -- semantique du breakpoint
          × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      )
       : Finder C A E R α BE (option C × C₂)  
    | o initial breakpoint reduction :=  
    list.filter_map
    (λ c: option C × C₂, match c with (c₁, c₂) := c₁ end )
    (
        (search_breakpoint (option C × C₂) α 
          (@FinderBridgeTemporalState C A E C₂ A₂ BE has_evaluate h inject o initial breakpoint) 
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
  [has_evaluate: Evaluate C A E bool]
  [has_reduce:   Reduce (option C × C₂) R α]
  [h: ∀ (S : set (A × C)), decidable (S = ∅)]
  (
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E C bool (has_evaluate.state))  -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
  )
  (o : STR C A) (breakpoint : BE) (reduction : R) 
: STR (DebugConfig C A) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A E R α o 
      (FinderFnTemporalState C A E R α inject) breakpoint reduction

def TemporalStateRMD {BE C₂ A₂: Type}
  [has_evaluate: Evaluate C A E bool]
  [has_reduce:   Reduce (option C × C₂) R α]
  [h: ∀ (S : set (A × C)), decidable (S = ∅)]
  [
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E C bool (has_evaluate.state))  -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
  ]
 := ReducedMultiverseDebugger C A E R α (FinderFnTemporalState C A E R α inject)

end rmd_state