import sli.sli model_checking.mc_bridge debugging.rmd_bridge debugging.rmd_search

namespace rmd_predicate
universe u
variables (S C A E R V α : Type)

open sli
open sli.toTR
open model_checking
open rmd_bridge
open rmd_search

/-! 
  # A bridge from the subject semantics with breakpoints to a transition relation
  The breakpoint is a simple state **predicate**
-/ 
def FinderBridgePredicate
  (o : STR C A)       -- underlying STR
  (initial : set C)   -- initial configurations
  (accepting : C → bool)    -- the breakpoint
  : TR C := 
    STR2TR
      (ReplaceInitial C A o initial) 
      accepting

/-!
  # The finder function of the multiverse debugger
-/
def FinderFnPredicate  
      [has_evaluate: Evaluate C A E bool]
      [has_reduce:   Reduce C R α]
      (
        inject : E →                                             -- le model (code, expression) du breakpoint
                    (C → bool)
                  × EmptinessChecker C α 
      )
       : Finder C A E R α E C
    | o initial breakpoint reduction := 
    let (accepting, search_breakpoint) := inject breakpoint
    in
      (search_breakpoint
        (FinderBridgePredicate C A o initial accepting) 
        (Reduce.state reduction))

/-!
  # The top-level semantics of the debugger
  it needs :
  * a subject semantics
  * a breakpoint
  * an abstraction of C
-/
def TopReducedMultiverseDebuggerPredicate
  [h_C_deq: decidable_eq C]
  [has_evaluate: Evaluate C A E bool]
  [has_reduce:   Reduce C R α]
  (
    inject : E →                                             -- le model (code, expression) du breakpoint
              (C → bool)
              × EmptinessChecker C α 
  )
  (o : STR C A) (breakpoint : E) (reduction : R) 
: STR (DebugConfig C A) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A E R α o 
      (FinderFnPredicate C A E R α inject) breakpoint reduction


def PredicateRMD
  [h_C_deq: decidable_eq C]
  [has_evaluate: Evaluate C A E bool]
  [has_reduce:   Reduce C R α]
  (
    inject : E →                                             -- le model (code, expression) du breakpoint
              (C → bool) 
              × (EmptinessChecker C α)
  )
 := ReducedMultiverseDebugger S C A E R α (FinderFnPredicate C A E R α inject)


end rmd_predicate