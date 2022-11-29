import data.set data.set.finite

/-!
  # Semantics Language Interface
-/
structure STR(C A : Type) :=
  (initial: set C)
  (actions: C → set A)
  (execute: C → A → set C)

class Evaluate (C E V : Type) :=
  (state : E → C → V)

class Reduce (C R α : Type) :=
  (state : R → C → α)

structure SLI(C A E R V α : Type) :=
  (semantics : STR C A)
  (evaluate: E → C → V)
  (reduce: R → C → α)

/-!
  # Debug semantics
-/
structure DebugConfig (C : Type) :=
  (current : option C)
  (history : set C)
  (options : set C)

inductive DebugAction (C A : Type) 
| step : A → DebugAction
| select : C → DebugAction  
| jump : C → DebugAction 
| run_to_breakpoint : DebugAction

def Finder 
  (C A E R α: Type)
      [has_evaluate: Evaluate C E bool]
      [has_reduce  : Reduce C R α]
       :=
      STR C A → set C → E → R → list C


def rmdInitial (C A : Type) (o : STR C A) : set (DebugConfig C) :=
  {{ current := none, history := ∅, options := o.initial }}

open DebugAction
def rmdActions (C A : Type) (o : STR C A) : DebugConfig C → set (DebugAction C A)
| ⟨ current, history, options ⟩ :=
  let
    oa := { x : DebugAction C A | ∀ c, current = some c → ∀ a ∈ (o.actions c), x = step a    },
    sa := { x : DebugAction C A | ∀ c ∈ options,                               x = select c  },
    ja := { x : DebugAction C A | ∀ c ∈ history,                               x = jump c    }	
	in oa ∪ sa ∪ ja ∪ { run_to_breakpoint }

def rmdExecute (C A E R α: Type)
  [has_evaluate: Evaluate C E bool]
  [has_reduce  : Reduce C R α]
  (o : STR C A) 
  (finder : Finder C A E R α) (breakpoint : E) (reduction : R)
  : 
  DebugConfig C → DebugAction C A → set (DebugConfig C)
| ⟨ (some c), history, _  ⟩ (step a)            := { ⟨ none, history, o.execute c a ⟩ }
| ⟨ (none), _, _ ⟩          (step a)            := ∅ -- cannot get here due to debugActions which produce steps only of current=some c
| ⟨ _, history, _⟩          (select c)          := { ⟨ c, { c } ∪ history, ∅ ⟩ }
| ⟨ _, history, _⟩          (jump c)            := { ⟨ c, { c } ∪ history, ∅ ⟩ }
| ⟨ (some c), history, _  ⟩ (run_to_breakpoint) := 
    match (finder o { c } breakpoint reduction) with 
    | []   := ∅
    | h::t := { ⟨ h, history ∪ { h } ∪ {x | x ∈ t}, ∅ ⟩ }
  end
| ⟨     none, history, opts⟩ (run_to_breakpoint) := 
    match (finder o opts breakpoint reduction) with 
    | []   := ∅
    | h::t := { ⟨ h, history ∪ { h } ∪ {x | x ∈ t}, ∅ ⟩ }
    end

def ReducedMultiverseDebuggerAlone (C A E R α : Type)
  [has_evaluate: Evaluate C E bool]
  [has_reduce  : Reduce C R α]
  (o : STR C A) 
  (finder : Finder C A E R α) 
  (breakpoint : E) 
  (reduction : R) 
  : STR (DebugConfig C) (DebugAction C A) :=
{
  initial :=          rmdInitial C A o,
  actions := λ dc,    rmdActions C A o dc,
  execute := λ dc da, rmdExecute C A E R α o finder breakpoint reduction dc da
}

/-!
  # Replace the initial states of a STR, to make it start somewhere else
-/
def Initialized (C A : Type) (o : STR C A) (initial : set C) : STR C A :=
{ 
  initial := initial,
  actions := o.actions,
  execute := o.execute,
}

/-!
   # Going down to a simple transition relation
-/
structure TR (C : Type) :=
    (initial : set C)
    (next : C -> set C) 
    (accepting : C → bool)

def STR2TR 
    (C A : Type)
    (str : STR C A)
    (accepting : C → bool) 
: TR C  := 
{ 
    initial := str.initial,
    next := λ c, { t | ∀ a ∈ str.actions c, t ∈ str.execute c a },
    accepting := accepting
}


/-! 
  # A bridge from the subject semantics with breakpoints to a transition relation
-/ 
def FinderBridge
  (C A E : Type)
  [has_evaluate: Evaluate C E bool]
  (o : STR C A)       -- underlying STR
  (initial : set C)   -- initial configurations
  (breakpoint : E)    -- the breakpoint
  : TR C := 
    STR2TR C A
      (Initialized C A o initial) 
      (Evaluate.state breakpoint)

def search_accepting (C α : Type) (o : TR C) (reducer : C → α)  : list C := 
  --under-approximating dfs/bfs here
  sorry

/-!
  # The finder function of the multiverse debugger
-/
def FinderFn  
      (C A E R α : Type)
      [has_evaluate: Evaluate C E bool]
      [has_reduce:   Reduce C R α]
       : Finder C A E R α  
    | o initial breakpoint reduction :=  
      (search_accepting C α 
        (FinderBridge C A E o initial breakpoint) 
        (Reduce.state reduction))

/-!
  # The top-level semantics of the debugger
  it needs :
  * a subject semantics
  * a breakpoint
  * an abstraction of C
-/
def ReducedMultiverseDebugger (C A E R α : Type)
  [has_evaluate: Evaluate C E bool]
  [has_reduce:   Reduce C R α]
  (o : STR C A) (breakpoint : E) (reduction : R) 
: STR (DebugConfig C) (DebugAction C A) :=
    ReducedMultiverseDebuggerAlone C A E R α o (FinderFn C A E R α) breakpoint reduction