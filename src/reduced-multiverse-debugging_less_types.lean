import data.set data.set.finite

variables (C A E R V α : Type)

/-!
  # Semantics Language Interface
-/
structure STR :=
  (initial: set C)
  (actions: C → set A)
  (execute: C → A → set C)

-- class Evaluate₀(EE VV : Type) := (state : EE → C → VV)
-- def Evaluate := Evaluate₀ E V
-- def Reduce := Evaluate₀ R α

class Evaluate :=
  (state : E → C → V)

class Reduce :=
  (state : R → C → α)

structure SLI :=
  (semantics : STR C A)
  (evaluate: E → C → V)
  (reduce: R → C → α)

structure SLI' :=
  (semantics:    STR C A)
  (has_evaluate: Evaluate C E V)
  (has_reduce:   Reduce C R α)

/-!
  # Debug semantics
-/



inductive DebugAction
| step : A → DebugAction
| select : C → DebugAction  
| jump : C → DebugAction 
| run_to_breakpoint : DebugAction

def Finder 
  [has_evaluate: Evaluate C E bool]
  [has_reduce:   Reduce C R α]
    :=
  STR C A → set C → E → R → list C


def rmdInitial {C A : Type}
(o : STR C A) : set (DebugConfig C) :=
  {{ current := none, history := ∅, options := o.initial }}

open DebugAction
def rmdActions {C A : Type}
(o : STR C A) : DebugConfig C → set (DebugAction C A)
| ⟨ current, history, options ⟩ :=
  let
    oa := { x : DebugAction C A | ∀ c, current = some c → ∀ a ∈ (o.actions c), x = step a    },
    sa := { x : DebugAction C A | ∀ c ∈ options,                               x = select c  },
    ja := { x : DebugAction C A | ∀ c ∈ history,                               x = jump c    }	
	in oa ∪ sa ∪ ja ∪ { run_to_breakpoint }

def rmdExecute {C A E R α : Type}
  [has_evaluate: Evaluate C E bool]
  [has_reduce  : Reduce C R α]
  (o : STR C A) 
  (finder : Finder C A E R α) (breakpoint : E) (reduction : R)
  : 
  DebugAction C A → DebugConfig C → set (DebugConfig C)
| (step a)            ⟨ (some c), history, _  ⟩  := { ⟨ none, history, o.execute c a ⟩ }
| (step a)            ⟨ (none), _, _ ⟩           := ∅ -- cannot get here due to debugActions which produce steps only of current=some c
| (select c)          ⟨ _, history, _⟩           := { ⟨ c, { c } ∪ history, ∅ ⟩ }
| (jump c)            ⟨ _, history, _⟩           := { ⟨ c, { c } ∪ history, ∅ ⟩ }
| (run_to_breakpoint) ⟨ (some c), history, _  ⟩  := 
    match (finder o { c } breakpoint reduction) with 
    | []   := ∅
    | h::t := { ⟨ h, history ∪ { h } ∪ {x | x ∈ t}, ∅ ⟩ }
  end
| (run_to_breakpoint) ⟨     none, history, opts⟩  := 
    match (finder o opts breakpoint reduction) with 
    | []   := ∅
    | h::t := { ⟨ h, history ∪ { h } ∪ {x | x ∈ t}, ∅ ⟩ }
    end

def ReducedMultiverseDebuggerBridge
  [has_evaluate: Evaluate C E bool]
  [has_reduce  : Reduce C R α]
  (o : STR C A) 
  (finder : Finder C A E R α) 
  (breakpoint : E) 
  (reduction : R) 
  : STR (DebugConfig C) (DebugAction C A) :=
{
  initial :=          rmdInitial o,
  actions := λ dc,    rmdActions o dc,
  execute := λ dc da, rmdExecute o finder breakpoint reduction da dc
}

/-!
  # Replace the initial states of a STR, to make it start somewhere else
-/
def ReplaceInitial (o : STR C A) (initial : set C) : STR C A :=
{ 
  initial := initial,
  actions := o.actions,
  execute := o.execute,
}

/-!
   # Going down to a simple transition relation
-/
structure TR :=
    (initial : set C)
    (next : C -> set C) 
    (accepting : C → bool)

def STR2TR 
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
  [has_evaluate: Evaluate C E bool]
  (o : STR C A)       -- underlying STR
  (initial : set C)   -- initial configurations
  (breakpoint : E)    -- the breakpoint
  : TR C := 
    STR2TR C A
      (ReplaceInitial C A o initial) 
      (Evaluate.state breakpoint)

def search_breakpoint (C α : Type) (o : TR C) (reducer : C → α)  : list C := 
  --under-approximating dfs/bfs here
  sorry

-- def search_breakpoint(o: TR C) (reduce: C → α): list C :=
--     k = {}
--     wt = ()
--     for s ∈ o.initial do
--         if dfs o reduce s k wt then return wt end if
--     end for
--     return wt

-- def dfs (o: TR C) (reduce: C → α) 
-- (s: C) (k: set C) (wt: list C): bool :=
--     if o.accepting s then 
--         wt = wt.append(s)
--         return true
--     end if
--     k = k ∪ { s }
--     for t ∈ o.next s do
--         if (reduce t) ∉ k then
--             if dfs o red t k wt then
--                 wt = wt.append(s)
--                 return true 
--             end if
--         end if
--     end for
--     return false
-- end 

/-!
  # The finder function of the multiverse debugger
-/
def FinderFn  
      [has_evaluate: Evaluate C E bool]
      [has_reduce:   Reduce C R α]
       : Finder C A E R α  
    | o initial breakpoint reduction :=  
      (search_breakpoint C α 
        (FinderBridge C A E o initial breakpoint) 
        (Reduce.state reduction))

/-!
  # The top-level semantics of the debugger
  it needs :
  * a subject semantics
  * a breakpoint
  * an abstraction of C
-/
def ReducedMultiverseDebugger
  [has_evaluate: Evaluate C E bool]
  [has_reduce:   Reduce C R α]
  (o : STR C A) (breakpoint : E) (reduction : R) 
: STR (DebugConfig C) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A E R α o (FinderFn C A E R α) breakpoint reduction