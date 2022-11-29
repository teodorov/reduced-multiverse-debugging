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

mutual inductive TraceEntry , DebugAction
with TraceEntry: Type
| root (c: C) (a: DebugAction) 
| child (c: C) (a: DebugAction) (parent : TraceEntry)
with DebugAction : Type  
| init
| step : A → DebugAction
| select : C → DebugAction  
| jump : TraceEntry → DebugAction 
| run_to_breakpoint : DebugAction

structure DebugConfig₁ :=
  (current : option (TraceEntry C A))
  (history : set (TraceEntry C A))
  (options : option(DebugAction C A × set C))

def Finder 
  [has_evaluate: Evaluate C E bool]
  [has_reduce:   Reduce C R α]
:=
  STR C A → set C → E → R → list C

def ote2c {C A : Type} : option (TraceEntry C A) → option C
| none := none
| (some (TraceEntry.root c _)) :=  c
| (some (TraceEntry.child c _ _)) := c

def rmdInitial {C A : Type}
(o : STR C A) : set (DebugConfig₁ C A) := 
  { { current := none, history := ∅, options := some (DebugAction.init, o.initial) } }

open DebugAction
def rmdActions {C A : Type}
(o : STR C A) : DebugConfig₁ C A → set (DebugAction C A) 
| ⟨ current, history, options ⟩ :=
  let
    oa := { x : DebugAction C A | ∀ c, (ote2c current) = some c → ∀ a ∈ (o.actions c), x = step a }, 
    sa := { x : DebugAction C A | match options with | some (_, configs) := ∀ c ∈ configs, x = select c | none := false end },
    ja := { x : DebugAction C A | ∀ te ∈ history,                               x = jump te    },
    rtb := { x : DebugAction C A | match current with | some te := x = run_to_breakpoint | none := false end }
	in oa ∪ sa ∪ ja ∪ rtb

def trace2history {C A : Type} : TraceEntry C A → DebugAction C A → list C → set (TraceEntry  C A) → TraceEntry C A × set (TraceEntry  C A)
| te da [] history := (te, history)
| te da (head::tail) history := 
  let
    te := (TraceEntry.child head da te),
    h := history ∪ { te }
  in 
   trace2history (TraceEntry.child head da te) da tail h

def te2c {C A : Type} : TraceEntry C A → C
|  (TraceEntry.root c _) :=  c
|  (TraceEntry.child c _ _):= c


def rmdExecute {C A E R α : Type}
  [has_evaluate: Evaluate C E bool]
  [has_reduce  : Reduce C R α]
  (o : STR C A) 
  (finder : Finder C A E R α) (breakpoint : E) (reduction : R)
  : 
  DebugAction C A → DebugConfig₁  C A → set (DebugConfig₁ C A)
| (init) _  :=  ∅ -- cannot get here
| (step a)            ⟨ (some (TraceEntry.root c da)), history, _ ⟩   := { ⟨ (TraceEntry.root c da), history, some (step a, o.execute c a) ⟩ }
| (step a)            ⟨ (some (TraceEntry.child c da p)), history, _⟩ := { ⟨ (TraceEntry.child c da p), history, some (step a, o.execute c a) ⟩ }
| (step a)            ⟨ _, _, _ ⟩                                     := ∅ -- cannot get here due to debugActions which produce steps only of current=some c
| (select c)          ⟨ none, history, some (da, _)⟩                  := (let te := (TraceEntry.root c (@select C A c)) in  { ⟨ te , { te } ∪ history, none ⟩ })
| (select c)          ⟨ some te, history, some(da, _)⟩                := (let te₁ := (TraceEntry.child c (@select C A c) te) in  { ⟨ te₁, { te₁ } ∪ history, none ⟩ })
| (select c)          ⟨ _, _, _ ⟩                                     := ∅ --cannot get here
| (jump te)           ⟨ _, history, _⟩                                := { ⟨ some te, history, none ⟩ }
| (run_to_breakpoint) ⟨ some te, history, opts ⟩                      := 
                                                                          let
                                                                            trace := finder o { (te2c te) } breakpoint reduction,
                                                                            counter := (trace2history te run_to_breakpoint trace ∅)
                                                                          in
                                                                            match counter with 
                                                                            | (te, ch) := { ⟨ some te, history ∪ ch, opts ⟩ }
                                                                            end
| (run_to_breakpoint) ⟨ _, _, _ ⟩                                     := ∅ --cannot get here
  


def ReducedMultiverseDebuggerBridge
  [has_evaluate: Evaluate C E bool]
  [has_reduce  : Reduce C R α]
  (o : STR C A) 
  (finder : Finder C A E R α) 
  (breakpoint : E) 
  (reduction : R) 
  : STR (DebugConfig₁ C A) (DebugAction C A) :=
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
: STR (DebugConfig₁ C A) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A E R α o (FinderFn C A E R α) breakpoint reduction