import data.set data.set.finite data.list.basic

universe u
variables (C A E R V α : Type)

/-!
  # Semantics Language Interface
-/
structure STR :=
  (initial: set C)
  (actions: C → set A)
  (execute: C → A → set C)

structure iSTR (C A E I V: Type) (eval : E → I → V) :=
  (initial: set C)
  (actions: C → I → set A)
  (execute: C → I → A → set C)


inductive MaybeStutter (α : Type u)
| stutter : MaybeStutter
| enabled (val : α) : MaybeStutter
open MaybeStutter

class Evaluate :=
  (state : E → C → V)
  (step : E → (C × MaybeStutter A × C) → V )

-- def handle_stutter (eval : E → (C × A × C) → V) : E → (C × MaybeStutter A × C) → V 
-- | e (_, MaybeStutter.stutter, _) :=
-- | e (s, (MaybeStutter.enabled a), t) := eval e (s, a, t)

class Reduce :=
  (state : R → C → α)

structure SLI :=
  (semantics:    STR C A)
  (has_evaluate: Evaluate C A E V)
  (has_reduce:   Reduce C R α)

/-!
   # Going down to a simple transition relation
-/
structure TR :=
    (initial : set C)
    (next : C -> set C) 
    (accepting : C → bool)

def STR2TR 
    {C A : Type}
    (str : STR C A)
    (accepting : C → bool) 
: TR C  := 
{ 
    initial := { c | c ∈ str.initial },
    next := λ c, { t | ∀ a ∈ (str.actions c), t ∈ str.execute c a },
    accepting := accepting
}

/-!
  # Composition for model-checking and finder
-/
open prod
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

def Step (C A : Type) := (C × MaybeStutter A × C)
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
  [has_evaluate: Evaluate C A E bool]
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

/-!
  Attention:
- a l'ordre des configurations dans le contre example
- est-ce que le contre example contient la configuration a partir de laquele on a lance le run_to_breakpoint 
  Dans la suite on suppose que contre example renvoye par finder ne contient pas le point de depart
-/
def trace2history {C A : Type} : TraceEntry C A → DebugAction C A → list C → set (TraceEntry  C A) → TraceEntry C A × set (TraceEntry  C A)
| te da [] history := (te, history)
| te da (head::tail) history := 
  let
    te' := (TraceEntry.child head da te),
    h := history ∪ { te' }
  in 
   trace2history te da tail h

def te2c {C A : Type} : TraceEntry C A → C
|  (TraceEntry.root c _) :=  c
|  (TraceEntry.child c _ _):= c


def rmdExecute {C A E R α : Type}
  [has_evaluate: Evaluate C A E bool]
  [has_reduce  : Reduce C R α]
  (o : STR C A) 
  (finder : Finder C A E R α) (breakpoint : E) (reduction : R)
  : 
  DebugAction C A → DebugConfig₁  C A → set (DebugConfig₁ C A)
| (init) _                                                            :=  ∅ -- cannot get here
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
                                                                            patch := trace2history te run_to_breakpoint trace ∅ 
                                                                          in 
                                                                            match patch with 
                                                                            | (te, ch) := { ⟨ some te, history ∪ ch, opts ⟩ } 
                                                                            end
| (run_to_breakpoint) ⟨ _, _, _ ⟩                                     := ∅ --cannot get here
  


def ReducedMultiverseDebuggerBridge
  [has_evaluate: Evaluate C A E bool]
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
  # A bridge from the subject semantics with breakpoints to a transition relation
  The breakpoint is a simple state **predicate**
-/ 
def FinderBridgePredicate
  [has_evaluate: Evaluate C A E bool]
  (o : STR C A)       -- underlying STR
  (initial : set C)   -- initial configurations
  (breakpoint : E)    -- the breakpoint
  : TR C := 
    STR2TR
      (ReplaceInitial C A o initial) 
      (Evaluate.state A breakpoint)

/-! 
  # A bridge from the subject semantics with breakpoints to a transition relation
  The breakpoint is a **temporal** state-based 
-/ 

def FinderBridgeTemporalState {C₁ A₁ E₁ C₂ A₂ BE: Type}
  [has_evaluate: Evaluate C₁ A₁ E₁ bool]
  [h : ∀ (S : set (A₁ × C₁)), decidable (S = ∅)]
  [
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E₁ C₁ bool (has_evaluate.state)) -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
  ]
  (o : STR C₁ A₁)       -- underlying STR
  (initial : set C₁)   -- initial configurations
  (breakpoint : BE)    
  : TR ( option C₁ × C₂) := 
    let 
      (istr, accepting) := inject breakpoint 
    in
      ModelCheckingStateBridge C₁ C₂ A₁  A₂ E₁ 
        (ReplaceInitial C₁ A₁ o initial)
        (λ c, true)
        istr
        accepting

/-! 
  # A bridge from the subject semantics with breakpoints to a transition relation
  The breakpoint is a **temporal** step-based 
-/ 
def FinderBridgeTemporalStep {C₁ A₁ E₁ C₂ A₂ BE: Type}
  [has_evaluate: Evaluate C₁ A₁ E₁ bool]
  [h: ∀ (actions : set (C₁ × MaybeStutter A₁ × C₁)), decidable (actions = ∅)]
  [
    inject : BE →                                             -- le model (code, expression) du breakpoint
        (iSTR C₂ A₂ E₁ (Step C₁ A₁) bool (has_evaluate.step)) -- semantique du breakpoint
      × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
  ]

  (o : STR C₁ A₁)      -- underlying STR
  (initial : set C₁)   -- initial configurations
  (breakpoint : BE)    -- le model (code, expression) du breakpoint
  : TR (C₁ × C₂) := 
    let 
      (istr, accepting) := inject breakpoint 
    in
    ModelCheckingStepBridge C₁ C₂ A₁ A₂ E₁ 
      (ReplaceInitial C₁ A₁ o initial)
      (λ c, true)
      (istr)
      (accepting)


def search_breakpoint (C : Type) (α : Type) (o : TR C) (reducer : C → α)  : list C := 
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
def FinderFnPredicate  
      [has_evaluate: Evaluate C A E bool]
      [has_reduce:   Reduce C R α]
       : Finder C A E R α  
    | o initial breakpoint reduction :=  
      (search_breakpoint C α 
        (FinderBridgePredicate C A E o initial breakpoint) 
        (Reduce.state reduction))

def Finder'' (C₁ C₂ A₁ E BE R α: Type)
  [has_evaluate: Evaluate C₁ A₁ E bool]
  [has_reduce:   Reduce (option C₁×C₂) R α]
:=
  STR C₁ A₁ → set C₁ → BE → R → list C₁

def FinderFnTemporalState {C₁ C₂ A₁ A₂ E BE: Type}
      [has_evaluate: Evaluate C₁ A₁ E bool]
      [has_reduce:   Reduce (option C₁×C₂) R α]
      [h: Π (S : set (A₁ × C₁)), decidable (S = ∅)]
      [
        inject : BE →                                             -- le model (code, expression) du breakpoint
            (iSTR C₂ A₂ E C₁ bool (has_evaluate.state))           -- semantique du breakpoint
          × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      ]
       : Finder'' C₁ C₂ A₁ E BE R α 
    | o initial breakpoint reduction :=  
    list.filter_map
    (λ c: option C₁ × C₂, match c with (c₁, c₂) := c₁ end )
    (
        (search_breakpoint (option C₁ × C₂) α 
          (@FinderBridgeTemporalState C₁ A₁ E C₂ A₂ BE has_evaluate h inject o initial breakpoint) 
          (Reduce.state reduction))
    )

def Finder' (C₁ C₂ A₁ E BE R α: Type)
  [has_evaluate: Evaluate C₁ A₁ E bool]
  [has_reduce:   Reduce (C₁×C₂) R α]
:=
  STR C₁ A₁ → set C₁ → BE → R → list C₁

def FinderFnTemporalStep {C₁ C₂ A₁ A₂ E BE: Type}
      [has_evaluate: Evaluate C₁ A₁ E bool]
      [has_reduce:   Reduce (C₁×C₂) R α]
      [h: ∀ (actions : set (C₁ × MaybeStutter A₁ × C₁)), decidable (actions = ∅)]
      [
        inject : BE →                                             -- le model (code, expression) du breakpoint
            (iSTR C₂ A₂ E (Step C₁ A₁) bool (has_evaluate.step))  -- semantique du breakpoint
          × (C₂ → bool)                                           -- la fonction d'acceptation induite par la semantic de breakpoint
      ]

       : Finder' C₁ C₂ A₁ E BE R α 
    | o initial breakpoint reduction :=  
      (list.map
      (λ (c: C₁ × C₂), match c with | (c₁, c₂) := c₁ end) 
      (search_breakpoint (C₁ × C₂) α
        (@FinderBridgeTemporalStep C₁ A₁ E C₂ A₂ BE has_evaluate h inject o initial breakpoint) 
        (Reduce.state reduction))
      )

/-!
  # The top-level semantics of the debugger
  it needs :
  * a subject semantics
  * a breakpoint
  * an abstraction of C
-/
def ReducedMultiverseDebugger
  [has_evaluate: Evaluate C A E bool]
  [has_reduce:   Reduce C R α]
  (o : STR C A) (breakpoint : E) (reduction : R) 
: STR (DebugConfig₁ C A) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A E R α o (FinderFnPredicate C A E R α) breakpoint reduction