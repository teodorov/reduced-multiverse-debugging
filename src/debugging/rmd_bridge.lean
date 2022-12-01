import sli.sli model_checking.mc_bridge

namespace rmd_bridge
universe u
/-!
  **S** the type of a specification (the model that is interpreted by the STR)
    - if it is a string, then we have an inject function String → STR C A that will parse the string and instantiate the STR
    - if it is an program AST, the we have an inject function AST → STR C A that will instantiate the STR with the program AST
    - more generaly it can be any object type S for which we have an inject function S → STR C A
-/
variables (S C A E R V α : Type)

open sli
open sli.toTR
open model_checking

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

structure DebugConfig :=
  (current : option (TraceEntry C A))
  (history : set (TraceEntry C A))
  (options : option(DebugAction C A × set C))

/-!
  **BE** breakpoint expression type, which can be mapped to the semantics and the emptiness checking algorithm needed
  **Cp** configuration product, a configuration type, which in general is different from C. 
    In practice it is the tuple (C, C₂), where C₂ is the configuration type needed by the breakpoint semantics
-/
def Finder (BE: Type)
:=
  STR C A → set C → BE → R → list C

def ote2c {C A : Type} : option (TraceEntry C A) → option C
| none := none
| (some (TraceEntry.root c _)) :=  c
| (some (TraceEntry.child c _ _)) := c

def rmdInitial
(o : STR C A) : set (DebugConfig C A) := 
  { { current := none, history := ∅, options := some (DebugAction.init, o.initial) } }

open DebugAction
def rmdActions
(o : STR C A) : DebugConfig C A → set (DebugAction C A) 
| ⟨ current, history, options ⟩ :=
  let
    oa := { x : DebugAction C A | ∀ c, (ote2c current) = some c → ∀ a ∈ (o.actions c), x = step a }, 
    sa := { x : DebugAction C A | match options with | some (_, configs) := ∀ c ∈ configs, x = select c | none := false end },
    ja := { x : DebugAction C A | ∀ te ∈ history,                               x = jump te    },
    rtb := { x : DebugAction C A | match current with | some te := x = run_to_breakpoint | none := false end }
	in oa ∪ sa ∪ ja ∪ rtb

def same_configuration [decidable_eq C]: TraceEntry C A → C → bool
| (TraceEntry.root  c₁ _  ) c₂ := c₁ = c₂
| (TraceEntry.child c₁ _ _) c₂ := c₁ = c₂

/-!
  Attention:
- to the order of configurations in the counter example (start .. end) vs (end .. start). 
  Here we suppose **(start .. end)**
- does the counter exemple contain the start configuration ?
  The same_configuration check removes the consecutive duplicates
-/
def trace2history {C A : Type} [decidable_eq C] : TraceEntry C A → DebugAction C A → list C → set (TraceEntry  C A) → TraceEntry C A × set (TraceEntry  C A)
| te da [] history := (te, history)
| te da (head::tail) history := 
  let
    te' := if (same_configuration C A te head) then te else (TraceEntry.child head da te),
    h := history ∪ { te' }
  in 
   trace2history te da tail h

def te2c {C A : Type} : TraceEntry C A → C
|  (TraceEntry.root c _) :=  c
|  (TraceEntry.child c _ _):= c


def rmdExecute {BE: Type}
  [decidable_eq C]
  (o : STR C A) 
  (finder : Finder C A R BE) (breakpoint : BE) (reduction : R)
  : 
  DebugAction C A → DebugConfig  C A → set (DebugConfig C A)
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
  


def ReducedMultiverseDebuggerBridge {BE: Type}
  [decidable_eq C]
  (o : STR C A) 
  (finder : Finder C A R BE) 
  (breakpoint : BE) 
  (reduction : R) 
  : STR (DebugConfig C A) (DebugAction C A) :=
{
  initial :=          rmdInitial C A o,
  actions := λ dc,    rmdActions C A o dc,
  execute := λ dc da, rmdExecute C A R o finder breakpoint reduction da dc
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


def ReducedMultiverseDebugger {BE: Type}
  [decidable_eq C]
  (finder : Finder C A R BE)
  (inject: S → STR C A)
  (specification: S)
  (breakpoint : BE) (reduction : R) 
: STR (DebugConfig C A) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A R (inject specification)
      finder breakpoint reduction

end rmd_bridge