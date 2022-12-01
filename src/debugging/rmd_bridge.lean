import ..sli.sli ..model_checking.mc_bridge

namespace rmd_bridge
universe u
variables (C A E R V α : Type)

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

def Finder (BE Cp: Type)
  [has_evaluate: Evaluate C A E bool]
  [has_reduce: Reduce Cp R α]
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


def rmdExecute {BE Cp: Type}
  [has_evaluate: Evaluate C A E bool]
  [has_reduce  : Reduce Cp R α]
  (o : STR C A) 
  (finder : Finder C A E R α BE Cp) (breakpoint : BE) (reduction : R)
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
  


def ReducedMultiverseDebuggerBridge {BE Cp: Type}
  [has_evaluate: Evaluate C A E bool]
  [has_reduce  : Reduce Cp R α]
  (o : STR C A) 
  (finder : Finder C A E R α BE Cp) 
  (breakpoint : BE) 
  (reduction : R) 
  : STR (DebugConfig C A) (DebugAction C A) :=
{
  initial :=          rmdInitial C A o,
  actions := λ dc,    rmdActions C A o dc,
  execute := λ dc da, rmdExecute C A E R α o finder breakpoint reduction da dc
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


def ReducedMultiverseDebugger {BE Cp: Type}
  [has_evaluate: Evaluate C A E bool]
  [has_reduce:   Reduce Cp R α]
  (finder : Finder C A E R α BE Cp)
  (o : STR C A)
  (breakpoint : BE) (reduction : R) 
: STR (DebugConfig C A) (DebugAction C A) :=
    ReducedMultiverseDebuggerBridge C A E R α o 
      finder breakpoint reduction

end rmd_bridge