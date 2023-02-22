# Temporal Multiverse Debugging

This repository contains the lean3 formalization of **Temporal Multiverse Debugging** (TMD) a new debugging architecture, which threats the breakpoints as a language component.

This formalization also integrates the *user-defined reductions* proposed in [[1]](#1).

## Structure of the repository

The repository is organized as follows:

- The [SLI](src/sli/) folder contains the semantic language interface (SLI) formalization with its extension for handling dependent semantics.
- The [composition](src/composition/) folder contains the definition of two synchronous composition operators, which bridge the gap between the subject language and the breakpoint language.
- The [debugging](src/debugging/) folder contains the core debugger formalization
  - The core multiverse debugger semantics is defined in the [rmd_bridge](src/debugging/rmd_bridge.lean) file.
  - The other files define different breakpoint finder functions
    - [rmd_predicate](src/debugging/rmd_predicate.lean) defines predicate breakpoints as presented in [[1]](#1).
    - [rmd_state](src/debugging/rmd_state.lean) defines state-based temporal breakpoints, the atomic propositions are evaluated only on configurations.
    - [rmd_step](src/debugging/rmd_step.lean) defines step-based temporal breakpoints, the atomic propositions are evaluated on execution steps (source, action, target).
- The [model_checking](src/model_checking/) folder contains a bridge for model-checking
- The [models_22](src/models_22/) folder contains the formalization from [[1]](#1).

## References

<a id="1">[1]</a>
Practical multiverse debugging through user-defined reductions. Pasquier, Matthias,  Teodorov, Ciprian, Jouault, Frédéric, Brun, Matthias, Roux, Luka Le, and Lagadec, Loïc
*In MODELS ’22: ACM/IEEE 25th International Conference on Model Driven Engineering Languages and Systems*, Montreal, Canada, Oct 2022
