# Proof of strong normalisation for the AEff language

- The formalisation has been tested with Agda version 2.8.0 and standard library version 2.3.

- The unicode symbols used in the source code have tested to display correctly with the DejaVu Sans Mono font.

- `AEff/` - definition of AEff as in the forked repository and proof that AEffBase simulates AEff

    - `EffectAnnotations.agda` - effect annotations for signals and interrupt handlers

    - `Types.agda` - value, computation, and process types

    - `AEff.agda` - well-typed values, computations, and processes (we do not consider untyped terms)

    - `Renamings.agda` - renamings for values, computations, and processes

    - `Substitutions.agda` - substitutions for values, computations, and processes

    - `Preservation.agda` - small-step operational semantics for computations (also serves as a preservation proof)

    - `Progress.agda` - proof of progress for the small-step operational semantics of computations

    - `ProcessPreservation.agda` - small-step operational semantics for processes (also serves as a preservation proof)

    - `ProcessProgress.agda` - proof of progress for the small-step operational semantics of processes

    - `Finality.agda` - proof that the result forms of computations are final, i.e., they do not reduce further

    - `ProcessFinality.agda` - proof that the result forms of processes are final, i.e., they do not reduce further
    
    - `Simulation.agda` - proof that AEffBase simulates AEff and that AEff is strongly normalising (via this simulation)

- `AEffBaseSN/` - definition of the simplified AEff without effect annotations and a proof of strong normalisation for its sequential part

    - `AEffBaseSN/AEffBase/` - definition of AEffBase (including the parallel part and type safety results; note that they are not used in the normalisation proof)
    
    - `AEffBaseSN/SubstitutionProperties.agda` - proofs of the standard properties of renaming and substitution

    - `AEffBaseSN/StronglyNormalising.agda` - definitions of the strong normalisation predicates and proof that they are equivalent

    - `AEffBaseSN/Continuations.agda` - definition of continuations, their renaming and how they interact with reduction

    - `AEffBaseSN/Main.agda` - definition of reducibility, proofs of the lemmas from the pen-and-paper version and the proof of strong normalisation

- `AEffFinTreeSN/` - definition of AEff with finite interrupt annotations and tree-shaped parallel part and the proof of strong normalisation

    - `AEffFinSN/FiniteEffectAnnotations.agda` - definition of finite (of finite width and height) interrupt annotations and proofs of their properties

    - `AEffFinSN/AEffSequential.agda` - definition of the sequential part of AEffFin

    - `AEffFinSN/AEffParallelTree.agda` - definition of the tree shaped parallel part of AEffFin

    - `AEffFinSN/ParallelShape.agda` - definition of abstract parallel shapes and their reduction, proof that this reduction is terminating

    - `AEffFinSN/StronglyNormalising.agda` - definition of the strong normalisation predicates and proof that they are equivalent

    - `AEffFinSN/Simulation.agda` - proof that AEffBase simulates AEffFin and that the sequential part of AEffFin is strongly normalising

    - `AEffFinSN/Main.agda` - proof of strong normalisation for the tree shaped parallel part of AEffFin

- `AEffFinFlatSN/` - definition of AEff with finite interrupt annotations and flattened parallel part and the proof of strong normalisation

- `AEffReinstSN/` - definition of AEff with reinstallable interrupt handlers (their variant that preserves strong normalisation)
    
    - `AEffReinstBaseSN/` - definition of AEffReinst without interrupt handlers and proof of strong normalisation for it

    - `Simulation.agda` - proof that AEffReinstBase simulates AEff and that the sequential part of AEffReinst is strongly normalising

- `AEffReinstCtxSN/` - variant of reinstallable interrupt handlers without sum and unit types: computations carry a reinstall context (`Γ ∣ ∅ ⊢M⦂ Y` outside handler code, `Γ ∣ re X ⊢M⦂ Y` inside the code of a handler for promises of type `⟨ X ⟩`), and handler code may call `reinstall` (possibly several times, using the returned promise) anywhere except under interrupts (`↓`) or in function bodies (`ƛ`)

    - `AEffReinstCtxBaseSN/` - definition of this calculus (with reinstall substitution and the corresponding trigger rule), its substitution properties, continuations, and the proof of strong normalisation for it

    - `Types.agda`, `AEff.agda`, `Renamings.agda`, `Substitutions.agda`, `Preservation.agda`, `Progress.agda`, `Finality.agda`, `ProcessPreservation.agda`, `ProcessProgress.agda`, `ProcessFinality.agda` - the effect-typed version of this calculus (`Γ ∣ Δ ⊢M⦂ C`, with `reinstall : ⟨ X ⟩ ! (o , i)` in reinstall context `re X (o , i)`), together with its type safety (preservation, progress, finality) for computations and processes

    - `Simulation.agda` - proof that `AEffReinstCtxBaseSN` simulates the effect-typed calculus (erasing effect annotations and coercions) and that the latter's sequential part is strongly normalising

    - `ExamplePreliminaries.agda` - recursive interrupt annotations for reinstallable handlers and the reflexive-transitive closure of reduction, used by the examples

    - `Examples.agda` - examples of reinstallable handlers (a server, an early-reinstall server, pre-emptive threads, nested handlers, a double reinstall) with their recursive effect annotations, and explicit reduction sequences for them

    - `Counterexamples.agda` - proof that the counterexamples to strong normalisation of the design with a first-class reinstall function (reinstall under an interrupt, reinstall leaked in a function) are not erasures of well-typed terms, together with their closest well-typed analogues and their reductions to normal forms
