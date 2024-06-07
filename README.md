# Oracle Modalities

This is the Agda formalisation to accompany the paper A.W. Swan, *Oracle modalities*.

## Directory layout

The main directory contains the following files:
  * `Includes.agda` Imports modules from the cubical library that are used multiple times
  * `DoubleNegationSheaves.agda` Implementation of 0-truncated double negation sheafification using the classifier for double negation stable propositions and various results about it
  * `OracleModality.agda` Main results about oracle modalities, including their definition, proof of relativised Markov's principle and its applications, definition of Turing degrees
  * `ParallelSearch.agda` parallel unbounded search using relativised Markov's principle
  * `RelativisedCC.agda` proof of relativised version of computable choice, with definition of Turing jump as application
  * `WeakTT.agda` a formulation of weak truth table reducibility and proof that Turing reducibility is strictly weaker
  * `Continuity.agda` a local continuity principle for Turing reducibility

`Axioms/` This directory contains files postulating the main axioms that we will be using together with some basic results using the axioms.

  * `NegativeResizing.agda` Postulates a small classifier for all negated types. Contains some basic results allowing us to use it as a classifier for double negation stable propositions
  * `ComputableChoice.agda` Postulates computable choice, derives ECT and CT
  * `MarkovInduction.agda` Markov induction allows us to construct functions that include unbounded search. Includes a derivation of Markov's principle

`Util/` Anything used in the formalisation that isn't specifically mentioned in the paper or isn't new
  * `ModalOperatorSugar.agda` load the bind function required for [syntactic sugar](https://agda.readthedocs.io/en/v2.6.4.3/language/syntactic-sugar.html) via [instance resolution](https://agda.readthedocs.io/en/v2.6.4.3/language/instance-arguments.html). Allows us to use `do` notation for anything implementing the `ModalOperator` type
  * `PropositionalTruncationModalInstance.agda` Propositional truncation implements `ModalOperator`
  * `DoubleNegation.agda` Lemmas about double negation including implementation of `ModalOperator`
  * `HasUnderlyingType.agda` Utility function for getting the underlying type of some structure via instance resolution
  * `Nullification.agda` a couple of useful functions regarding nullification
  * `LexNull.agda` Proof that nullification of a family of propositions is lex
  * `PartialElements.agda` Implementation of partial elements, including notation for any modal operator whose elements can be viewed as partial elements.
  * `StablePartial.agda` Partial elements with double negation stable domain
  * `Nat.agda` Minor utility function on the naturals
  * `List.agda` Utility for universal quantifiers over lists
  * `Misc.agda` Miscellaneous utility functions
  * `Everything.agda` Packages commonly used utility functions into a single import


## Installation

We use cubical mode Agda and the cubical Agda library. We need version v0.7 of the [cubical library](https://github.com/agda/cubical), which requires [Agda](https://agda.readthedocs.io/en/v2.6.4/) 2.6.4 or later. The library needs to be in the Agda search path, as described at https://agda.readthedocs.io/en/v2.6.4.3/tools/package-system.html. These files have been tested and type check correctly with Agda 2.6.4.3 and cubical v0.7.
