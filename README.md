# Oracle Modalities

This is the Agda formalisation to accompany the paper *Oracle modalities*.

## Directory layout

The main directory contains the following files:
  * `Includes.agda` Imports modules from the cubical library that are used multiple times
  * `DoubleNegationSheaves.agda` Implementation of 0-truncated double negation sheafification using the classifier for double negation stable propositions and various results about it
  * `OracleModality.agda` Main results about oracle modalities, including their definition, proof of relativised Markov's principle and its applications, definition of Turing degrees
  * `ParallelSearch.agda` parallel unbounded search using relativised Markov's principle
  * `RelativisedCT.agda` coding function used for relativised Church's thesis

`Axioms/` This directory contains files postulating the main axioms that we will be using together with some basic results using the axioms.

  * `NegativeResizing.agda` Postulates a small classifier for all negated types. Contains some basic results allowing us to use it as a classifier for double negation stable propositions
  * `ChurchsThesis.agda` Postulates extended Church's thesis (all partial functions are computable) and derives Church's thesis (all total functions are computable)
  * `MarkovInduction.agda` Markov induction allows us to construct functions that include unbounded search. Includes a derivation of Markov's principle
  * `StableSubcountableChoice.agda` The choice axiom used in one of the sections of the paper

`Util/` Anything used in the formalisation that isn't specifically mentioned in the paper or isn't new
  * `ModalOperatorSugar.agda` load the bind function required for [syntactic sugar](https://agda.readthedocs.io/en/v2.6.2.2/language/syntactic-sugar.html) via [instance resolution](https://agda.readthedocs.io/en/v2.6.2.2/language/instance-arguments.html). Allows us to use `do` notation for anything implementing the `ModalOperator` type
  * `PropositionalTruncationModalOperator.agda` Propositional truncation implements `ModalOperator`
  * `DoubleNegation.agda` Lemmas about double negation including implementation of `ModalOperator`
  * `HasUnderlyingType.agda` Utility function for getting the underlying type of some structure via instance resolution
  * `LexNull.agda` Proof that nullification of a family of propositions is lex
  * `PartialElements.agda` Implementation of partial elements, including notation for any modal operator whose elements can be viewed as partial elements.
  * `StablePartial.agda` Partial elements with double negation stable domain
  * `Everything.agda` Packages commonly used utility functions into a single import


## Installation

We use cubical mode Agda and the cubical Agda library. We need version v0.4 of the [cubical library](https://github.com/agda/cubical), which is currently the most recent release. I recommend version 2.6.2.2 of [Agda](https://agda.readthedocs.io/en/v2.6.2.2/). I have tested it on that version and it is recommended for v0.4 of the library. The library needs to be in the Agda search path, as described at https://agda.readthedocs.io/en/v2.6.2.2/tools/package-system.html.
