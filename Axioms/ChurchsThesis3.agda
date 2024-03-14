module Axioms.ChurchsThesis3 where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Includes

open import Axioms.MarkovInduction
open import Axioms.NegativeResizing
open import Util.StablePartial
open import Util.PartialElements
open import Util.Everything

open import Axioms.ChurchsThesis

postulate
  ECT2 :
    (dom : ℕ → Ω¬¬)
    (X : (n : ℕ) → ⟨ dom n ⟩ → ℕ → Ω¬¬) →
    (f : (n : ℕ) → (d : ⟨ dom n ⟩) → ∥ Σ[ m ∈ ℕ ] [ X n d m ] ∥₁) →
    ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (d : ⟨ dom n ⟩) → Σ[ c ∈ φ-domain e n ] [ X n d (φ-fromDomain e n c) ]) ∥₁


