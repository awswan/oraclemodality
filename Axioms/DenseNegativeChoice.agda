open import Includes

open import PartialElements
open import DoubleNegationSheaves

open import Cubical.HITs.PropositionalTruncation

module Axioms.DenseNegativeChoice where

postulate
  dnc : (N : ∇ ℕ) (C : N ↓ → Type ℓ) → ((s : N ↓) → ∥ C s ∥₁) → ∥ ((s : N ↓) → C s) ∥₁


