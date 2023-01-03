module Axioms.NegativeCountableChoice where

open import Includes

postulate
  acℕ¬¬ : (A : ℕ → Type ℓ) → (a : (n : ℕ) → ∥ A n ∥₁) → ¬ ¬ ((n : ℕ) → A n)

