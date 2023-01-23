open import Includes hiding (map)

open import Cubical.HITs.PropositionalTruncation

open import Util.HasUnderlyingType

open import Axioms.NegativeResizing

module Axioms.StableSubcountableChoice where

postulate
  sscc : (P : ℕ → Ω¬¬) → (X : (n : ℕ) → ⟨ P n ⟩ → Type ℓ) → ((n : ℕ) → (z : ⟨ P n ⟩) → ∥ X n z ∥₁) → ∥ ((n : ℕ) → (z : ⟨ P n ⟩) → X n z) ∥₁

cc : (X : ℕ → Type ℓ) → ((n : ℕ) → ∥ X n ∥₁) → ∥ ((n : ℕ) → X n) ∥₁
cc X f = map (λ g n → g n (¬¬resize-in tt)) (sscc (λ _ → ¬¬⊤) (λ n _ → X n) λ n _ → f n)