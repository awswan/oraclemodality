module FixedPoint where

open import Includes hiding (_≤_)

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Functions.Surjection

open import Util.StablePartial
open import Util.PartialElements

open import Axioms.ChurchsThesis

record PosetStr (P : Type) : Type (ℓ-suc ℓ-zero) where
  field
    _≤_ : P → P → Type

open PosetStr ⦃...⦄ public

instance
  ∂ℕPoset : PosetStr (∂ ℕ)
  PosetStr._≤_ ∂ℕPoset μ ν =
    (m : μ ↓) → ν ↓= ∂.value μ m

  PointwisePoset : {X Y : Type} ⦃ XPoset : PosetStr X ⦄ → PosetStr (Y → X)
  PosetStr._≤_ (PointwisePoset {Y = Y}) f g = (y : Y) → f y ≤ g y
  
ECT≤ : (f : ℕ → ∂ ℕ) → ∥ (Σ[ e ∈ ℕ ] f ≤ φ e) ∥₁
ECT≤ = ECT

module Fixed {X Y : Type} ⦃ PosetY : PosetStr Y ⦄
  (s : X → (X → Y)) (sDense : (f : X → Y) → ∥ Σ[ x₀ ∈ X ] ((x : X) → f x ≤ s x₀ x) ∥₁)
  (F : Y → Y) where
  
  t : X → Y
  t x = F (s x x)
  
  ifMonotone : ((x y : Y) → x ≤ y → F x ≤ F y) → ∥ Σ[ y ∈ Y ] F y ≤ y ∥₁
  ifMonotone monotoneF = map (λ (x₀ , p) → (t x₀) , monotoneF _ _ (p x₀)) (sDense t)
  
  ifMaximal : ((x y : Y) → F x ≤ y → F x ≡ y) → ∥ Σ[ y ∈ Y ] F y ≡ y ∥₁
  ifMaximal maximalF = map (λ (x₀ , p) → s x₀ x₀ , maximalF _ _ (p x₀)) (sDense t)
