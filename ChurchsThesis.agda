module ChurchsThesis where

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

open import NegativeResizing
open import PartialElements
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import Util.HasUnderlyingType
open import Util.ModalOperatorInstances.PropTruncation

private variable
  ℓ : Level

isJust : {A : Type ℓ} → Maybe A → Type
isJust nothing = ⊥
isJust (just x) = Unit

postulate
  φ₀ : ℕ → ℕ → ℕ → Maybe ℕ -- φ₀ e n k = output of eth Turing on input n in k steps
  φ₀-haltsOnce : (e n : ℕ) → (k k' : ℕ) → (isJust (φ₀ e n k)) → (isJust (φ₀ e n k')) → k ≡ k'

φ : ℕ → ℕ → ∂ ℕ
∂.is-this (φ e n) m = ¬¬resize (Σ[ k ∈ ℕ ] (φ₀ e n k ≡ just m))
∂.well-defd (φ e n) m m' u v = do
  (k , p) ← ¬¬resize-out u
  (k' , p') ← ¬¬resize-out v
  let q = φ₀-haltsOnce e n k k' (subst isJust (sym p) tt) (subst isJust (sym p') tt)
  ¬¬-in (just-inj _ _ (sym p ∙∙ cong (φ₀ e n) q ∙∙ p'))

postulate
  ECT : (f : ℕ → ∂ ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → f n ↓ → φ e n ≡ f n) ∥₁

CT : (f : ℕ → ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → φ e n ↓= f n) ∥₁
CT f = do
  (e , p) ← ECT (ι ∘ f)
  ∣ e , (λ n → ≡compose↓= (p n (ιdefd (f n))) (ιIs (f n))) ∣₁

--fast : ℕ → ∇ ℕ
--fast ℕ = 
