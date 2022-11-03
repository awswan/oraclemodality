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

open import Includes

open import MarkovInduction
open import NegativeResizing
open import StablePartial
open import PartialElements
open import Util.Everything


isJust : {A : Type ℓ} → Maybe A → Type
isJust nothing = ⊥
isJust (just x) = Unit

postulate
  φ₀ : ℕ → ℕ → ℕ → Maybe ℕ -- φ₀ e n k = output of eth Turing on input n in k steps
  φ₀-haltsOnce : (e n : ℕ) → (k k' : ℕ) → (isJust (φ₀ e n k)) → (isJust (φ₀ e n k')) → k ≡ k'

φ-domain : ℕ → ℕ → Type
φ-domain e n = Σ[ (k , m) ∈ ℕ × ℕ ] (φ₀ e n k ≡ just m)

φ-domainStable : (e : ℕ) → (n : ℕ) → Stable (φ-domain e n)
φ-domainStable e n z = ((fst kw) , (fst (snd kw))) , (snd (snd kw))
  where
    kw : Σ[ k ∈ ℕ ] (Σ[ m ∈ ℕ ] (φ₀ e n k ≡ just m))
    kw = markovsPrinciple (λ k → Σ[ m ∈ ℕ ] φ₀ e n k ≡ just m) dec (¬¬-map (λ {((k , m) , p) → k , m , p}) z)
      where
        dec : (k : ℕ) → Dec (Σ[ m ∈ ℕ ] φ₀ e n k ≡ just m)
        dec k with (φ₀ e n k)
        ... | nothing = no (λ {(_ , p) → ¬nothing≡just p})
        ... | just m = yes (m , refl)

φ : ℕ → ℕ → ∂ ℕ
∂.domain (φ e n) = ¬¬resize (φ-domain e n)
∂.value (φ e n) z = snd (fst dom)
  where
    dom : φ-domain e n
    dom = φ-domainStable e n (¬¬resize-out z)
  
postulate
  ECT : (f : ℕ → ∂ ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → f n ↓ → φ e n ≡ f n) ∥₁

CT : (f : ℕ → ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → φ e n ↓= f n) ∥₁
CT f = do
  (e , p) ← ECT (ι ∘ f)
  ∣ e , (λ n → ≡compose↓= (p n (ιdefd (f n))) (ιIs (f n))) ∣₁

