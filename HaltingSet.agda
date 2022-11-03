module HaltingSet where

open import Includes
open import Util.Everything
open import OracleModality
open import ChurchsThesis
open import MarkovInduction
open import DoubleNegationSheaves
open import StablePartial
open import PartialElements
open import NegativeResizing

K : ℕ → Ω¬¬
K n = ∂.domain (φ n n)

coK : ℕ → Ω¬¬
coK n = ¬resize (φ n n ↓)

coK≰mK : (f : ℕ → ℕ) → ((n : ℕ) → ⟨ coK n ⟩ ↔ ⟨ K (f n) ⟩) → ⊥
coK≰mK f red = {!!}
  where
    lemma1 : {A : Type ℓ} {B : Type ℓ'} → (x : Maybe A) → (y : Maybe B) → Dec (isJust x ⊎ isJust y)
    lemma1 nothing nothing = no (⊎rec (λ x → x) (λ x → x))
    lemma1 nothing (just x) = yes (inr tt)
    lemma1 (just x) nothing = yes (inl tt)
    lemma1 (just x) (just x₁) = yes (inl tt)

    lemma2 : (n : ℕ) → ((m : ℕ) → ¬ isJust (φ₀ (f n) (f n) m)) → ((m : ℕ) → ¬ isJust (φ₀ n n m)) → ⊥
    lemma2 n u v = {!!}
      where
        halts : ¬ ¬ (φ n n ↓)
        halts dnh = u n {!!}

    g : ℕ → Bool
    g n = {!!}
      where
        k : Σ[ k' ∈ ℕ ] (isJust (φ₀ (f n) (f n) k') ⊎ isJust (φ₀ n n k'))
        k = markovsPrinciple (λ k' → (isJust (φ₀ (f n) (f n) k') ⊎ isJust (φ₀ n n k'))) (λ k' → lemma1 _ _)
            λ x → {!!}
