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


countableCodECT2 :
  (C : Type ℓ) →
  (s : ℕ → ∂ C) →
  ((c : C) → ∥ Σ[ n ∈ ℕ ] s n ↓= c ∥₁) →
  (dom : ℕ → Ω¬¬)
  (X : (n : ℕ) → ⟨ dom n ⟩ → C → Ω¬¬) →
  (f : (n : ℕ) → (d : ⟨ dom n ⟩) → ∥ Σ[ c ∈ C ] [ X n d c ] ∥₁) →
  ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (d : ⟨ dom n ⟩) → Σ[ φdefd ∈ φ-domain e n ] Σ[ sdefd ∈ [ ∂.domain (s (φ-fromDomain e n φdefd)) ] ] [ X n d (∂.value (s (φ-fromDomain e n φdefd)) sdefd) ]) ∥₁
  
countableCodECT2 C s sSurj dom X f = do
  (e , g) ← ECT2 dom (λ n d m → ¬¬resize (Σ[ w ∈ [ ∂.domain (s m) ] ] [ X n d (∂.value (s m) w) ]))
    λ n d → do
      (c , x) ← f n d
      (m , (y , p)) ← sSurj c
      ∣ m , ¬¬resize-in (y , subst (λ c → [ X n d c ]) (sym p) x) ∣₁
  ∣ e , (λ n d → (fst (g n d)) , (Ω¬¬-stab _ (¬¬-map fst (¬¬resize-out (snd (g n d))))) , Ω¬¬-stab _ (¬¬-map (λ (w , x) → subst (λ w → [ X n d (∂.value (s (φ-fromDomain e n (fst (g n d)))) w) ]) (Ω¬¬-props _ _ _) x) (¬¬resize-out (snd (g n d))))) ∣₁
