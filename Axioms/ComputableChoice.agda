open import Includes

open import Axioms.ChurchsThesis
open import Axioms.StableSubcountableChoice
open import Axioms.NegativeResizing

open import Util.PartialElements
open import Util.DoubleNegation
open import Util.HasUnderlyingType
open import Util.ModalOperatorSugar
open import Util.PropTruncationModalInstance

module Axioms.ComputableChoice where

{- Package Church's thesis and stable subcountable choice together into a convenient single axiom -}
compChoice : (dom : ℕ → Ω¬¬) (X : (n : ℕ) → ⟨ dom n ⟩ → ℕ → Type ℓ) → (f : (n : ℕ) → (d : ⟨ dom n ⟩) →  ∥ Σ[ m ∈ ℕ ] (X n d m) ∥₁) →
  ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (d : ⟨ dom n ⟩) → Σ[ c ∈ φ-domain e n ] (X n d (φ-fromDomain e n c))) ∥₁
compChoice dom X f = do
  g ← sscc dom (λ n d → Σ[ m ∈ ℕ ] (X n d m)) f
  (e , eWorks) ← ECT (λ n → record { domain = dom n
                                     ; value = λ d → fst (g n d) })
  ∣ e , (λ n d → (φ-domainStable (¬¬resize-out (fst (eWorks n d)))) , (subst (X n d) (sym (snd (eWorks n d))) (snd (g n d)))) ∣₁
