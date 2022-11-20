module Relativised.Nat where

open import Includes
open import Util.Everything
open import OracleModality

suc⟨_⟩ : (χ : Oracle A B) → ◯⟨ χ ⟩ ℕ → ◯⟨ χ ⟩ ℕ
suc⟨ χ ⟩ = nullRec (isNull-Null (oDefd χ)) (λ n → ∣ suc n ∣)

relativeℕElim : {A : Type ℓ} {B : Type ℓ'} (χ : Oracle A B) →
  (X : ◯⟨ χ ⟩ ℕ → OM.◯-Types χ {ℓ = ℓ''}) → ⟨ X (∣ 0 ∣) ⟩ →
  ((n : ◯⟨ χ ⟩ ℕ) → ⟨ X n ⟩ → ⟨ X (suc⟨ χ ⟩ n) ⟩) →
  (n : ◯⟨ χ ⟩ ℕ) → ⟨ X n ⟩

relativeℕElim χ X base step = nullElim (snd ∘ X) (ℕelim base (λ n ih → step ∣ n ∣ ih))

relativeℕElim2 : (χ : Oracle A B) → (X : ◯⟨ χ ⟩ ℕ → ◯⟨ χ ⟩ ℕ → OM.◯-Types χ {ℓ = ℓ}) →
 ⟨ X ∣ 0 ∣ ∣ 0 ∣ ⟩ →
 ((ν : ◯⟨ χ ⟩ ℕ) → ⟨ X ∣ 0 ∣ ν ⟩ → ⟨ X ∣ 0 ∣ (suc⟨ χ ⟩ ν) ⟩) →
 ((μ : ◯⟨ χ ⟩ ℕ) → ⟨ X μ ∣ 0 ∣ ⟩ → ⟨ X (suc⟨ χ ⟩ μ) ∣ 0 ∣ ⟩) →
 ((μ ν : ◯⟨ χ ⟩ ℕ) → ⟨ X μ ν ⟩ → ⟨ X (suc⟨ χ ⟩ μ) (suc⟨ χ ⟩ ν) ⟩) →
 (μ : ◯⟨ χ ⟩ ℕ) → (ν : ◯⟨ χ ⟩ ℕ) → ⟨ X μ ν ⟩

relativeℕElim2 {ℓ = ℓ} χ X zz zs sz ss =
  relativeℕElim {ℓ'' = ℓ} χ (λ μ → ((ν : ◯⟨ χ ⟩ ℕ) → ⟨ X μ ν ⟩) , isNullΠ (λ ν → snd (X μ ν)))
                (λ ν → relativeℕElim {ℓ'' = ℓ} χ (λ ν' → X ∣ 0 ∣ ν') zz zs ν)
                (λ μ ih → relativeℕElim {ℓ'' = ℓ} χ (λ ν → X (suc⟨ χ ⟩ μ) ν) (sz μ (ih ∣ 0 ∣))
                                                       λ ν _ → ss μ ν (ih ν))

-- ◯znots : (χ : Oracle A B) → (ν : ◯⟨ χ ⟩ ℕ) → ¬ (∣ 0 ∣ ≡ suc⟨ χ ⟩ ν)
-- ◯znots χ = nullElim {!!} (λ _ → λ p → extract⊥ χ {!!})
--   where
--     isZ : ◯⟨ χ ⟩ ℕ → Type _
--     isZ = {!!}

-- ◯discreteℕ : (χ : Oracle A B) → (ν μ : ◯⟨ χ ⟩ ℕ) → ◯⟨ χ ⟩ (Dec (ν ≡ μ))
-- ◯discreteℕ χ = relativeℕElim2 χ (λ ν μ → ◯⟨ χ ⟩ (Dec (ν ≡ μ)) , isNull-Null (oDefd χ))
--   ∣ yes refl ∣
--   (λ ν _ → ∣ no {!!} ∣) {!!} {!!}
