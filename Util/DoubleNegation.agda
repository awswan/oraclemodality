module Util.DoubleNegation where

open import Cubical.Core.Everything

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty

open import Util.ModalOperatorSugar

private
  variable
    ℓ ℓ' : Level

¬¬-in : {A : Type ℓ} → A → ¬ ¬ A
¬¬-in x = λ z → z x

¬¬-map : {A : Type ℓ} {B : Type ℓ'} → (A → B) → (¬ ¬ A → ¬ ¬ B)
¬¬-map f x = λ z → x (λ a → z (f a))

_↔_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

instance
  ¬¬-modal : {ℓa ℓb : Level} → ModalOperator ℓ-zero ℓa ℓb (λ {ℓ} A → ¬ ¬ A)
  ¬¬-modal = record { bind = λ nna f nb → nna (λ a → f a nb) }

¬¬¬→¬ : (A : Type ℓ) → ¬ (¬ (¬ A)) → ¬ A
¬¬¬→¬ A w = λ a → w (¬¬-in a)

¬¬⊥→⊥ : ¬ (¬ ⊥) → ⊥
¬¬⊥→⊥ x = x (λ y → y)

¬¬Dec : (A : Type ℓ) → ¬ ¬ (Dec A)
¬¬Dec A z = z (no noA)
  where
    noA : ¬ A
    noA a = z (yes a)

¬¬LEM : (P : Type ℓ) → ¬ ¬ (P ⊎ (¬ P))
¬¬LEM P z = z (inr (λ p → z (inl p)))
