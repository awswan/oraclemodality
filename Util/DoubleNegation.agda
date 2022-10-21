module Util.DoubleNegation where

open import Cubical.Core.Everything

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma

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
  ¬¬-modal : ModalOperator {ℓbase = ℓ-zero} {ℓ = ℓ} {ℓ' = ℓ'} (λ {ℓ} A → ¬ ¬ A)
  ¬¬-modal = record { bind = λ nna f nb → nna (λ a → f a nb) }
