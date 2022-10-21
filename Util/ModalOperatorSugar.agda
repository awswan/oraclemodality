module Util.ModalOperatorSugar where

open import Cubical.Core.Everything

private
  variable
    ℓbase ℓ ℓ' : Level

record ModalOperator (M : {ℓ : Level} → Type ℓ → Type ℓ) : Type (ℓ-suc (ℓ-max ℓbase (ℓ-max ℓ ℓ'))) where
  field
    bind : {A : Type ℓ} {B : Type ℓ'} → M A → (A → M B) → M B

_>>=_ : {M : {ℓ : Level} → Type ℓ → Type ℓ} ⦃ mo : ModalOperator {ℓbase = ℓbase} M ⦄ →
           {A : Type ℓ} {B : Type ℓ'}→ M A → (A → M B) → M B
_>>=_ ⦃ mo ⦄ = ModalOperator.bind mo
