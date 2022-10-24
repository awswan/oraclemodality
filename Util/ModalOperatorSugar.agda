module Util.ModalOperatorSugar where

open import Cubical.Core.Everything

record ModalOperator (ℓbase ℓa ℓb : Level) (M : {ℓ' : Level} → Type ℓ' → Type (ℓ-max ℓbase ℓ')) :
       Type (ℓ-suc (ℓ-max ℓbase (ℓ-max ℓa ℓb))) where
  field
    bind : {A : Type ℓa} {B : Type ℓb} → M A → (A → M B) → M B

_>>=_ : {ℓbase ℓa ℓb : Level} {M : {ℓ' : Level} → Type ℓ' → Type (ℓ-max ℓbase ℓ')} → 
        ⦃ mo : ModalOperator ℓbase ℓa ℓb M ⦄ →
        {A : Type ℓa} {B : Type ℓb} →
        M A → (A → M B) → M B
_>>=_ ⦃ mo ⦄ = ModalOperator.bind mo
