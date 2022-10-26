module Util.HasUnderlyingType where

open import Cubical.Core.Everything

open import Cubical.Foundations.Structure hiding (⟨_⟩)

private
  variable
    ℓ ℓ' : Level

record HasUnderlyingType (T : Type ℓ') : Type (ℓ-max ℓ' (ℓ-suc ℓ)) where
  field
    get-underlying-type : T → Type ℓ

⟨_⟩ : { T : Type ℓ' } ⦃ hut : HasUnderlyingType T ⦄ → T → Type ℓ
⟨_⟩ ⦃ hut ⦄ = HasUnderlyingType.get-underlying-type hut

instance
  StructureHasUnderlyingType : {S : Type ℓ → Type ℓ'} → HasUnderlyingType (TypeWithStr ℓ S)
  HasUnderlyingType.get-underlying-type StructureHasUnderlyingType = typ
