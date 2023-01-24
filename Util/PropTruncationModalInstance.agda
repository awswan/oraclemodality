module Util.PropTruncationModalInstance where

open import Cubical.Core.Everything
open import Cubical.HITs.PropositionalTruncation public

open import Util.ModalOperatorSugar

instance
  truncModalOp : ∀ {ℓ ℓ'} → ModalOperator ℓ-zero ℓ ℓ' ∥_∥₁
  ModalOperator.bind (truncModalOp) z f = rec isPropPropTrunc f z
