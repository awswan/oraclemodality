open import Util.ModalOperatorSugar
open import Includes

module Util.MaybeModalInstance where

instance
  maybeModal : ModalOperator ℓ-zero ℓ ℓ Maybe
  ModalOperator.bind maybeModal nothing f = nothing
  ModalOperator.bind maybeModal (just x) f = f x
