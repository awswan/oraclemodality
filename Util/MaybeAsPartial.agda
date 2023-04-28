module Util.MaybeAsPartial where

open import Cubical.Core.Everything
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty

open import Util.HasUnderlyingType
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import Axioms.NegativeResizing
open import Util.PartialElements

private variable
  ℓ : Level

instance
  open HasUnderlyingPartial
  maybeHasUnderlyingPartial : HasUnderlyingPartial (Maybe {ℓ = ℓ})
  is-this maybeHasUnderlyingPartial z a = ¬¬resize (z ≡ just a)
  well-defd maybeHasUnderlyingPartial z a b u v = do
    u' ← ¬¬resize-out u
    v' ← ¬¬resize-out v
    ¬¬-in (just-inj a b (sym u' ∙ v'))
  includeTotal maybeHasUnderlyingPartial a = just a
  totalIs maybeHasUnderlyingPartial a = ¬¬resize-in refl
