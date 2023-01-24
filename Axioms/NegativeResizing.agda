module Axioms.NegativeResizing where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Relation.Nullary

open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Util.ModalOperatorSugar
open import Util.DoubleNegation
open import Util.HasUnderlyingType

private
  variable
    ℓ ℓ' : Level

{- We postulate a classifier for all negated propositions. We formulate it
   in terms of negated types rather than ¬¬-stable types because that is
   closer to what happens in the semantics in cubical assemblies.
-}
postulate
  Ω¬¬ : Type
  [_] : Ω¬¬ → Type
  Ω¬¬-props : (P : Ω¬¬) → (isProp [ P ])
  ¬resize : Type ℓ → Ω¬¬
  ¬resize-in : (A : Type ℓ) → ¬ A → [ ¬resize A ]
  ¬resize-out : (A : Type ℓ) → [ ¬resize A ] → ¬ A
  ¬resize-rtr : (P : Ω¬¬) → ¬resize(¬ [ P ]) ≡ P

{- We derive properties that allow us to use Ω¬¬ as a classifier for ¬¬-stable props -}
Ω¬¬-stab : (P : Ω¬¬) → Stable [ P ]
Ω¬¬-stab P x = subst [_] (¬resize-rtr P) (¬resize-in (¬ [ P ]) x)

Ω¬¬-ext : (P Q : Ω¬¬) → ([ P ] → [ Q ]) → ([ Q ] → [ P ]) → P ≡ Q
Ω¬¬-ext P Q f g =
  sym (¬resize-rtr P) ∙ cong (λ R → ¬resize(¬ R)) (hPropExt (Ω¬¬-props P) (Ω¬¬-props Q) f g) ∙
    ¬resize-rtr Q

¬¬resize : (A : Type ℓ) → Ω¬¬
¬¬resize A = ¬resize (¬ A)

¬¬resize-in : {A : Type ℓ} → A → [ ¬¬resize A ]
¬¬resize-in a = ¬resize-in _ (¬¬-in a)

¬¬resize-out : {A : Type ℓ} → [ ¬¬resize A ] → ¬ ¬ A
¬¬resize-out x = ¬resize-out _ x

¬¬resize-out' : {A : Type ℓ} → Stable A → [ ¬¬resize A ] → A
¬¬resize-out' stab x = stab (¬¬resize-out x)

¬¬⊤ = ¬¬resize Unit
¬¬⊥ = ¬¬resize ⊥

¬¬⊥-out : [ ¬¬⊥ ] → ⊥
¬¬⊥-out x = ¬¬resize-out x λ y → y

Ω¬¬-invert : Ω¬¬ → Ω¬¬
Ω¬¬-invert x = ¬¬resize (¬ [ x ])

SeparatedΩ¬¬ : Separated Ω¬¬
SeparatedΩ¬¬ = (λ x y z → Ω¬¬-ext x y (λ w → Ω¬¬-stab _ (¬¬-map (λ p → subst _ p w) z))
                                            λ w → Ω¬¬-stab _ (¬¬-map (λ p → subst _ (sym p) w) z))

Ω¬¬Set : isSet Ω¬¬
Ω¬¬Set = Separated→isSet SeparatedΩ¬¬

instance
  Ω¬¬underlyingType : HasUnderlyingType Ω¬¬
  HasUnderlyingType.get-underlying-type Ω¬¬underlyingType = [_]
