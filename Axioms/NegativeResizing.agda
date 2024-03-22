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

¬¬resize-in-from¬¬ : {A : Type ℓ} → ¬ ¬ A → [ ¬¬resize A ]
¬¬resize-in-from¬¬ p = Ω¬¬-stab (¬¬resize _) (¬¬-map ¬¬resize-in p)

¬¬resize-out : {A : Type ℓ} → [ ¬¬resize A ] → ¬ ¬ A
¬¬resize-out x = ¬resize-out _ x

¬¬resize-out' : {A : Type ℓ} → Stable A → [ ¬¬resize A ] → A
¬¬resize-out' stab x = stab (¬¬resize-out x)

¬¬⊤ = ¬¬resize Unit
¬¬⊥ = ¬¬resize ⊥

¬¬⊥-out : [ ¬¬⊥ ] → ⊥
¬¬⊥-out x = ¬¬resize-out x λ y → y

¬¬Σ : (p : Ω¬¬) → (q : [ p ] → Ω¬¬) → Ω¬¬
¬¬Σ p q = ¬¬resize (Σ[ z ∈ [ p ] ] [ q z ])

¬¬Σ-in : {p : Ω¬¬} {q : [ p ] → Ω¬¬} → (z : [ p ]) → (w : [ q z ]) → [ ¬¬Σ p q ]
¬¬Σ-in z w = ¬¬resize-in (z , w)

¬¬fst : {p : Ω¬¬} {q : [ p ] → Ω¬¬} → [ ¬¬Σ p q ] → [ p ]
¬¬fst z = Ω¬¬-stab _ (¬¬-map fst (¬¬resize-out z))

¬¬snd' : {p : Ω¬¬} {q : [ p ] → Ω¬¬} → (z : [ ¬¬Σ p q ]) → (w : [ p ]) → [ q w ]
¬¬snd' {p} {q} z w = Ω¬¬-stab _ (¬¬-map (λ (w' , u) → subst (λ w → [ q w ]) (Ω¬¬-props _ _ _) u) (¬¬resize-out z))

¬¬snd : {p : Ω¬¬} {q : [ p ] → Ω¬¬} → (z : [ ¬¬Σ p q ]) → [ q (¬¬fst z) ]
¬¬snd z = ¬¬snd' z (¬¬fst z)

¬¬Π : (A : Type ℓ) → (q : A → Ω¬¬) → Ω¬¬
¬¬Π A q = ¬¬resize ((z : A) → [ q z ])

¬¬Π-in : {A : Type ℓ} {q : A → Ω¬¬} → ((a : A) → [ q a ]) → [ ¬¬Π A q ]
¬¬Π-in f = ¬¬resize-in f

¬¬Π-out : {A : Type ℓ} {q : A → Ω¬¬} → [ ¬¬Π A q ] → (a : A) → [ q a ]
¬¬Π-out z a = Ω¬¬-stab _ (¬¬-map (λ f → f a) (¬¬resize-out z))

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
