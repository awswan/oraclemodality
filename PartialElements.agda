module PartialElements where

open import Cubical.Core.Everything
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Util.HasUnderlyingType
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import NegativeResizing

private
  variable
    ℓ ℓ' : Level

record ∂ (A : Type ℓ) : Type ℓ where
  field
    is-this : A → Ω¬¬
    well-defd : (a a' : A) → ⟨ is-this a ⟩ → ⟨ is-this a' ⟩ → ¬ ¬ a ≡ a'

record HasUnderlyingPartial (S : Type ℓ → Type ℓ') : Type (ℓ-max ℓ' (ℓ-suc ℓ)) where
  field
    getUnderlyingPartial : {A : Type ℓ} → S A → ∂ A
    includeTotal : {A : Type ℓ} → A → S A
    totalIs : {A : Type ℓ} → (a : A) → ⟨ ∂.is-this (getUnderlyingPartial (includeTotal a)) a ⟩


module _ {S : Type ℓ → Type ℓ} ⦃ hup : HasUnderlyingPartial S ⦄ {A : Type ℓ} where
  open HasUnderlyingPartial hup

  _↓=_ : S A → A → Type
  _↓=_ α a = ⟨ ∂.is-this (getUnderlyingPartial α) a ⟩

  {- We say x is defined, or that it denotes an element of A. -}
  _↓ : S A → Type ℓ
  _↓ α = Σ[ a ∈ A ] (α ↓= a)

  defdIsProp : (Separated A) → (α : S A) → isProp (α ↓)
  defdIsProp sA α (a , u) (b , v) = Σ≡Prop (λ a' → Ω¬¬-props _) (sA _ _ (∂.well-defd (getUnderlyingPartial α) _ _ u v))

  _↓=↓_ : S A → S A → Type ℓ
  α ↓=↓ β = Σ[ a ∈ A ] (α ↓= a × β ↓= a)

  _≈_ : S A → S A → Type ℓ
  α ≈ β = (a : A) → ((α ↓= a) ↔ (β ↓= a))

  ι : A → S A
  ι = includeTotal

  ιIs : (a : A) → (ι a ↓= a)
  ιIs = totalIs

  ιdefd : (a : A) → (ι a ↓)
  ιdefd a = a , (ιIs a)

  ↓=compose≡ : {α : S A} {a b : A} → (α ↓= a) → (p : a ≡ b) → (α ↓= b)
  ↓=compose≡ {α} u p = subst (λ a' → α ↓= a') p u

  ≡compose↓= : {α β : S A} (p : α ≡ β) {a : A} → (β ↓= a) → (α ↓= a)
  ≡compose↓= p {a} u = subst (λ γ → γ ↓= a) (sym p) u

  ↓=↓compose↓= : {α β : S A} {a : A} → (α ↓=↓ β) → (β ↓= a) → (α ↓= a)
  ↓=↓compose↓= {α} {β} {a} (a' , (v , w)) u = Ω¬¬-stab _ (¬¬-map (λ p' → subst (λ c → α ↓= c) p' v) p)
    where
      p : ¬ ¬ (a' ≡ a)
      p = ∂.well-defd (getUnderlyingPartial β) a' a w u

instance
  open HasUnderlyingPartial
  degenerateHasUnderlyingPartial : HasUnderlyingPartial {ℓ = ℓ} ∂
  getUnderlyingPartial degenerateHasUnderlyingPartial α = α
  ∂.is-this (includeTotal degenerateHasUnderlyingPartial a) a' = ¬¬resize (a ≡ a')
  ∂.well-defd (includeTotal degenerateHasUnderlyingPartial a) b b' u v = do
    p ← ¬¬resize-out u
    q ← ¬¬resize-out v
    ¬¬-in (sym p ∙ q)
  totalIs (degenerateHasUnderlyingPartial) a = ¬¬resize-in refl

∂in : {A : Type ℓ} → A → ∂ A
∂.is-this (∂in a) a' = ¬¬resize (a ≡ a')
∂.well-defd (∂in a) b b' u v = do
  p ← ¬¬resize-out u
  q ← ¬¬resize-out v
  ¬¬-in (sym p ∙ q)
