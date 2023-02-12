module Util.StablePartial where

open import Includes
open import Util.PartialElements
open import Axioms.NegativeResizing

open import Util.Everything

record ∂ (A : Type ℓ) : Type ℓ where
  field
    domain : Ω¬¬
    value : ⟨ domain ⟩ → A

∂hasUnderlyingPartialDF : HasUnderlyingPartialDomainFirst {ℓ = ℓ} ∂
HasUnderlyingPartialDomainFirst.domain ∂hasUnderlyingPartialDF α = ⟨ ∂.domain α ⟩
HasUnderlyingPartialDomainFirst.eval ∂hasUnderlyingPartialDF α = ∂.value α
∂.domain (fst (HasUnderlyingPartialDomainFirst.total ∂hasUnderlyingPartialDF a)) = ¬¬⊤
∂.value (fst (HasUnderlyingPartialDomainFirst.total ∂hasUnderlyingPartialDF a)) _ = a
snd (HasUnderlyingPartialDomainFirst.total ∂hasUnderlyingPartialDF a) = (¬¬resize-in tt) , refl

instance
  ∂hasUnderlyingPartial : HasUnderlyingPartial {ℓ = ℓ} ∂
  ∂hasUnderlyingPartial = HasUnderlyingPartialFromDomain ∂hasUnderlyingPartialDF

isProp∂↓ : {A : Type ℓ} (Asep : Separated A) {α : ∂ A} → (isProp (α ↓))
isProp∂↓ Asep {α = α} = Ω¬¬-props (∂.domain α)

instance
  open ModalOperator
  ∂modalOp : ModalOperator ℓ-zero ℓ ℓ' ∂
  ∂.domain (bind (∂modalOp) α f) = ¬¬resize (Σ[ z ∈ ⟨ ∂.domain α ⟩ ] ⟨ ∂.domain (f (∂.value α z)) ⟩)
  ∂.value (bind (∂modalOp) α f) u = ∂.value (f (∂.value α αdom)) βdom
    where
      αdom : ⟨ ∂.domain α ⟩
      αdom = Ω¬¬-stab _ (¬¬-map fst (¬¬resize-out u))
        
      βdom : ⟨ ∂.domain (f (∂.value α αdom)) ⟩
      βdom = Ω¬¬-stab _ do
        (αdom' , βdom') ← ¬¬resize-out u
        ¬¬-in (subst (λ αdom'' → ⟨ ∂.domain (f (∂.value α αdom'')) ⟩) (Ω¬¬-props _ αdom' αdom) βdom')
