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

∂defEqStable : {A : Type ℓ} (ASet : Separated A) (α : ∂ A) (b : A) → Stable (α ↓= b)
∂defEqStable Asep α b p = (Ω¬¬-stab _ (¬¬-map fst p)) , Asep _ _ (¬¬-map (λ q → cong (∂.value α) (isProp∂↓ Asep {α = α} _ (fst q)) ∙ snd q) p)

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

∂bindDesc : {A : Type ℓa} {B : Type ℓb} (α : ∂ A) (β : A → ∂ B)
  (dα : ⟨ ∂.domain α ⟩) (dβ : ⟨ ∂.domain (β (∂.value α dα)) ⟩) → (α >>= β) ↓= ∂.value (β (∂.value α dα)) dβ
∂bindDesc α β dα dβ = (¬¬resize-in (dα , dβ)) , λ i → ∂.value (β (∂.value α (αpath i)))
  (βpath i)
  where
    u : ⟨ ∂.domain (α >>= β) ⟩
    u = ¬¬resize-in (dα , dβ)
  
    dα' : ⟨ ∂.domain α ⟩
    dα' = Ω¬¬-stab _ (¬¬-map fst (¬¬resize-out u))

    αpath : dα' ≡ dα
    αpath = Ω¬¬-props _ _ _

    dβ' : ⟨ ∂.domain (β (∂.value α dα')) ⟩
    dβ' = Ω¬¬-stab _ do
        (αdom' , βdom') ← ¬¬resize-out u
        ¬¬-in (subst (λ αdom'' → ⟨ ∂.domain (β (∂.value α αdom'')) ⟩) (Ω¬¬-props _ αdom' dα') βdom')

    βpath : PathP (λ i → ⟨ ∂.domain (β (∂.value α (αpath i))) ⟩) dβ' dβ
    βpath = isProp→PathP (λ i → Ω¬¬-props _) _ _
