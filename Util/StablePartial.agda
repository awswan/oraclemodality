module Util.StablePartial where

open import Includes
open import Util.PartialElements
open import Axioms.NegativeResizing

open import Util.Everything

record ∂ (A : Type ℓ) : Type ℓ where
  field
    domain : Ω¬¬
    value : ⟨ domain ⟩ → A

∂≡ : (α β : ∂ A) →
  (p : ∂.domain α ≡ ∂.domain β) →
  PathP (λ i → ⟨ p i ⟩ → A) (∂.value α) (∂.value β) →
  α ≡ β
∂.domain (∂≡ α β p q i) = p i
∂.value (∂≡ α β p q i) = q i

-- n∂≡2 : (α β : ∂ A) → (p : ∂.domain α ≡ ∂.domain β) →
--  (∂)

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

∂undefdUnique : {A : Type ℓ} → {α β : ∂ A} → ¬ α ↓ → ¬ β ↓ → α ≡ β
∂undefdUnique {α = α} {β = β} u v =
  ∂≡ α β (Ω¬¬-ext _ _ (λ w → ⊥rec (u w)) (λ w → ⊥rec (v w)))
    (toPathP (funExt (λ w → ⊥rec (v w))))

∂defdUnique : {A : Type ℓ} → {α β : ∂ A} → (u : [ ∂.domain α ]) →
  (v : [ ∂.domain β ]) → (∂.value α u ≡ ∂.value β v) → α ≡ β

∂defdUnique {A = A} {α = α} {β = β} u v p =
  ∂≡ α β q (toPathP (funExt (λ x →
    transport (λ i → ⟨ q i ⟩ → A) (∂.value α) x
      ≡⟨ lemma q x ⟩
    ∂.value α (subst [_] (sym q) x)
      ≡⟨ cong (∂.value α) (Ω¬¬-props _ _ _) ⟩
    ∂.value α u
      ≡⟨ p ⟩
    ∂.value β v
      ≡⟨ cong (∂.value β) (Ω¬¬-props _ _ _) ⟩
    ∂.value β x ∎
  )))
  where
    q = (Ω¬¬-ext _ _ (λ _ → v) (λ _ → u))

    lemma : {y : Ω¬¬} → (q : ∂.domain α ≡ y) → (z : [ y ]) →
      transport (λ i → [ q i ] → A) (∂.value α) z ≡
        ∂.value α (subst [_] (sym q) z)
    lemma = J (λ y q → (z : [ y ]) →
                 transport (λ i → [ q i ] → A) (∂.value α) z ≡
                   ∂.value α (subst [_] (sym q) z))
              λ z → transportRefl (∂.value α _)

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
