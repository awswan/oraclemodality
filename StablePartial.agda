module StablePartial where

open import Includes
open import PartialElements
open import Axioms.NegativeResizing

open import Util.Everything

record ∂ (A : Type ℓ) : Type ℓ where
  field
    domain : Ω¬¬
    value : ⟨ domain ⟩ → A

instance
  open HasUnderlyingPartial
  ∂hasUnderlyingPartial : HasUnderlyingPartial {ℓ = ℓ} ∂
  is-this ∂hasUnderlyingPartial α a = ¬¬resize (Σ[ z ∈ ⟨ ∂.domain α ⟩ ] (∂.value α z ≡ a))
  well-defd ∂hasUnderlyingPartial α a b u v = do
    (z , p) ← ¬¬resize-out u
    (w , q) ← ¬¬resize-out v
    ¬¬-in (sym p ∙∙ cong (∂.value α) (Ω¬¬-props _ _ _) ∙∙ q)
  ∂.domain (includeTotal ∂hasUnderlyingPartial a) = ¬¬⊤
  ∂.value (includeTotal ∂hasUnderlyingPartial a) _ = a
  totalIs ∂hasUnderlyingPartial a = ¬¬resize-in ((¬¬resize-in tt) , refl)

↓→domain : {A : Type ℓ} (α : ∂ A) → (α ↓) → ⟨ ∂.domain α ⟩
↓→domain α (a , u) = Ω¬¬-stab _ do
  (z , _) ← ¬¬resize-out u
  ¬¬-in z

domain→↓ : {A : Type ℓ} (α : ∂ A) → ⟨ ∂.domain α ⟩ → (α ↓)
domain→↓ α z = (∂.value α z) , (¬¬resize-in (z , refl))

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
