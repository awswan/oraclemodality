module Axioms.ChurchsThesis where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Includes

open import Axioms.MarkovInduction
open import Axioms.NegativeResizing
open import Util.StablePartial
open import Util.PartialElements
open import Util.Everything


isJust : {A : Type ℓ} → Maybe A → Type
isJust nothing = ⊥
isJust (just x) = Unit

isJustDec : {A : Type ℓ} → (α : Maybe A) → Dec (isJust α)
isJustDec nothing = no (λ x → x)
isJustDec (just x) = yes tt

isPropIsJust : {A : Type ℓ} → {α : Maybe A} → (isProp (isJust α))
isPropIsJust {α = nothing} = isProp⊥
isPropIsJust {α = just x} = isPropUnit

fromJust : {A : Type ℓ} → (α : Maybe A) → (isJust α) → A
fromJust (just a) z = a

postulate
  φ₀ : ℕ → ℕ → ℕ → Maybe ℕ -- φ₀ e n k = output of eth Turing on input n in k steps
  φ₀-haltsOnce : (e n : ℕ) → (k k' : ℕ) → (isJust (φ₀ e n k)) → (isJust (φ₀ e n k')) → k ≡ k'

φ-domain : ℕ → ℕ → Type
φ-domain e n = Σ[ k ∈ ℕ ] (isJust (φ₀ e n k))

φ-isPropDomain : {e n : ℕ} → (isProp (φ-domain e n))
φ-isPropDomain {e} {n} (k , z) (k' , z') = Σ≡Prop (λ _ → isPropIsJust) (φ₀-haltsOnce e n k k' z z')

φ-fromDomain : (e : ℕ) → (n : ℕ) → (φ-domain e n) → ℕ
φ-fromDomain e n z = fromJust (φ₀ e n (fst z)) (snd z)

φ-domainStable : {e n : ℕ} → Stable (φ-domain e n)
φ-domainStable {e} {n} z =
  markovsPrinciple (λ k → isJust (φ₀ e n k)) dec z
      where
        dec : (k : ℕ) → Dec (isJust (φ₀ e n k))
        dec k with (φ₀ e n k)
        ... | nothing = no λ x → x
        ... | just m = yes tt

φ : ℕ → ℕ → ∂ ℕ
∂.domain (φ e n) = ¬¬resize (φ-domain e n)
∂.value (φ e n) z = φ-fromDomain e n (φ-domainStable (¬¬resize-out z))


φ-domainEquiv : (e n : ℕ) → (φ e n ↓ ≃ φ-domain e n)
φ-domainEquiv e n = propBiimpl→Equiv (isProp∂↓ separatedℕ) (φ-isPropDomain)
  (λ {(m , w) → φ-domainStable (¬¬resize-out w >>= (¬¬resize-out ∘ fst))})
  λ {(k , z) → (fromJust (φ₀ e n k) z) ,
        (¬¬resize-in ((¬¬resize-in ((k , z))) , cong (φ-fromDomain e n) (φ-isPropDomain _ _)))}

-- φ : ℕ → ℕ → ∂ ℕ
-- ∂.domain (φ e n) = ¬¬resize (φ-domain e n)
-- ∂.value (φ e n) z = φ-fromDomain e n dom
--   where
--     dom : φ-domain e n
--     dom = φ-domainStable e n (¬¬resize-out z)

-- module _ (e : ℕ) (n : ℕ) where
--   φ-domainIn : (φ-domain e n) → (φ e n ↓)
--   φ-domainIn z = snd (fst (φ-domainStable e n (¬¬resize-out (¬¬resize-in z)))) ,
--     ¬¬resize-in ((¬¬resize-in z) , refl)

--   φ-domainOut : (φ e n ↓) → (φ-domain e n)
--   φ-domainOut (m , z) = φ-domainStable e n do
--     (u , p) ← ¬¬resize-out z
--     ¬¬resize-out u

--   φ-domainStable' : Stable (φ e n ↓)
--   φ-domainStable' z = φ-domainIn (φ-domainStable e n (¬¬-map φ-domainOut z))

--   φ-domainIsProp : isProp (φ e n ↓)
--   φ-domainIsProp (m , u) (l , v) = Σ≡Prop (λ k → Ω¬¬-props _) (separatedℕ _ _ p)
--     where
--       p : NonEmpty (m ≡ l)
--       p = do
--         u' ← ¬¬resize-out u
--         v' ← ¬¬resize-out v
--         ¬¬-in (sym (snd u') ∙∙ cong (λ z → ∂.value (φ e n) z) (Ω¬¬-props _ (fst u') (fst v')) ∙∙ snd v')

postulate
  ECT : (f : ℕ → ∂ ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (z : f n ↓) → φ e n ↓= (fst z)) ∥₁
--  ECT' : (f : ℕ → ∂ ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (z : f n ↓) → φ e n ↓= ∂.value (f n) (Ω¬¬-stab (∂.domain (f n)) (¬¬-map (λ {(s , p) → s}) (¬¬resize-out (snd z))))) ∥₁

ECT' : (f : ℕ → ∂ ℕ) →
  ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (z : f n ↓) → Σ[ d ∈ φ-domain e n ] φ-fromDomain e n d ≡ fst z) ∥₁

ECT' f = ECT f >>= λ {(e , w) → ∣ e , (λ n z → lemma e w n z) ∣₁}
  where
    lemma : (e : ℕ) (w : (n : ℕ) → (z : f n ↓) → φ e n ↓= fst z) (n : ℕ) (z : f n ↓) →
      Σ[ d ∈ φ-domain e n ] φ-fromDomain e n d ≡ fst z
    lemma e w n z = d , p
      where
        w0 : φ e n ↓= fst z
        w0 = w n z
      
        d : φ-domain e n
        d = φ-domainStable do (¬¬resize-out w0 >>= (¬¬resize-out ∘ fst))

        p : φ-fromDomain e n d ≡ fst z
        p = separatedℕ _ _ do
          (u , q) ← ¬¬resize-out w0
          ¬¬-in (cong (φ-fromDomain e n) (φ-isPropDomain _ _) ∙ q)
        
ECT'' : (X : ℕ → ℕ → Type) (f : (n : ℕ) → ∂ (Σ[ m ∈ ℕ ] X n m)) →
  ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (f n ↓) → Σ[ d ∈ φ-domain e n ] (X n (φ-fromDomain e n d))) ∥₁
ECT'' X f = do
  (e , g) ← ECT f'
  ∣ e , (λ n z → lemma e n z (g n (proj↓ n z))) ∣₁
  where
    lemma : (e n : ℕ) → (z : f n ↓) → φ e n ↓= fst (fst z) → Σ[ d ∈ φ-domain e n ] (X n (φ-fromDomain e n d))
    lemma e n z u = φdom , subst (X n) path x
      where
        fdom : ⟨ ∂.domain (f n) ⟩
        fdom = ↓→domain (f n) z

        φdom : φ-domain e n
        φdom = φ-domainStable do
          u' ← ¬¬resize-out u
          ¬¬resize-out (fst u')

        x : X n (fst (∂.value (f n) fdom))
        x = snd (∂.value (f n) fdom)

        path : fst (∂.value (f n) fdom) ≡ φ-fromDomain e n φdom
        path = separatedℕ _ _ do
          (fdom' , p) ← ¬¬resize-out (snd z)
          (w , q) ← ¬¬resize-out u
          φdom' ← ¬¬resize-out w
          ¬¬-in (
            fst (∂.value (f n) fdom)
              ≡⟨ cong (fst ∘ (∂.value (f n))) (Ω¬¬-props _ _ _) ⟩
            fst (∂.value (f n) fdom')
              ≡⟨ cong fst p ⟩
            fst (fst z)
              ≡⟨ sym q ⟩
            φ-fromDomain e n _
              ≡⟨ cong (φ-fromDomain e n) (φ-isPropDomain _ _) ⟩
            φ-fromDomain e n φdom
              ∎)

    f' : ℕ → ∂ ℕ
    ∂.domain (f' n) = ∂.domain (f n)
    ∂.value (f' n) z = fst (∂.value (f n) z)

    proj↓ : (n : ℕ) → f n ↓ → f' n ↓
    proj↓ n (mx , w) = fst mx , Ω¬¬-stab _ do
      (z , p) ← ¬¬resize-out w
      ¬¬-in (¬¬resize-in (z , (cong fst p)))

CT : (f : ℕ → ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → φ e n ↓= f n) ∥₁
CT f = do
  (e , p) ← ECT (ι ∘ f)
  ∣ e , (λ n → p n (ιdefd (f n))) ∣₁

