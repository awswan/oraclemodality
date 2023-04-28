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

φ-domainIndependent : (e n : ℕ) → (d : φ-domain e n) → (φ e n ↓= (φ-fromDomain e n d))
φ-domainIndependent e n d = (¬¬resize-in d) , (cong (φ-fromDomain e n) (φ-isPropDomain _ _))

postulate
  ECT : (f : ℕ → ∂ ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (z : f n ↓) → φ e n ↓= (get (f n) z)) ∥₁

-- ECT' : 

module GeneralisedECT (encA : A → ℕ) (encB : B → ℕ) (decA : ℕ → A) (decB : ℕ → B)
  (p : (a : A) → decA (encA a) ≡ a) (q : (b : B) → decB (encB b) ≡ b)
  where

  θ : (e : ℕ) → A → ∂ B
  ∂.domain (θ e a) = ∂.domain (φ e (encA a))
  ∂.value (θ e a) u = decB (∂.value (φ e (encA a)) u)

  GECT : (X : A → B → Type) (dom : A → Ω¬¬) (f : (a : A) → ⟨ dom a ⟩ → Σ[ b ∈ B ] X a b) →
    ∥ Σ[ e ∈ ℕ ] ((a : A) → (d : ⟨ dom a ⟩) → Σ[ u ∈ θ e a ↓ ] X a (get (θ e a) u)) ∥₁
  GECT X dom f = do
    (e , z) ← ECT (λ n → record { domain = dom (decA n)
                                  ; value = λ d → encB (fst (f (decA n) d)) })
    ∣ e , lemma e z ∣₁
    where
      lemma : (e : ℕ) (z : (n : ℕ) → (d : ⟨ dom (decA n) ⟩) → φ e n ↓= encB (fst (f (decA n) d))) (a : A) (d : ⟨ dom a ⟩) → Σ[ u ∈ θ e a ↓ ] X a (get (θ e a) u)
      lemma e z a d = (fst (z (encA a) d')) ,
        subst (X a) ((λ i → fst (f (p a (~ i)) (dPath i))) ∙∙ sym (q _) ∙∙ cong decB (sym (snd (z (encA a) d')))) (snd (f a d))
        where
          dPath = subst-filler (λ a → ⟨ dom a ⟩) (sym (p a)) d
          d' = dPath i1

CT : (f : ℕ → ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → φ e n ↓= f n) ∥₁
CT f = do
  (e , p) ← ECT (ι ∘ f)
  ∣ e , (λ n → p n (ιdefd (f n))) ∣₁

totalComputable : Type
totalComputable = Σ[ e ∈ ℕ ] ((n : ℕ) → φ e n ↓)

evalTC : totalComputable → ℕ → ℕ
evalTC tc n = ∂.value (φ (fst tc) n) (snd tc n)

CT' : (X : ℕ → ℕ → Type ℓ) → (f : (n : ℕ) → Σ[ m ∈ ℕ ] X n m) →
  ∥ Σ[ e ∈ totalComputable ] ((n : ℕ) → X n (evalTC e n)) ∥₁
CT' X f = do
  (e , p) ← CT (λ n → fst (f n))
  ∣ (e , (λ n → fst (p n))) , (λ n → subst (X n) (sym (snd (p n))) (snd (f n))) ∣₁
