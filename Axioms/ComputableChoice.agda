module Axioms.ComputableChoice where

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
  ComputableChoice :
    (dom : ℕ → Ω¬¬)
    (X : (n : ℕ) → ⟨ dom n ⟩ → ℕ → Ω¬¬) →
    (f : (n : ℕ) → (d : ⟨ dom n ⟩) → ∥ Σ[ m ∈ ℕ ] [ X n d m ] ∥₁) →
    ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (d : ⟨ dom n ⟩) → Σ[ c ∈ φ-domain e n ] [ X n d (φ-fromDomain e n c) ]) ∥₁


generalisedComputableChoice :
  (C : Type ℓ) →
  (s : ℕ → ∂ C) →
  ((c : C) → ∥ Σ[ n ∈ ℕ ] s n ↓= c ∥₁) →
  (dom : ℕ → Ω¬¬)
  (X : (n : ℕ) → ⟨ dom n ⟩ → C → Ω¬¬) →
  (f : (n : ℕ) → (d : ⟨ dom n ⟩) → ∥ Σ[ c ∈ C ] [ X n d c ] ∥₁) →
  ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (d : ⟨ dom n ⟩) → Σ[ φdefd ∈ φ-domain e n ] Σ[ sdefd ∈ [ ∂.domain (s (φ-fromDomain e n φdefd)) ] ] [ X n d (∂.value (s (φ-fromDomain e n φdefd)) sdefd) ]) ∥₁
  
generalisedComputableChoice C s sSurj dom X f = do
  (e , g) ← ComputableChoice dom (λ n d m → ¬¬resize (Σ[ w ∈ [ ∂.domain (s m) ] ] [ X n d (∂.value (s m) w) ]))
    λ n d → do
      (c , x) ← f n d
      (m , (y , p)) ← sSurj c
      ∣ m , ¬¬resize-in (y , subst (λ c → [ X n d c ]) (sym p) x) ∣₁
  ∣ e , (λ n d → (fst (g n d)) , (Ω¬¬-stab _ (¬¬-map fst (¬¬resize-out (snd (g n d))))) , Ω¬¬-stab _ (¬¬-map (λ (w , x) → subst (λ w → [ X n d (∂.value (s (φ-fromDomain e n (fst (g n d)))) w) ]) (Ω¬¬-props _ _ _) x) (¬¬resize-out (snd (g n d))))) ∣₁


ECT : (f : ℕ → ∂ ℕ) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (z : f n ↓) → φ e n ↓= (get (f n) z)) ∥₁
ECT f = do
  (e , w) ← ComputableChoice (λ n → ∂.domain (f n)) (λ n z m → ¬¬resize (m ≡ get (f n) z))
    λ n z → ∣ (get (f n) z) , ¬¬resize-in refl ∣₁
  ∣ e , (λ n z → (¬¬resize-in (fst (w n z))) , separatedℕ _ _ (¬¬-map (λ p → cong (φ-fromDomain e n) (φ-isPropDomain _ _) ∙ p) (¬¬resize-out (snd (w n z))))) ∣₁

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
