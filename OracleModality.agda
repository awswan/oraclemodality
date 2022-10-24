module OracleModality where

open import Util.ModalOperatorSugar
open import Util.DoubleNegation
open import DoubleNegationPlus
open import NegativeResizing

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ⊥rec)
open import Cubical.Data.Sum renaming (rec to ⊎rec)

open import Cubical.HITs.Nullification renaming (rec to Null-rec)

open import Cubical.Modalities.Modality

open import MarkovInduction
open import DoubleNegationPlus

variable
  ℓ ℓ' ℓ'' ℓa ℓb : Level
  A : Type ℓ
  B : Type ℓ

Oracle : (A : Type ℓa) (B : Type ℓb) → Type (ℓ-max ℓa ℓb)
Oracle A B = A → ∇ B

module OM (f : Oracle A B) {ℓ : Level} where
  domain : A → Type _
  domain a = (f a) ↓

  open Modality (NullModality {ℓ = ℓ} domain) public

◯⟨_⟩ : {A : Type ℓa} {B : Type ℓb} (χ : Oracle A B) {ℓ : Level} →
       Type ℓ → Type (ℓ-max ℓ (ℓ-max ℓa ℓb))
◯⟨ χ ⟩ {ℓ = ℓ} = Null domain
  where
    open OM χ {ℓ = ℓ}

instance
  open ModalOperator
  Null-bind : ∀ {A : Type ℓa} {S : A → Type ℓb} {ℓc ℓd : Level} →
              ModalOperator (ℓ-max ℓa ℓb) ℓc ℓd (Null S)
  bind (Null-bind {S = S}) a g = Null-rec (isNull-Null S) g a
    -- Nullification.rec is more flexible than ◯-rec in allowing differing universe levels

module _ (χ : Oracle A B) where
  open OM χ

  private
    _is_ = ∇.is-this {A = ℕ}
    mp-inst : ∇ ℕ → Type _
    mp-inst N = ((n : ℕ) → ◯⟨ χ ⟩ (Dec [ N is n ])) → ◯⟨ χ ⟩ (N ↓)

  rel-markov : (N : ∇ ℕ) → mp-inst N
  rel-markov = markov-ind mp-inst step
    where
      step : (N : ∇ ℕ) →
             ((M : ∇ ℕ) → N is-suc-of M → mp-inst M) → mp-inst N

      step N ih dec = do
        (no ¬p) ← dec 0
          where yes p → ∣ (0 , p) ∣
        n₀ ← ih (Pred.M N ¬p) (Pred.is-suc N ¬p) (convert-dec ¬p)
        ∣ ((suc (fst n₀)) , snd n₀) ∣
        where
          convert-dec : (¬p : ¬ [ N is 0 ]) (n : ℕ) → ◯⟨ χ ⟩ (Dec [ (Pred.M N ¬p) is n ])
          convert-dec ¬p n = do
            yes p ← dec (suc n)
              where no ¬p' → ∣ no (λ z → ¬p' (Pred.is-suc N ¬p n z)) ∣
            ∣ yes (invert-suc-of {N = N} {M = Pred.M N ¬p} (Pred.is-suc N ¬p) n p) ∣

  locate-unique : (X : ℕ → Type ℓ) (is-unique : (n m : ℕ) → (X n) → (X m) → n ≡ m)
    (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) → ◯⟨ χ ⟩ (Dec (X n))) → ◯⟨ χ ⟩ (Σ ℕ X)
  locate-unique X is-unique exists dec = do
    (n , z) ← rel-markov N dec'
    yes p ← dec n
      where (no ¬p) → ⊥rec (¬¬resize-out z ¬p)
    ∣ n , p ∣
    where
      N : ∇ ℕ
      ∇.is-this N n = ¬¬resize (X n)
      ∇.well-defd N n m x y = do
        x' ← ¬¬resize-out x
        y' ← ¬¬resize-out y
        ¬¬-in (is-unique n m x' y')
      ∇.almost-inh N = ¬¬-map (λ {(n , x) → (n , ¬¬resize-in x)}) exists

      dec' : (n : ℕ) → ◯⟨ χ ⟩ (Dec [ ∇.is-this N n ])
      dec' n = do
        (no ¬p) ← dec n
          where (yes p) → ∣ yes (¬¬resize-in p) ∣
        ∣ no (λ w → ¬¬resize-out w ¬p) ∣

  locate-first : (X : ℕ → Type ℓ) (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) →
                    ◯⟨ χ ⟩ (Dec (X n))) → ◯⟨ χ ⟩ (Σ ℕ (λ n → X n × ((m : ℕ) → m < n → ¬ (X m))))
  locate-first X exists dec = locate-unique X' unique (λ w → exists (λ (n , v) → convert-ex w n v)) dec'
    where
      X' : ℕ → Type _
      X' n = X n × ((m : ℕ) → m < n → ¬ (X m))

      convert-ex : ¬ (Σ ℕ X') → (n : ℕ) → ¬ (X n)
      convert-ex z = WFI.induction <-wellfounded λ n w v → z (n , (v , w))

      unique : (n m : ℕ) → (X' n) → (X' m) → n ≡ m
      unique m n x y with (m ≟ n)
      ... | lt p = ⊥rec (snd y m p (fst x))
      ... | eq p = p
      ... | gt p = ⊥rec (snd x n p (fst y))

      scan : (n : ℕ) → ◯⟨ χ ⟩(((m : ℕ) → m < n → ¬ (X m)) ⊎ Σ ℕ λ k → (k < n) × (X' k))
      scan zero = ∣ inl (λ m p _ → ¬-<-zero p) ∣
      scan (suc n) = do
        inl z ← scan n
          where inr (m , (p , z)) → ∣ inr (m , (<-trans p ≤-refl) , z) ∣
        no ¬xn ← dec n
          where yes xn → ∣ inr (n , (≤-refl , (xn , z))) ∣
        ∣ inl (λ m p → ⊎rec (z m) (λ q → subst _ (sym q) ¬xn) (<-split p)) ∣

      dec' : (n : ℕ) → ◯⟨ χ ⟩ (Dec (X' n))
      dec' n = do
        inr (m , (p , z)) ← scan (suc n)
          where inl z → ∣ no (λ w → z n ≤-refl (fst w) ) ∣
        ⊎rec (λ q → ∣ no (λ {(_ , w) → w m q (fst z)}) ∣)
             (λ q → ∣ yes (subst X' q z) ∣) (<-split p)

  locate : (X : ℕ → Type ℓ) (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) →
                    ◯⟨ χ ⟩ (Dec (X n))) → ◯⟨ χ ⟩ (Σ ℕ X)
  locate X exists dec = do
    (n , (x , _)) ← locate-first X exists dec
    ∣ n , x ∣

  query : (a : A) → ◯⟨ χ ⟩((χ a) ↓)
  query a = hub a (λ z → ∣ z ∣)

--  query-correct : (a : A) → ◯⟨ χ ⟩ (

-- compute-section : (χ : ℕ → ∇ ℕ) →  →
  
search-fibre : (χ : ℕ → ∇ ℕ) (m : ℕ) → ¬ ¬ (Σ ℕ (λ n → [ ∇.is-this (χ n) m ])) →
  ◯⟨ χ ⟩ (Σ ℕ (λ n → [ ∇.is-this (χ n) m ]))

search-fibre χ m z = locate χ _ z λ n → do
  z ← query χ n
  ∣ dec' n z ∣
  where
    dec' : (n : ℕ) → ((χ n) ↓) → Dec [ ∇.is-this (χ n) m ]
    dec' n (χn , w) with discreteℕ χn m
    ... | yes p = yes (subst _ p w)
    ... | no ¬p = no (λ v → ∇.well-defd (χ n) χn m w v ¬p)

