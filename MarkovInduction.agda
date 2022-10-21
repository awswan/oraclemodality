module MarkovInduction where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Nat

open import Util.ModalOperatorSugar
open import Util.DoubleNegation
open import DoubleNegationPlus
open import NegativeResizing


private
  variable
    ℓ ℓ' : Level

_is-suc-of_ : (∇ ℕ) → (∇ ℕ) → Type
N is-suc-of M = (n : ℕ) → [ ∇.is-this M n ] → [ ∇.is-this N (suc n) ]

private
  ℕsep = Discrete→Separated (discreteℕ)

invert-suc-of : {N M : (∇ ℕ)} → (N is-suc-of M) → (n : ℕ) →
                [ ∇.is-this N (suc n) ] → [ ∇.is-this M n ]
invert-suc-of {N} {M} s n z = Ω¬¬-stab _
  do
    (m , w) ← ∇.almost-inh M
    ¬¬-in (lem m w)
  where
    is-N = ∇.is-this N
    is-M = ∇.is-this M
  
    lem : (m : ℕ) → [ is-M m ] → [ is-M n ]
    lem m w = subst (λ k → [ is-M k ]) (injSuc (ℕsep _ _ (∇.well-defd N _ _ (s m w) z))) w

module Pred (N : (∇ ℕ)) (nz : ¬ [ ∇.is-this N 0 ]) where
  M : (∇ ℕ)
  M = record { is-this = λ n → ∇.is-this N (suc n)
             ; well-defd = λ n m x y → ¬¬-map injSuc (∇.well-defd N (suc n) (suc m) x y)
             ; almost-inh = λ z → ∇.almost-inh N (λ {(0 , w) → nz w ; ((suc n) , w) → z (n , w)}) }

  is-suc : N is-suc-of M
  is-suc n x = x

postulate
  markov-ind : (A : (∇ ℕ) → Type ℓ)
               (step : (N : (∇ ℕ)) (ih : (M : (∇ ℕ)) → (N is-suc-of M) → (A M)) → (A N)) →
               (N : (∇ ℕ)) → A N
