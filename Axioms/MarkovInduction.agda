module Axioms.MarkovInduction where

open import Includes

open import Util.Everything

open import DoubleNegationSheaves
open import Axioms.NegativeResizing
open import PartialElements

_is-suc-of_ : (∇ ℕ) → (∇ ℕ) → Type
N is-suc-of M = (n : ℕ) → ⟨ ∇.is-this M n ⟩ → ⟨ ∇.is-this N (suc n) ⟩

private
  ℕsep = Discrete→Separated (discreteℕ)

invert-suc-of : {N M : (∇ ℕ)} → (N is-suc-of M) → (n : ℕ) →
                ⟨ ∇.is-this N (suc n) ⟩ → ⟨ ∇.is-this M n ⟩
invert-suc-of {N} {M} s n z = Ω¬¬-stab _
  do
    (m , w) ← ∇.almost-inh M
    ¬¬-in (lem m w)
  where
    is-N = ∇.is-this N
    is-M = ∇.is-this M
  
    lem : (m : ℕ) → ⟨ is-M m ⟩ → ⟨ is-M n ⟩
    lem m w = subst (λ k → ⟨ is-M k ⟩) (injSuc (ℕsep _ _ (∇.well-defd N _ _ (s m w) z))) w

module Pred (N : (∇ ℕ)) (nz : ¬ ⟨ ∇.is-this N 0 ⟩) where
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

least : (A : ℕ → Type ℓ) → ¬ ¬ (Σ ℕ A) → ∇ ℕ
∇.is-this (least A nnA) n = ¬¬resize (A n × ((m : Fin n) → ¬ A (fst m)))
∇.well-defd (least A nnA) n m u v = do
  (a , nisleast) ← ¬¬resize-out u
  (b , misleast) ← ¬¬resize-out v
  trichotomyRec n m (λ p _ → misleast (n , p) a) ¬¬-in λ q _ → nisleast (m , q) b
∇.almost-inh (least A nnA) noleast = nnA (λ {(n , a) → none n a})
  where
    none : (n : ℕ) → ¬ (A n)
    none = WFI.induction <-wellfounded (λ n ih a → noleast (n , (¬¬resize-in (a , (λ m → ih (fst m) (snd m))))))

least-in : {A : ℕ → Type ℓ} (nnA : ¬ ¬ (Σ ℕ A)) → (n : ℕ) → (least A nnA ↓= n) → ¬ ¬ (A n)
least-in nnA n u = ¬¬-map fst (¬¬resize-out u)

dec→decLeast : {A : ℕ → Type ℓ} (nnA : ¬ ¬ (Σ ℕ A)) → ((n : ℕ) → Dec (A n)) → (n : ℕ) → (Dec (least _ nnA ↓= n))
dec→decLeast nnA decA n with (any? {n = n} (decA ∘ fst))
... | yes (m , a) = no λ z → ¬¬resize-out z (λ {(_ , x) → x m a})
... | no ¬p with (decA n)
... | yes b = yes (¬¬resize-in (b , λ m c → ¬p (m , c)))
... | no ¬q = no (λ z → ¬¬resize-out z (λ {(c , _) → ¬q c}))

markovsPrinciple₀ : (N : ∇ ℕ) → ((n : ℕ) → Dec (N ↓= n)) → Σ[ n ∈ ℕ ] (N ↓= n)
markovsPrinciple₀ = markov-ind _ step
  where
    A' : ∇ ℕ → Type _
    A' N = ((n : ℕ) → Dec (N ↓= n)) → N ↓

    step : (N : (∇ ℕ)) (ih : (M : (∇ ℕ)) → (N is-suc-of M) → (A' M)) → (A' N)
    step N ih dec with (dec 0)
    ... | yes p = 0 , p
    ... | no ¬p = (suc (fst Mdefd)) , snd Mdefd
      where
        M : ∇ ℕ
        M = Pred.M N ¬p
    
        Mdefd : M ↓
        Mdefd = ih M (λ _ u → u) (λ n → dec (suc n))


markovsPrinciple : (A : ℕ → Type ℓ) → ((n : ℕ) → Dec (A n)) → ¬ ¬ (Σ[ n ∈ ℕ ] A n) → Σ[ n ∈ ℕ ] A n
markovsPrinciple A dec nnA =
  (fst MP0) ,
  (decRec (λ x → x) (λ z → ⊥rec (¬¬resize-out (snd MP0) λ w → z (fst w))) (dec (fst MP0)))
  where
    N : ∇ ℕ
    N = least A nnA

    MP0 : N ↓
    MP0 = markovsPrinciple₀ N (dec→decLeast nnA dec)
