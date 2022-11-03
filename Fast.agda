module Fast where

open import Includes
open import Util.Everything
open import OracleModality
open import ChurchsThesis
open import MarkovInduction
open import DoubleNegationSheaves
open import StablePartial
open import PartialElements
open import NegativeResizing

boundPartial : (n : ℕ) → (f : Fin n → ∂ ℕ) →
  ¬ ¬ (Σ[ m ∈ ℕ ] ((k : Fin n) → (z : f k ↓) → fst z ≤ m))

boundPartial zero f z = z (0 , (λ k _ → ⊥rec (¬Fin0 k)))
boundPartial (suc n) f = do
  (N , Nismax) ← boundPartial n λ k → f ((fst k) , ≤-suc (snd k))
  yes (m , w) ← ¬¬Dec (f (n , ≤-refl) ↓)
    where no ¬p → ¬¬-in (N , (λ k z → ⊎rec (λ q → Nismax ((fst k) , q) (subst (λ k' → f k' ↓) (toℕ-injective refl) z))
                                              (λ p → ⊥rec (¬p (subst (λ k' → f k' ↓) (toℕ-injective p) z))) (<-split (snd k))))
  ¬¬-in ((max N m) , λ k z → ⊎rec (λ q → ≤-trans (Nismax ((fst k) , q) (subst (λ k' → f k' ↓) (toℕ-injective refl) z)) left-≤-max)
                                  (λ p → subst (λ k' → k' ≤ max N m) (separatedℕ _ _ (partialUnique (f k) (subst (λ k' → f k' ↓= m) (toℕ-injective (sym p)) w) (snd z))) right-≤-max)
                                  (<-split (snd k)))

partialMax : (n : ℕ) → (Fin n → ∂ ℕ) → ∇ ℕ
partialMax n f = least (λ m → (k : Fin n) → (z : f k ↓) → fst z ≤ m) (boundPartial n f)

∂suc : ∂ ℕ → ∂ ℕ
∂.domain (∂suc N) = ∂.domain N
∂.value (∂suc N) = suc ∘ (∂.value N)

-- fastWithProof : (n : ℕ) → ∇ (Σ[ m ∈ ℕ ] ({!!} × {!!}))
-- fastWithProof n = {!!}

fast : ℕ → ∇ ℕ
∇.is-this (fast n) m =
  ¬¬resize (Σ[ mx ∈ ℕ ] ((partialMax (suc n) (λ l → φ (fst l) (fst l))) ↓= mx ) × (m ≡ n + (suc mx)) )
∇.well-defd (fast n) m m' u u' = do
  (mx , (z , p)) ← ¬¬resize-out u
  (mx' , (z' , p')) ← ¬¬resize-out u'
  q ← ∇.well-defd (partialMax (suc n) (λ l → φ (fst l) (fst l))) _ _ z z'
  ¬¬-in (p ∙∙ (λ i → n + suc (q i)) ∙∙ sym p')
∇.almost-inh (fast n) = do
  (mx , z) ← ∇.almost-inh (partialMax (suc n) (λ l → φ (fst l) (fst l)))
  ¬¬-in (n + (suc mx) , ¬¬resize-in (mx , (z , refl)))

fastSIncreasing : {n : ℕ} → (x : fast n ↓) → (y : fast (suc n) ↓) → (fst x < fst y)
fastSIncreasing {n} (x , p) (y , q) = <Stable _ _ do
  (mx , (u , v)) ← ¬¬resize-out p
  (my , (w , t)) ← ¬¬resize-out q
  (_ , u') ← ¬¬resize-out u
  (w' , _) ← ¬¬resize-out w
  ¬¬-in (subst2 (λ x' y' → x' < y') (sym v) (sym t)
                (<-+-≤ {m = n} ≤-refl (suc-≤-suc (<-asym' (λ r → u' (my , r) (λ {(k , z) → w' (k , ≤-suc z)}))))))

fastIsFast : (e : ℕ) → (z : φ e e ↓) (w : fast e ↓) → fst z < fst w
fastIsFast e z (m , w) = <Stable _ _ do
  (mx , (u , v)) ← ¬¬resize-out w
  (mxIsBound , _) ← ¬¬resize-out u
  ¬¬-in (subst (λ m' → fst z < m') (sym v) (≤<-trans (mxIsBound (e , ≤-refl) z) (<≤-trans ≤-refl (≤-+k zero-≤))))

slowWithProof : (n : ℕ) → ◯⟨ fast ⟩ (Σ[ m ∈ ℕ ] ((u : fast m ↓) → n ≤ fst u) × ((k : Fin m) → (v : fast (fst k) ↓) → fst v < n))
slowWithProof zero = ∣ 0 , ((λ u → zero-≤) , λ k → ⊥rec (¬Fin0 k)) ∣
slowWithProof (suc n) = do
  (m , (p , q)) ← slowWithProof n
  k ← query fast m
  ∣ ⊎rec (λ r → m , ((λ u → subst (λ x → suc n ≤ x) (separatedℕ _ _ (partialUnique (fast m) (snd k) (snd u))) r) , λ l v → ≤-suc (q l v)))
         (λ r → (suc m) , ((λ u → ≤<-trans (p k) (fastSIncreasing k u)) ,
           λ l v → ⊎rec (λ w → ≤-suc (q ((fst l) , w) v))
                        (λ w → subst (λ k' → k' < suc n) (separatedℕ _ _ (partialUnique (fast m) (snd k) (subst (λ l' → fast l' ↓= fst v) w (snd v)))) r)
         (<-split (snd l)))) (splitℕ-≤ (suc n) (fst k)) ∣

slowFromFast : ℕ → ◯⟨ fast ⟩ ℕ
slowFromFast n = slowWithProof n >>= (∣_∣ ∘ fst)

slow : ℕ → ∇ ℕ
slow n = strip fast separatedℕ (slowFromFast n)

