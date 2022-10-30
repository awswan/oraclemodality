module Encodings where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to ⊎rec)
open import Cubical.Data.Maybe
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to ⊥rec)

-- open import NegativeResizing
-- open import PartialElements
-- open import OracleModality
-- open import Util.DoubleNegation
-- open import Util.ModalOperatorSugar
-- open import Util.HasUnderlyingType
-- open import Util.ModalOperatorInstances.PropTruncation


module triangle where
  tno : ℕ → ℕ
  tno zero = zero
  tno (suc n) = (suc n) + tno n

  zero-<-suc : {n : ℕ} → 0 < suc n
  zero-<-suc = suc-≤-suc zero-≤

  tno-monotonic : (n m : ℕ) → n < m → (tno n < tno m)
  tno-monotonic n zero p = ⊥rec (¬-<-zero p)
  tno-monotonic n (suc m) p = ⊎rec (λ p' → <≤-trans (tno-monotonic n m p') (≤-+k zero-≤)) (λ p' → suc-≤-suc (subst (λ z → z ≤ m + tno m) (cong tno (sym p')) ≤SumRight)) (<-split p)

  tno-wmonotonic : (n m : ℕ) → n ≤ m → (tno n ≤ tno m)
  tno-wmonotonic n m p = ⊎rec (λ p' → <-weaken (tno-monotonic n m p')) (λ p' → subst (λ k → tno n ≤ k) (cong tno p') ≤-refl) (≤-split p)

  f₀ : (n m : ℕ) → ℕ
  f₀ n m = m + tno n

  private
    lemma1 : (n m : ℕ) → (m ≤ n) → f₀ n m < tno (suc n)
    lemma1 n m p = ≤-+k (suc-≤-suc p)

    lemma2 : (n m : ℕ) → tno n ≤ f₀ n m
    lemma2 n m = ≤-+k zero-≤

  f₀-inj₀ : (n n' m m' : ℕ) → (m ≤ n) → (m' ≤ n') → (n < n') → (f₀ n m < f₀ n' m')
  f₀-inj₀ n n' m m' p p' q = <≤-trans (lemma1 n m p) (≤-trans (tno-wmonotonic (suc n) n' q) (lemma2 n' m'))

  f₀-inj₁ : (n m m' : ℕ) → (f₀ n m ≡ f₀ n m' → m ≡ m')
  f₀-inj₁ n m m' q = inj-+m q

  ℕ≤ = Σ[ (n , m) ∈ ℕ × ℕ ] m ≤ n

  f : ℕ≤ → ℕ
  f ((n , m) , p) = f₀ n m

  f-inj : (u v : ℕ≤) → (f u ≡ f v) → (u ≡ v)
  f-inj u@((n , m) , p) u'@((n' , m') , p') q = Σ≡Prop (λ _ → isProp≤) (≡-× r (f₀-inj₁ n m m' (q ∙ cong (λ l → m' + l) (cong tno (sym r)))))
    where
      r : n ≡ n'
      r with n ≟ n'
      r | lt v = ⊥rec (¬m<m (subst (λ x → x < f u') q (f₀-inj₀ n n' m m' p p' v)))
      r | eq v = v
      r | gt v = ⊥rec (¬m<m (subst (λ x → f u' < x) q (f₀-inj₀ n' n m' m p' p v)))
      

  g : (k : ℕ) → fiber f k
  g zero = ((0 , 0) , ≤-refl) , refl
  g (suc k) = ⊎rec (λ p' → ((n , (suc m)) , p') , (cong suc q)) (λ p' → (((suc n) , 0) , zero-≤) , (cong suc (cong (λ l → l + tno n) (sym p') ∙ q))) (≤-split p)
    where
      n = fst (fst (fst (g k)))
      m = snd (fst (fst (g k)))
      p = snd (fst (g k))
      q = snd (g k)

  triangle-equiv : ℕ≤ ≃ ℕ
  triangle-equiv = pathSplitToEquiv (f , (record { sec = (fst ∘ g) , (snd ∘ g) ; secCong = λ u u' → (f-inj u u') , (λ _ → isSetℕ _ _ _ _)}))
