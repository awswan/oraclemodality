open import Includes
open import Cubical.Data.Nat.IsEven
open import Cubical.Data.Vec
open import Cubical.Data.Sum
open import Cubical.Functions.Embedding

open import Util.DoubleNegation

module Util.Encodings where

module Triangle where
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

  equiv : ℕ≤ ≃ ℕ
  equiv = pathSplitToEquiv (f , (record { sec = (fst ∘ g) , (snd ∘ g) ; secCong = λ u u' → (f-inj u u') , (λ _ → isSetℕ _ _ _ _)}))


▵Equiv = Triangle.equiv

Pair▵Iso :  Iso (ℕ × ℕ) Triangle.ℕ≤
Iso.inv Pair▵Iso ((n , m) , p) = m , (fst p)
Iso.fun Pair▵Iso (m , k) = ((k + m) , m) , k , refl
Iso.rightInv Pair▵Iso ((n , m) , p) = Σ≡Prop (λ _ → isProp≤) (ΣPathP ((snd p) , refl))
Iso.leftInv Pair▵Iso (m , k) = refl

Pair▵Equiv : (ℕ × ℕ) ≃ Triangle.ℕ≤ 
Pair▵Equiv = isoToEquiv Pair▵Iso

ℕPairEquiv : (ℕ × ℕ) ≃ ℕ
ℕPairEquiv = Pair▵Equiv ∙ₑ ▵Equiv

module OddEvenEquivM where
  f : ℕ ⊎ ℕ → ℕ
  f (inl n) = 2 · n
  f (inr n) = 1 + (2 · n)

  evenT→Path : (n : ℕ) → (isEvenT n) → (isEven n ≡ true)
  oddT→Path : (n : ℕ) → (isOddT n) → (isOdd n ≡ true)

  evenT→Path zero nEven = refl
  evenT→Path (suc n) nOdd = oddT→Path n nOdd

  oddT→Path (suc n) nEven = evenT→Path n nEven


  fEquiv : isEquiv f
  isEquiv.equiv-proof fEquiv n = ⊎rec ifEven ifOdd (evenOrOdd n)
    where
      ifEven : isEvenT n → isContr (fiber f n)
      ifEven nEven = ((inl (fst fib)) , (sym (snd fib))) ,
                     λ {(inl m , p) → Σ≡Prop (λ _ → isSetℕ _ _)
                       (cong inl (inj-sm· {m = 1} (sym (snd fib) ∙ sym p)))
                       ; (inr m , p) → ⊥rec (true≢false (sym (evenT→Path n nEven) ∙
                         falseIsEven n (m , (sym p))))}
        where
          fib : Σ[ m ∈ ℕ ] n ≡ (2 · m)
          fib = isEvenTrue n (evenT→Path n nEven)

      ifOdd : isOddT n → isContr (fiber f n)
      ifOdd nOdd = ((inr (fst fib)) , sym (snd fib)) ,
                 λ {(inl m , p) → ⊥rec (true≢false (sym (trueIsEven n (m , (sym p))) ∙
                   ¬IsOddTrue n (oddT→Path n nOdd)))
                 ; (inr m , p) → Σ≡Prop (λ _ → isSetℕ _ _)
                   (cong inr (inj-sm· {m = 1} (injSuc (sym (snd fib) ∙ sym p))))}
        where
          fib : Σ[ m ∈ ℕ ] n ≡ 1 + (2 · m)
          fib = isOddTrue n (oddT→Path n nOdd)

oddEvenEquiv : ℕ ⊎ ℕ ≃ ℕ
oddEvenEquiv = OddEvenEquivM.f , OddEvenEquivM.fEquiv

data haltingTime : Type where
  now : haltingTime
  later : ℕ → haltingTime → haltingTime

HTlength : haltingTime → ℕ
HTlength now = 0
HTlength (later _ t) = suc (HTlength t)

HTlengthExtendIso : (n : ℕ) → Iso (fiber HTlength n × ℕ) (fiber HTlength (suc n))
Iso.fun (HTlengthExtendIso n) ((t , p) , k) = (later k t) , cong suc p
Iso.inv (HTlengthExtendIso n) (now , p) = ⊥rec (znots p)
Iso.inv (HTlengthExtendIso n) (later k t , p) = (t , injSuc p) , k
Iso.leftInv (HTlengthExtendIso n) ((t , p) , k) = ΣPathP ((Σ≡Prop (λ _ → isSetℕ _ _) refl) , refl)
Iso.rightInv (HTlengthExtendIso n) (now , p) = ⊥rec (znots p)
Iso.rightInv (HTlengthExtendIso n) (later k t , p) = Σ≡Prop (λ _ → isSetℕ _ _) refl

FinSucIso : (n : ℕ) → Iso (Fin n ⊎ Unit) (Fin (suc n))
Iso.fun (FinSucIso n) (inl (m , p)) = m , ≤-suc p
Iso.fun (FinSucIso n) (inr _) = n , ≤-refl
Iso.inv (FinSucIso n) (m , p) = ⊎rec (λ q → inl (m , q)) (λ _ → inr tt) (<-split p)
Iso.leftInv (FinSucIso n) (inl (m , p)) with (<-split (≤-suc p))
... | inl p' = cong inl (Σ≡Prop (λ _ → isProp≤) refl)
... | inr p' = ⊥rec (¬m<m (subst (λ m → m < n) p' p))
Iso.leftInv (FinSucIso n) (inr _) with (<-split {m = n} ≤-refl)
... | inl p' = ⊥rec (¬m<m p')
... | inr p' = cong inr (isPropUnit _ _)
Iso.rightInv (FinSucIso n) (m , p) with (<-split p)
... | inl p' = Σ≡Prop (λ _ → isProp≤) refl
... | inr p' = Σ≡Prop (λ _ → isProp≤) (sym p')

ℕTupleEquiv : (n : ℕ) → (Fin (suc n) → ℕ) ≃ ℕ
ℕTupleEquiv zero =
  (Fin 1 → ℕ)
    ≃⟨ equiv→ (invEquiv Unit≃Fin1) (idEquiv ℕ) ⟩
  (Unit → ℕ)
    ≃⟨ UnitToType≃ ℕ ⟩
  ℕ
    ■
ℕTupleEquiv (suc n) =
  (Fin (suc (suc n)) → ℕ)
    ≃⟨ equiv→ (invEquiv (isoToEquiv (FinSucIso (suc n)))) (idEquiv ℕ) ⟩
  ((Fin (suc n)) ⊎ Unit → ℕ)
    ≃⟨ Π⊎≃ ⟩
  (Fin (suc n) → ℕ) × (Unit → ℕ)
    ≃⟨ ≃-× (ℕTupleEquiv n) (ΠUnit (λ _ → ℕ)) ⟩
  ℕ × ℕ
    ≃⟨ ℕPairEquiv ⟩
  ℕ
    ■

HTEqZ : (t : haltingTime) → Type
HTEqZ now = Unit
HTEqZ (later x t) = ⊥

HTEqZ→≡ : (t : haltingTime) → (HTEqZ t) → (now ≡ t)
HTEqZ→≡ now z = refl

HT≡→EqZ : (t : haltingTime) → (now ≡ t) → (HTEqZ t)
HT≡→EqZ t p = subst HTEqZ p tt

HT≡EqZIso : (t : haltingTime) → Iso (now ≡ t) (HTEqZ t)
Iso.fun (HT≡EqZIso t) p = HT≡→EqZ t p
Iso.inv (HT≡EqZIso t) z = HTEqZ→≡ t z
Iso.leftInv (HT≡EqZIso t) p = J (λ t p → HTEqZ→≡ t (HT≡→EqZ t p) ≡ p) refl p
Iso.rightInv (HT≡EqZIso now) z = substRefl {B = HTEqZ} tt

HTLengthZ≃EqZ : (t : haltingTime) →  HTEqZ t ≃ ((HTlength t) ≡ 0)
HTLengthZ≃EqZ now = propBiimpl→Equiv isPropUnit (isSetℕ _ _) (λ _ → refl) λ _ → tt
HTLengthZ≃EqZ (later x t) = propBiimpl→Equiv isProp⊥ (isSetℕ _ _) ⊥rec snotz

ℕ+Iso : Iso (Unit ⊎ ℕ) ℕ
Iso.fun ℕ+Iso (inl _) = 0
Iso.fun ℕ+Iso (inr n) = suc n
Iso.inv ℕ+Iso zero = inl tt
Iso.inv ℕ+Iso (suc n) = inr n
Iso.leftInv ℕ+Iso (inl _) = refl
Iso.leftInv ℕ+Iso (inr n) = refl
Iso.rightInv ℕ+Iso 0 = refl
Iso.rightInv ℕ+Iso (suc n) = refl

HTFibreEquiv : (n : ℕ) → (Fin n → ℕ) ≃ (fiber HTlength n)
HTFibreEquiv zero =
  (Fin zero → ℕ)
    ≃⟨ equiv→ (uninhabEquiv (λ {(m , p) → ¬-<-zero p}) (λ x → x)) (idEquiv ℕ) ⟩
  (⊥ → ℕ)
    ≃⟨ isContr→≃Unit isContr⊥→A ⟩
  Unit
    ≃⟨ invEquiv (isContr→≃Unit (isContrSingl now)) ⟩
  Σ[ t ∈ haltingTime ] now ≡ t
    ≃⟨ Σ-cong-equiv-snd (λ t → isoToEquiv (HT≡EqZIso t) ∙ₑ HTLengthZ≃EqZ t) ⟩
  fiber HTlength zero
    ■
HTFibreEquiv (suc n) =
  (Fin (suc n) → ℕ)
    ≃⟨ equiv→ (invEquiv (isoToEquiv (FinSucIso n))) (idEquiv ℕ) ⟩
  ((Fin n) ⊎ Unit → ℕ)
    ≃⟨ Π⊎≃ ⟩
  (Fin n → ℕ) × (Unit → ℕ)
    ≃⟨ ≃-× (HTFibreEquiv n) (ΠUnit (λ _ → ℕ)) ⟩
  fiber HTlength n × ℕ
    ≃⟨ isoToEquiv (HTlengthExtendIso n) ⟩
  fiber HTlength (suc n)
    ■

abstract
  haltingTimeCtbl : haltingTime ≃ ℕ
  haltingTimeCtbl =
    haltingTime
      ≃⟨ invEquiv (Σ-contractSnd (λ t → isContrSingl (HTlength t))) ⟩
    Σ[ t ∈ haltingTime ] Σ[ n ∈ ℕ ] HTlength t ≡ n
      ≃⟨ isoToEquiv rearrange ⟩
    Σ[ n ∈ ℕ ] (fiber HTlength n)
      ≃⟨ Σ-cong-equiv-snd (λ t → invEquiv (HTFibreEquiv t)) ⟩
    Σ[ n ∈ ℕ ] (Fin n → ℕ)
      ≃⟨ isoToEquiv rearrange2 ⟩
    Unit ⊎ (Σ[ n ∈ ℕ ] (Fin (suc n) → ℕ))
      ≃⟨ ⊎-equiv (idEquiv Unit) (Σ-cong-equiv-snd (λ n → ℕTupleEquiv n)) ⟩
    Unit ⊎ (ℕ × ℕ)
      ≃⟨ ⊎-equiv (idEquiv Unit) ℕPairEquiv ⟩
    Unit ⊎ ℕ
      ≃⟨ isoToEquiv ℕ+Iso ⟩
    ℕ
      ■
    where
      rearrange : Iso (Σ[ t ∈ haltingTime ] Σ[ n ∈ ℕ ] HTlength t ≡ n) (Σ[ n ∈ ℕ ] (fiber HTlength n))
      Iso.fun rearrange (t , n , p) = n , (t , p)
      Iso.inv rearrange (n , (t , p)) = t , (n , p)
      Iso.leftInv rearrange _ = refl
      Iso.rightInv rearrange _ = refl

      rearrange2 : Iso (Σ[ n ∈ ℕ ] (Fin n → ℕ)) (Unit ⊎ (Σ[ n ∈ ℕ ] (Fin (suc n) → ℕ)))
      Iso.fun rearrange2 (zero , f) = inl tt
      Iso.fun rearrange2 (suc n , f) = inr (n , f)
      Iso.inv rearrange2 (inl _) = 0 , (λ (m , p) → ⊥rec (¬-<-zero p))
      Iso.inv rearrange2 (inr (n , f)) = suc n , f
      Iso.leftInv rearrange2 (zero , f) = ΣPathP (refl , funExt (λ (m , p) → ⊥rec (¬-<-zero p)))
      Iso.leftInv rearrange2 (suc n , f) = refl
      Iso.rightInv rearrange2 (inl _) = refl
      Iso.rightInv rearrange2 (inr (n , f)) = refl

separatedHaltingTime : Separated haltingTime
separatedHaltingTime t t' p = isEmbedding→Inj (isEquiv→isEmbedding (snd haltingTimeCtbl))
  t t' (separatedℕ _ _ (¬¬-map (cong (fst haltingTimeCtbl)) p))

data Code : Type where
    returnNat : ℕ → Code
    queryOracleAndContinue : ℕ → ℕ → Code

abstract
  CodeCtbl : Code ≃ ℕ
  CodeCtbl =
    Code
      ≃⟨ isoToEquiv e ⟩
    ℕ ⊎ (ℕ × ℕ)
      ≃⟨ ⊎-equiv (idEquiv ℕ) ℕPairEquiv ⟩
    ℕ ⊎ ℕ
      ≃⟨ oddEvenEquiv ⟩
    ℕ
      ■
    where
      e : Iso Code (ℕ ⊎ (ℕ × ℕ))
      Iso.fun e (returnNat n) = inl n
      Iso.fun e (queryOracleAndContinue n e) = inr (n , e)
      Iso.inv e (inl n) = returnNat n
      Iso.inv e (inr (n , e)) = queryOracleAndContinue n e
      Iso.leftInv e (returnNat n) = refl
      Iso.leftInv e (queryOracleAndContinue n e) = refl
      Iso.rightInv e (inl n) = refl
      Iso.rightInv e (inr n) = refl

ℕ→Code : ℕ → Code
ℕ→Code = invEq CodeCtbl
Code→ℕ : Code → ℕ
Code→ℕ = fst CodeCtbl

ℕ→HT : ℕ → haltingTime
ℕ→HT = invEq haltingTimeCtbl

HT→ℕ : haltingTime → ℕ
HT→ℕ = fst haltingTimeCtbl


