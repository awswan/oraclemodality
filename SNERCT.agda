module SNERCT where

open import Includes

open import Cubical.Functions.Surjection

open import Axioms.NegativeResizing
open import Axioms.ChurchsThesis
open import Axioms.NegativeCountableChoice
open import Axioms.DenseNegativeChoice
open import PartialElements
open import OracleModality
open import DoubleNegationSheaves
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import Util.HasUnderlyingType
open import Util.ModalOperatorInstances.PropTruncation
open import Util.LexNull
open import Util.Nullification

ℕwithVec : Type
ℕwithVec = ℕ × (Σ[ n ∈ ℕ ] (Fin n → ℕ))

postulate
  ℕwithVecℕIso : Iso ℕwithVec ℕ

ℕ→ℕwithVec = Iso.inv ℕwithVecℕIso
ℕwithVec→ℕ = Iso.fun ℕwithVecℕIso

finiteSearchMaybe : (n : ℕ) → (A : Type ℓ) → (f : (m : Fin n) → Maybe A) → ((m : Fin n) → f m ≡ nothing) ⊎ (Σ[ (m , a) ∈ Fin n × A ] f m ≡ just a)
finiteSearchMaybe zero A f = inl (λ (m , p) → ⊥rec (¬-<-zero p))
finiteSearchMaybe (suc n) A f = ⊎rec (λ z → ⊎rec (λ p → inl (λ m → ⊎rec (λ q → cong f (toℕ-injective refl) ∙ z ((fst m) , q)) (λ q → cong f (toℕ-injective q) ∙ p) (<-split (snd m)))) (λ {(a , p) → inr (((n , ≤-refl) , a) , p)}) (lem (f (n , ≤-refl)))) (λ {((m , a) , p) → inr ((((fst m) , (≤-suc (snd m))) , a) , p)}) (finiteSearchMaybe n A λ m → f ((fst m) , (≤-suc (snd m))))
  where -- TODO: Cleanup
    lem : (w : Maybe A) → (w ≡ nothing) ⊎ (Σ[ a ∈ A ] w ≡ just a)
    lem nothing = inl refl
    lem (just x) = inr (x , refl)

data prOutputPoss : Type where
  continue : prOutputPoss
  halt : ℕ → prOutputPoss
  callOracle : ℕ → prOutputPoss

-- instance
--   open HasUnderlyingPartial
--   OMHasUnderlyingPartial : {χ : Oracle ℕ ℕ} → HasUnderlyingPartial {ℓ = ℓ} ◯⟨ χ ⟩
--   is-this (OMHasUnderlyingPartial {χ = χ}) z x = ¬¬resize (z ≡ ∣ x ∣)
--   well-defd (OMHasUnderlyingPartial {χ = χ}) z a b p q = do
--     p' ← ¬¬resize-out p
--     q' ← ¬¬resize-out q
--     ◯→¬¬ χ separatedℕ (∣∣-inj (λ n → (χ n ↓) , (∇defd-prop separatedℕ (χ n))) a b (sym p' ∙ q'))
--   includeTotal (OMHasUnderlyingPartial {χ = χ}) = ∣_∣
--   totalIs (OMHasUnderlyingPartial {χ = χ}) a = ¬¬resize-in refl

below∇ : ∇ ℕ → ℕ → Type
below∇ N m = (n : ℕ) → N ↓= n → m < n

data M⟨_⟩ {A : Type ℓa} {B : Type ℓb} (χ : Oracle A B) (X : Type ℓ) : Type (ℓ-max ℓ (ℓ-max ℓa ℓb)) where
  ∣_∣M : X → M⟨ χ ⟩ X
  queryM : (a : A) → (f : χ a ↓ → M⟨ χ ⟩ X) → M⟨ χ ⟩ X

M→◯⟨_⟩ : (χ : Oracle A B) → (X : Type ℓ) → M⟨ χ ⟩ X → ◯⟨ χ ⟩ X
M→◯⟨ χ ⟩ X ∣ x ∣M = ∣ x ∣
M→◯⟨ χ ⟩ X (queryM a f) = hub a (λ s → M→◯⟨ χ ⟩ X (f s))

mixedMax : ℕ → ∇ ℕ → ∇ ℕ
∇.is-this (mixedMax n M) k = ¬¬resize ((m : ℕ) → M ↓= m → k ≡ max n m)
∇.well-defd (mixedMax n M) k k' u v = do
  u ← ¬¬resize-out u
  v ← ¬¬resize-out v
  (m , w) ← ∇.almost-inh M
  ¬¬-in (u m w ∙ sym (v m w))
∇.almost-inh (mixedMax n M) = do
  (m , w) ← ∇.almost-inh M
  ¬¬-in (max n m , (¬¬resize-in (λ m' w' → cong (max n) (separatedℕ _ _ (∇.well-defd M _ _ w w')))))


module _ (n : ℕ) (M : ∇ ℕ) where
  mixedMax≤Left :  (k : ℕ) → (mixedMax n M ↓= k) → (n ≤ k)
  mixedMax≤Left k u = ≤Stable _ _ do
    (m , v) ← ∇.almost-inh M
    u ← ¬¬resize-out u
    ¬¬-in (subst (λ k → n ≤ k) (sym (u m v)) left-≤-max)

  mixedMaxRight↓ : M ↓ → (mixedMax n M ↓)
  mixedMaxRight↓ (m , u) = max n m , ¬¬resize-in (λ m' u' → cong (max n)
    (separatedℕ _ _ (∇.well-defd M _ _ u u')))

  mixedMax≤Right : (k : ℕ) → (below∇ M k) → (below∇ (mixedMax n M) k)
  mixedMax≤Right k u l v = <Stable _ _ do
    (m , w) ← ∇.almost-inh M
    p ← ∇.well-defd (mixedMax n M) (max n m) l
                    (¬¬resize-in (λ m' w' → cong (max n) (separatedℕ _ _ (∇.well-defd M _ _ w w')))) v
    ¬¬-in (<≤-trans (u _ w) (subst (λ l' → m ≤ l') p right-≤-max))

module _ (χ : Oracle ℕ ℕ) where
  initialSeg : (l : ℕ) → (Fin l) → ∇ ℕ
  initialSeg l (i , _) = χ i

  initialSegDefd : (l : ℕ) → Type
  initialSegDefd l = (k : Fin l) → χ (fst k) ↓

  valuesBelow : ∇ ℕ → Type
  valuesBelow N = (m : ℕ) → below∇ N m → χ m ↓

  bound : M⟨ χ ⟩ X → ∇ ℕ
  bound ∣ x ∣M = ∇-in 0
  bound (queryM n f) = mixedMax (suc n) (fst (∇injective ((χ n ↓) , (∇defd-prop separatedℕ (χ n)))
                                         (∇.almost-inh (χ n)) (λ s → (bound (f s)))))


  fromBound : (x : M⟨ χ ⟩ X) → valuesBelow (bound x) → X
  fromBound ∣ x ∣M g = x
  fromBound (queryM n f) g = fromBound (f χn) g'
    where
      χn : χ n ↓
      χn = g n (mixedMax≤Left (suc n) ((fst (∇injective ((χ n ↓) , (∇defd-prop separatedℕ (χ n)))
                                         (∇.almost-inh (χ n)) (λ s → (bound (f s)))))))

      injWitness = snd (∇injective ((χ n ↓) , (∇defd-prop separatedℕ (χ n)))
                                         (∇.almost-inh (χ n)) (λ s → (bound (f s))))

      g' : valuesBelow (bound (f χn))
      g' m mlt = g m (subst (λ z → below∇ (mixedMax (suc n) z) m) (injWitness χn)
                                                    (mixedMax≤Right _ (bound (f χn)) _ mlt))

  oracleCover : isSurjection (M→◯⟨ χ ⟩ X)
  oracleCover = NullPropElim _ (λ z → _ , isPropPropTrunc) (λ x → ∣ ∣ x ∣M , refl ∣₁)
    λ a f ih → dnc (χ a) _ ih >>= λ g → ∣ (queryM a (λ s → fst (g s))) , (cong (hub a) (funExt (λ s → snd (g s)))) ∣₁



  sufficientBound : {A : Type ℓ} → (z : ◯⟨ χ ⟩ A) → ∥ Σ[ N ∈ ∇ ℕ ] (valuesBelow N → fiber ∣_∣ z) ∥₁
  sufficientBound z = oracleCover zp >>= λ {(zp' , q) → ∣ (bound zp') , (fromBound zp') ∣₁}
    where
      zp : ◯⟨ χ ⟩ (fiber ∣_∣ z)
      zp = nullElim (λ z' → isNull-Null (oDefd χ) {X = fiber ∣_∣ z'}) (λ z' → ∣ z' , refl ∣) z




  -- queryBound : (z : ◯⟨ χ ⟩ A) → ∥ sufficientBound z ∥₁
  -- queryBound = NullPropElim (oDefd χ) (λ z → ∥ sufficientBound z ∥₁ , isPropPropTrunc) (λ a → ∣ (∇-in 0) , (λ _ → a , refl) ∣₁) λ n f → λ w → dnc (χ n) (λ s → sufficientBound (f s)) w >>= λ w' → ∣ givenBound n f w' ∣₁
  --   where
  --     givenBound : (n : ℕ) → (f : oDefd χ n → Null (oDefd χ) A) → ((s : χ n ↓) → sufficientBound (f s)) →
  --                     sufficientBound (hub n f)
  --     givenBound n f w' =
  --       (fst (fst M)) , (λ g → fst (snd (w' (g n (λ m s → {!!})) , {!!}))) -- subst (λ m → n < m) (separatedℕ _ _ {!!}) left-≤-max))) {!!}) , {!!})
  --       where
  --         packst :  ¬ (¬ (Σ[ s ∈ χ n ↓ ] (fst (w' s) ↓)))
  --         packst = do
  --               s ← ∇.almost-inh (χ n)
  --               t ← ∇.almost-inh (fst (w' s))
  --               ¬¬-in (s , t)

  --         M : isContr _
  --         M = ∇-isSheaf ((Σ[ s ∈ χ n ↓ ] (fst (w' s) ↓)) , isPropΣ (∇defd-prop separatedℕ (χ n)) λ s → ∇defd-prop separatedℕ (fst (w' s))) packst λ {(s , t) → ∇-in (max (suc n) (fst t))}

--          lemma : ¬ ¬ (max (suc n)
--           M : ∇ ℕ
--           is-this M m = ¬¬resize ((s : χ n ↓) → (t : fst (w' s) ↓) → m ≡ max (fst s) (fst t))
--           well-defd M m m' u v = do
--             u' ← ¬¬resize-out u
--             v' ← ¬¬resize-out v
--             s ← almost-inh (χ n)
--             t ← almost-inh (fst (w' s))
--             ¬¬-in (u' s t ∙ sym (v' s t))
--           almost-inh M = do
--             s ← almost-inh (χ n)
--             t ← almost-inh (fst (w' s))
--             -- ¬¬-in ((max (fst s) (fst t)) , (¬¬resize-in (λ s' t' i → max (separatedℕ (fst s) (fst s') (well-defd (χ n) (fst s) (fst s') (snd s) (snd s')) i) (fst (isProp→PathP (λ j → ∇defd-prop {!!} {!!}) {!!} {!!} {!!})))))
--             ¬¬-in (max (fst s) (fst t) , ¬¬resize-in (λ s' t' → cong₂ {B = λ s → fst (w' s) ↓} {C = λ s' t' → ℕ} (λ s t → max (fst s) (fst t)) (Σ≡Prop (λ m → Ω¬¬-props (is-this (χ n) m)) (separatedℕ (fst s) (fst s') (well-defd (χ n) (fst s) (fst s') (snd s) (snd s')))) {!!}))
-- --            max (fst s) (fst t) ≡ max (fst s') (fst t')
            

  -- -- eth Turing machine halts on input n in < l steps given first l - 1 values of oracle but may halt on other fragments of χ
  -- ψ₀ : ℕ → ℕ → (l : ℕ) → ((k : Fin l) → initialSeg l k ↓) → Maybe ℕ
  -- ψ₀ e n l approx = ⊎rec (λ _ → nothing) (λ { ((l' , m) , p) → just m}) (finiteSearchMaybe l ℕ λ l' → φ₀ e (encodeℕwithVec→ℕ (n , (l , λ k → fst (approx k)))) (fst l'))
  
  -- -- eth Turing machine halts on input from the first l values of oracle in ≤ l steps and this does not occur for any smaller values of l
  -- ψ₁ : ℕ → ℕ → (l : ℕ) → ((k : Fin l) → initialSeg l k ↓) → Maybe ℕ 
  -- ψ₁ e n l approx = ⊎rec (λ _ → ψ₀ e n l approx) (λ _ → nothing) (finiteSearchMaybe l ℕ (λ l' → ψ₀ e n (fst l') λ {(k , p) → approx (k , (<-trans p (snd l')))}))

  -- ψ : ℕ → ℕ → ∇ ℕ
  -- ψ e n = {!!}

  
