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
open import StablePartial
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

postulate
  ℕPairIso : Iso (ℕ × ℕ) ℕ

p₀ : ℕ → ℕ
p₀ n = fst (Iso.inv ℕPairIso n)

p₁ : ℕ → ℕ
p₁ n = snd (Iso.inv ℕPairIso n)

pair : ℕ → ℕ → ℕ
pair n m = Iso.fun ℕPairIso (n , m)

pairβ₀ : (x y : ℕ) → (p₀ (pair x y) ≡ x)
pairβ₀ x y = cong fst (Iso.leftInv ℕPairIso (x , y))

pairβ₁ : (x y : ℕ) → (p₁ (pair x y) ≡ y)
pairβ₁ x y = cong snd (Iso.leftInv ℕPairIso (x , y))

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

  decodeDom : ℕ → ℕ → Type
  decodeDom e zero = p₀ e ≡ 0
  decodeDom e (suc k) = Σ[ z ∈ p₀ e > 0 ] ((w : χ (fst z) ↓) → Σ[ u ∈ φ (p₁ e) (fst w) ↓ ] decodeDom (fst u) k)

  decodeDomProp : (e : ℕ) → (k : ℕ) → (u v : decodeDom e k) → u ≡ v
  decodeDomProp e zero u v = isSetℕ _ _ u v
  decodeDomProp e (suc k) u v = isPropΣ isProp≤ (λ _ → isPropΠ (λ _ → isPropΣ (φ-domainIsProp _ _) (λ _ → decodeDomProp _ k))) _ _

  decodeDomStable : (e : ℕ) → (k : ℕ) → Stable (decodeDom e k)
  decodeDomStable e zero = separatedℕ _ _
  decodeDomStable e (suc k) p = z , (λ w → u w , decodeDomStable (fst (u w)) k (s w))
    where
      z : p₀ e > 0
      z = ≤Stable _ _ (¬¬-map fst p)

      p2 : (w : χ (fst z) ↓) → NonEmpty (Σ[ u ∈ φ (p₁ e) (fst w) ↓ ] decodeDom (fst u) k)
      p2 w = do
        (z' , f) ← p
        ¬¬-in (f (subst (λ z'' → χ (fst z'') ↓) (isProp≤ z z') w))

      u : (w : χ (fst z) ↓) → φ (p₁ e) (fst w) ↓
      u w = φ-domainStable' (p₁ e) (fst w) (¬¬-map fst (p2 w))

      s : (w : χ (fst z) ↓) → NonEmpty (decodeDom (fst (u w)) k)
      s w = do
        (u' , t) ← p2 w
        ¬¬-in (subst (λ u'' → decodeDom (fst u'') k) (φ-domainIsProp _ _ u' (u w)) t)

  decodeFromDom : (e k : ℕ) → (decodeDom e k) → ◯⟨ χ ⟩ ℕ
  decodeFromDom e zero z = ∣ p₁ e ∣
  decodeFromDom e (suc k) (nz , w) = hub (fst nz) λ s → decodeFromDom (fst (fst (w s))) k (snd (w s))

  decode : ℕ → ℕ → ∂ (◯⟨ χ ⟩ ℕ)
  ∂.domain (decode e k) = ¬¬resize (decodeDom e k)
  ∂.value (decode e k) z = decodeFromDom e k (decodeDomStable e k (¬¬resize-out z))
    where
      dom : decodeDom e k
      dom = decodeDomStable e k (¬¬resize-out z)

  decodeWellDefd : (e k : ℕ) → (z : decodeDom e k) → (decode e k ↓= decodeFromDom e k z)
  decodeWellDefd e k z = ↓=compose≡ (decode e k)
                                    (¬¬resize-in ((¬¬resize-in (decodeDomStable e k (¬¬resize-out (¬¬resize-in z)))) , refl))
                                      (cong (decodeFromDom e k)
                                            (decodeDomProp e k (decodeDomStable e k (¬¬resize-out (¬¬resize-in (decodeDomStable e k (¬¬resize-out (¬¬resize-in z))))))
                                            z))

  decodeWellDefdLemma : (e k n : ℕ) → (f : χ n ↓ → ◯⟨ χ ⟩ ℕ) →
                   (w : χ n ↓) → (u : φ e (fst w) ↓) → (decode (fst u) k ↓= f w) →
                   decode (pair (suc n) e) (suc k) ↓= hub n f
  decodeWellDefdLemma e k n f w u v = ↓=compose≡ (decode (pair (suc n) e) (suc k)) (decodeWellDefd (pair (suc n) e) (suc k) dom') (cong (hub n) (funExt (λ s → separated◯⟨⟩ χ separatedℕ separatedℕ _ _ (partialUnique (decode (fst u) k) (decodeWellDefd (fst u) k _) (↓=compose≡ (decode (fst u) k) v (cong f (∇defd-prop separatedℕ (χ n) w s)))))))
    where
      dom' : decodeDom (pair (suc n) e) (suc k)
      dom' = (n , +-comm n 1 ∙  sym (pairβ₀ _ _)) , λ w' → ((fst u) , ≡compose↓= (cong₂ φ (pairβ₁ _ _) (separatedℕ _ _ (∇.well-defd (χ n) _ _ (snd w') (snd w)))) (snd u)) , decodeDomStable (fst u) k ((¬¬resize-out v) >>= (¬¬resize-out ∘ fst))


  decodeSurj : (z : ◯⟨ χ ⟩ ℕ) → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= z)) ∥₁
  decodeSurj = NullPropElim (oDefd χ) (λ z → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= z)) ∥₁ , isPropPropTrunc) (λ n → ∣ (pair 0 n) , ¬¬-in (0 , (¬¬resize-in ((¬¬resize-in (pairβ₀ _ _)) , cong ∣_∣ (pairβ₁ _ _)))) ∣₁) step
    where
      step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ)  →
              ((s : χ n ↓) → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= f s)) ∥₁) →
              ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= hub n f)) ∥₁
      step n f ih = do
         esWithPf ← dnc (χ n) (λ s → Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= f s))) ih
         (e , eworks) ← ECT (λ m → record { domain = ∇.is-this (χ n) m ; value = λ z → fst (esWithPf (m , z)) })
         let w = do
           (m , u) ← ∇.almost-inh (χ n)
           let v = eworks m (fst (esWithPf (m , u)) , (¬¬resize-in (u , refl)))
           (k , x) ← snd (esWithPf (m , u))
           x' ← ¬¬resize-out x
           ¬¬-in (suc k , decodeWellDefdLemma e k n f (m , u) (fst (esWithPf (m , u)) ,
                     ≡compose↓= v (¬¬resize-in (u , refl))) (¬¬resize-in x'))
         ∣ (pair (suc n) e) , w ∣₁
            

  -- -- eth Turing machine halts on input n in < l steps given first l - 1 values of oracle but may halt on other fragments of χ
  -- ψ₀ : ℕ → ℕ → (l : ℕ) → ((k : Fin l) → initialSeg l k ↓) → Maybe ℕ
  -- ψ₀ e n l approx = ⊎rec (λ _ → nothing) (λ { ((l' , m) , p) → just m}) (finiteSearchMaybe l ℕ λ l' → φ₀ e (encodeℕwithVec→ℕ (n , (l , λ k → fst (approx k)))) (fst l'))
  
  -- -- eth Turing machine halts on input from the first l values of oracle in ≤ l steps and this does not occur for any smaller values of l
  -- ψ₁ : ℕ → ℕ → (l : ℕ) → ((k : Fin l) → initialSeg l k ↓) → Maybe ℕ 
  -- ψ₁ e n l approx = ⊎rec (λ _ → ψ₀ e n l approx) (λ _ → nothing) (finiteSearchMaybe l ℕ (λ l' → ψ₀ e n (fst l') λ {(k , p) → approx (k , (<-trans p (snd l')))}))

  -- ψ : ℕ → ℕ → ∇ ℕ
  -- ψ e n = {!!}

  
