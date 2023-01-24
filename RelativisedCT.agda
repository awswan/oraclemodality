module RelativisedCT where

open import Includes

open import Cubical.Functions.Surjection

open import Axioms.NegativeResizing
open import Axioms.ChurchsThesis
open import Axioms.StableSubcountableChoice

open import Util.PartialElements
open import Util.StablePartial
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import Util.HasUnderlyingType
open import Util.PropTruncationModalInstance
open import Util.LexNull
open import Util.Nullification

open import OracleModality
open import DoubleNegationSheaves

{- We need a pairing function, but don't care what it looks like, so just postulate one -}
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

module _ (χ : Oracle ℕ ℕ) where
  {- domain of the decode function referred to as s in Section VI -}
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

  {- Called s' in Section VI. -} 
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


  {- Every element of ◯⟨ χ ⟩ ℕ can be coded by some natural number. Theorem VI.3 -}
  decodeSurj : (z : ◯⟨ χ ⟩ ℕ) → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= z)) ∥₁
  decodeSurj = NullPropElim (oDefd χ) (λ z → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= z)) ∥₁ , isPropPropTrunc) (λ n → ∣ (pair 0 n) , ¬¬-in (0 , (¬¬resize-in ((¬¬resize-in (pairβ₀ _ _)) , cong ∣_∣ (pairβ₁ _ _)))) ∣₁) step
    where
      step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ)  →
              ((s : χ n ↓) → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= f s)) ∥₁) →
              ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= hub n f)) ∥₁
      step n f ih = do
         esWithPf ← sscc (λ m → ∇.is-this (χ n) m) (λ m z → Σ[ e ∈ ℕ ] (¬ ¬ (Σ[ k ∈ ℕ ] (decode e k ↓= f (m , z))))) λ m z → ih (m , z)
         (e , eworks) ← ECT (λ m → record { domain = ∇.is-this (χ n) m ; value = λ z → fst (esWithPf m  z) })
         let w = do
           (m , u) ← ∇.almost-inh (χ n)
           let v = eworks m (fst (esWithPf m u) , (¬¬resize-in (u , refl)))
           (k , x) ← snd (esWithPf m u)
           x' ← ¬¬resize-out x
           ¬¬-in (suc k , decodeWellDefdLemma e k n f (m , u) (fst (esWithPf m u) ,
                     ≡compose↓= v (¬¬resize-in (u , refl))) (¬¬resize-in x'))
         ∣ (pair (suc n) e) , w ∣₁
            
