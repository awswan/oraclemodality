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
open import ComputableChoice

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
  data haltingTime : Type where
    now : haltingTime
    later : ℕ → haltingTime → haltingTime


  data Code : Type where
    returnNat : ℕ → Code
    queryOracleAndContinue : ℕ → ℕ → Code

  postulate
    htctbl : Iso ℕ haltingTime
    Codectbl : Iso ℕ Code
    separatedHaltingTime : Separated haltingTime

  ℕ→Code : ℕ → Code
  ℕ→Code = Iso.fun Codectbl
  Code→ℕ : Code → ℕ
  Code→ℕ = Iso.inv Codectbl

  ℕ→HT : ℕ → haltingTime
  ℕ→HT = Iso.fun htctbl

  decodeAtDom : ℕ → haltingTime → Type
  decodeAtDom e now = p₀ e ≡ 0
  decodeAtDom e (later k t) =
    Σ[ (n , _) ∈ p₀ e > 0 ]
      ((w : χ n ↓) → Σ[ z ∈ isJust (φ₀ (p₁ e) (fst w) k) ] decodeAtDom (fromJust _ z) t)

  decodeAtDom' : Code → haltingTime → Type
  decodeAtDom' (returnNat x) now = Unit
  decodeAtDom' (queryOracleAndContinue _ _) now = ⊥
  decodeAtDom' (returnNat n) (later k t) = ⊥
  decodeAtDom' (queryOracleAndContinue n e) (later k t) =
    (w : χ n ↓) → Σ[ z ∈ isJust (φ₀ e (fst w) k) ] decodeAtDom' (ℕ→Code (fromJust _ z)) t

  isPropDecodeAtDom : {c : Code} {t : haltingTime} → isProp (decodeAtDom' c t)
  isPropDecodeAtDom {returnNat n} {now} = isPropUnit
  isPropDecodeAtDom {returnNat n} {later k t} = isProp⊥
  isPropDecodeAtDom {queryOracleAndContinue n e} {now} = isProp⊥
  isPropDecodeAtDom {queryOracleAndContinue n e} {later k t} = isPropΠ (λ _ → isPropΣ isPropIsJust (λ _ → isPropDecodeAtDom))

  haltingTimeUnique : {c : Code} (t t' : haltingTime) (d : decodeAtDom' c t) (d' : decodeAtDom' c t') → t ≡ t'
  haltingTimeUnique {returnNat x} now now d d' = refl
  haltingTimeUnique {returnNat x₁} now (later x t') d d' = ⊥rec d'
  haltingTimeUnique {queryOracleAndContinue n e} now (later k t') d d' = ⊥rec d
  haltingTimeUnique {queryOracleAndContinue n e} (later k t) (later k' t') d d' = separatedHaltingTime _ _ do
    z ← ∇.almost-inh (χ n)
    let kPath = φ₀-haltsOnce _ _ _ _ (fst (d z)) (fst (d' z))
    ¬¬-in (cong₂ later kPath (haltingTimeUnique t t' (transport (cong₂ (λ k ij → decodeAtDom' (ℕ→Code (fromJust (φ₀ e (fst z) k) ij)) t) kPath (isProp→PathP (λ _ → isPropIsJust) _ _)) (snd (d z))) (snd (d' z))))

-- Goal: decodeAtDom'
--       (Iso.fun Codectbl (fromJust (φ₀ e (fst z) k') (fst (d' z)))) t


  decodeAtDomDec : (e : ℕ) (t : haltingTime) → ◯⟨ χ ⟩ (Dec (decodeAtDom e t))
  decodeAtDomDec e now = ∣ discreteℕ _ _ ∣
  decodeAtDomDec e k'@(later k t) = do
    yes u@(n , _) ← ∣ <Dec 0 (p₀ e) ∣
      where no nz → ∣ no (λ {(z , _) → nz z}) ∣
    w ← query χ n
    yes z ← ∣ isJustDec (φ₀ (p₁ e) (fst w) k) ∣
      where no nz → ∣ no (λ {(u' , v) → nz (fst (v (subst (λ u → χ (fst u) ↓) (isProp≤ u u') w)))}) ∣
    yes ih ← decodeAtDomDec (fromJust _ z) t
      where no ¬ih → ∣ no (λ {(u' , v) → ¬ih (subst (λ z → decodeAtDom (fromJust _ z) t) (isPropIsJust _ z) (snd (v (subst (λ u → χ (fst u) ↓) (isProp≤ u u') w))))}) ∣
    ∣ yes (u , (λ w' → subst (λ w → Σ[ z ∈ isJust (φ₀ (p₁ e) (fst w) k) ] decodeAtDom (fromJust _ z) t) (∇defd-prop separatedℕ (χ n) w w') (z , ih))) ∣

  decodeAtDomDec' : (c : Code) (t : haltingTime) → ◯⟨ χ ⟩ (Dec (decodeAtDom' c t))
  decodeAtDomDec' (returnNat n) now = ∣ yes tt ∣
  decodeAtDomDec' (returnNat n) (later k t) = ∣ no (λ x → x) ∣
  decodeAtDomDec' (queryOracleAndContinue n e) now = ∣ no (λ x → x) ∣
  decodeAtDomDec' (queryOracleAndContinue n e) (later k t) = do
    w ← query χ n
    yes z ← ∣ isJustDec (φ₀ e (fst w) k) ∣
      where no ¬z → ∣ no (λ f → ¬z (fst (f w))) ∣
    yes p ← decodeAtDomDec' (ℕ→Code (fromJust _ z)) t
      where no ¬p → ∣ no (λ f → ¬p (subst (λ z → decodeAtDom' (ℕ→Code (fromJust (φ₀ e (fst w) k) z)) t) (isPropIsJust _ _) (snd (f w)))) ∣
    ∣ yes (λ w' → subst (λ w' → Σ-syntax (isJust (φ₀ e (fst w') k))
      (λ z₁ → decodeAtDom' (ℕ→Code (fromJust (φ₀ e (fst w') k) z₁)) t))
         (∇defd-prop separatedℕ (χ n) w w') (z , p)) ∣

  decodeAt : (e : ℕ) (t : haltingTime) → (decodeAtDom e t) → ◯⟨ χ ⟩ ℕ
  decodeAt e now z = ∣ p₁ e ∣
  decodeAt e (later k t) ((n , _) , v) = hub n λ w → decodeAt (fromJust (φ₀ (p₁ e) (fst w) k) (fst (v w))) t (snd (v w))

  decodeAt' : (c : Code) (t : haltingTime) → (decodeAtDom' c t) → ◯⟨ χ ⟩ ℕ
  decodeAt' (returnNat n) now d = ∣ n ∣
  decodeAt' (queryOracleAndContinue n e) (later k t) d =
    hub n (λ w → decodeAt' (ℕ→Code (fromJust _ (fst (d w)))) t (snd (d w)))

  decodeDom' : Code → Type
  decodeDom' e = ¬ ¬ (Σ[ k ∈ haltingTime ] (decodeAtDom' e k))

  computeHaltingTime : (c : Code) → ¬ ¬ (Σ[ k ∈ haltingTime ] decodeAtDom' c k) →
    ◯⟨ χ ⟩ (Σ[ k ∈ haltingTime ] decodeAtDom' c k)
  computeHaltingTime c p = natVersion >>= λ {(n , d) → ∣ (ℕ→HT n) , d ∣}
    where
      natVersion : ◯⟨ χ ⟩ (Σ[ n ∈ ℕ ] decodeAtDom' c (ℕ→HT n))
      natVersion = search χ (λ n → decodeAtDom' c (ℕ→HT n))
        (λ x → p (λ (t , d) → x ((Iso.inv htctbl t) , (subst (decodeAtDom' c) (sym (Iso.rightInv htctbl t)) d))))
        λ n → decodeAtDomDec' c (ℕ→HT n)

  decodeWithPath : (e : Code) → ⟨ ¬¬resize (Σ[ k ∈ haltingTime ] decodeAtDom' e k) ⟩ → Σ[ z ∈ ◯⟨ χ ⟩ ℕ ] ((k : haltingTime) → (w : decodeAtDom' e k) → z ≡ decodeAt' e k w)
  decodeWithPath e w = nullRec (isNullΣ (isNull-Null (oDefd χ)) (λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null (oDefd χ)))))) (λ x → x) fromOracle
    where
      fromOracle : ◯⟨ χ ⟩ (Σ[ z ∈ ◯⟨ χ ⟩ ℕ ] ((k : haltingTime) → (w : decodeAtDom' e k) → z ≡ decodeAt' e k w))
      fromOracle = do
        (k , d) ← computeHaltingTime e (¬¬resize-out w)
        ∣ (decodeAt' e k d) , (λ k' d' → cong₂ (decodeAt' e) (haltingTimeUnique _ _ d d') (isProp→PathP (λ _ → isPropDecodeAtDom) _ _)) ∣

  decode' : Code → ∂ (◯⟨ χ ⟩ ℕ)
  ∂.domain (decode' c) = ¬¬resize (Σ[ k ∈ haltingTime ] decodeAtDom' c k)
  ∂.value (decode' c) d = fst (decodeWithPath c d)


  decode : ℕ → ∂ (◯⟨ χ ⟩ ℕ)
  ∂.domain (decode e) = ¬¬resize (Σ[ k ∈ haltingTime ] (decodeAtDom e k))
  ∂.value (decode e) z = do
    (t , u) ← dom
    decodeAt e t u
    where
      haltsAt : ℕ → Type
      haltsAt k = decodeAtDom e (Iso.fun htctbl k)

      haltsAtDec : (k : ℕ) → ◯⟨ χ ⟩ (Dec (haltsAt k))
      haltsAtDec k = decodeAtDomDec e (Iso.fun htctbl k)

      haltsFirst : ◯⟨ χ ⟩ (Σ[ k ∈ ℕ ] haltsAt k)
      haltsFirst = search χ haltsAt (λ w → ¬¬resize-out z (λ {(t , u) → w ((Iso.inv htctbl t) , subst (λ t → decodeAtDom e t) (sym (Iso.rightInv htctbl t)) u)})) haltsAtDec

      dom : ◯⟨ χ ⟩ (Σ[ t ∈ haltingTime ] (decodeAtDom e t))
      dom = do
        (k , u) ← haltsFirst
        ∣ (Iso.fun htctbl k) , u ∣

  private
    fibreData : (z : ◯⟨ χ ⟩ ℕ) → Type
    fibreData z = (Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ t ∈ haltingTime ]  Σ[ d ∈ decodeAtDom' (ℕ→Code e) t ] decodeAt' (ℕ→Code e) t d ≡ z))
    fibreData' : (z : ◯⟨ χ ⟩ ℕ) → Type
    fibreData' z = (Σ[ e ∈ Code ] ¬ ¬ (Σ[ t ∈ haltingTime ]  Σ[ d ∈ decodeAtDom' e t ] decodeAt' e t d ≡ z))

  decodeSurj₀ : (z : ◯⟨ χ ⟩ ℕ) → ∥ fibreData' z ∥₁
  decodeSurj₀ = NullPropElim (oDefd χ) (λ z → ∥ fibreData' z ∥₁ , isPropPropTrunc)
    (λ n → ∣ returnNat n , (¬¬-in (now , tt , refl)) ∣₁) step
    where
      step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ) → ((w : χ n ↓) → ∥ fibreData' (f w) ∥₁) →
             ∥ fibreData' (hub n f) ∥₁
      step n f ih = do
        (e , eWorks) ← compChoice (λ m → ∇.is-this (χ n ) m) (λ m d e → ¬ ¬ (Σ[ t ∈ haltingTime ]  Σ[ d' ∈ decodeAtDom' (ℕ→Code e) t ] decodeAt' (ℕ→Code e) t d' ≡ f (m , d)))
                  λ m d → ih (m , d) >>= λ z →
                    ∣ (Code→ℕ (fst z)) , ¬¬-map (λ {(t , p) → t ,
                      subst (λ c → Σ[ t' ∈ decodeAtDom' c t ] decodeAt' c t t' ≡ f (m , d)) (sym (Iso.rightInv Codectbl (fst z))) p}) (snd z) ∣₁
        let w = do
          (m , u) ← ∇.almost-inh (χ n)
          let ((k , w) , v) = eWorks m u
          (t , (d' , p)) ← v
          let adjust = λ mu' → subst (λ mu' → Σ[ z ∈ isJust (φ₀ e (fst mu') (fst (fst (eWorks m u)))) ] decodeAtDom' (ℕ→Code (fromJust _ z)) t) (∇defd-prop separatedℕ (χ n) (m , u) mu') (w , d')
          ¬¬-in (later k t , adjust , cong (hub n) (funExt λ mu' → lemma e mu' (m , u) k t _ _ _ _ ∙∙ p ∙∙ cong f (∇defd-prop separatedℕ (χ n) _ _)))
        ∣ (queryOracleAndContinue n e) , w ∣₁
        where
          lemma : (e : ℕ) (mu mu' : χ n ↓) (k : ℕ) (t : haltingTime) (z : isJust (φ₀ e (fst mu) k)) (z' : isJust (φ₀ e (fst mu') k))
            (w : decodeAtDom' (ℕ→Code (fromJust (φ₀ e (fst mu) k) z)) t) (w' : decodeAtDom' (ℕ→Code (fromJust (φ₀ e (fst mu') k) z')) t) →
            decodeAt' (ℕ→Code (fromJust (φ₀ e (fst mu) k) z)) t w ≡ decodeAt' (ℕ→Code (fromJust (φ₀ e (fst mu') k) z')) t w'
          lemma e mu mu' k t z z' w w' i = decodeAt' (ℕ→Code (fromJust (φ₀ e (fst (muP i)) k) (zP i))) t (wP i)
            where
              muP : mu ≡ mu'
              muP = ∇defd-prop separatedℕ (χ n) mu mu'

              zP : PathP (λ i → isJust (φ₀ e (fst (muP i)) k)) z z'
              zP = isProp→PathP (λ _ → isPropIsJust) _ _

              wP : PathP (λ i → decodeAtDom' (ℕ→Code (fromJust (φ₀ e (fst (muP i)) k) (zP i))) t) w w'
              wP = isProp→PathP (λ _ → isPropDecodeAtDom) _ _

  decodeSurj : (z : ◯⟨ χ ⟩ ℕ) → ∥ Σ[ e ∈ Code ] decode' e ↓= z ∥₁
  decodeSurj z = do
    (e , w) ← decodeSurj₀ z
    let resizedDom = ¬¬resize-in-from¬¬ (¬¬-map (λ {(k , t , _) → (k , t)}) w)
    let p = do
      (t , d , q) ← w
      ¬¬-in (snd (decodeWithPath e resizedDom) t d ∙ q)
    ∣ e , resizedDom , separated◯⟨⟩ χ separatedℕ separatedℕ _ _ p ∣₁
    

-- Σ-syntax (isJust (φ₀ e (fst mu') (fst (fst (eWorks m u)))))
--       (λ z →
--          decodeAtDom'
--          (ℕ→Code (fromJust (φ₀ e (fst mu') (fst (fst (eWorks m u)))) z)) t)

-- Goal: decodeAt'
--       (ℕ→Code
--        (fromJust (φ₀ e (fst mu') (fst (fst (eWorks m u))))
--         (fst
--          (?0 (χ = χ) (n = n) (f = f) (ih = ih) (e = e) (eWorks = eWorks)
--           (m = m) (u = u) (t = t) (d' = d') (p = p) (mu' = mu')))))
--       t
--       (snd
--        (?0 (χ = χ) (n = n) (f = f) (ih = ih) (e = e) (eWorks = eWorks)
--         (m = m) (u = u) (t = t) (d' = d') (p = p) (mu' = mu')))
--       ≡ f mu'


-- Goal: decodeAt'
--       (ℕ→Code
--        (fromJust (φ₀ e (fst mu') k)
--         (fst
--          (subst

-- Σ-syntax (isJust (φ₀ e (fst mu') k))
--       (λ z₁ → decodeAtDom' (ℕ→Code (fromJust (φ₀ e (fst mu') k) z₁)) t)
    
  -- decodeSurj'' : (z : ◯⟨ χ ⟩ ℕ) → ∥ fibreData' z ∥₁
  -- decodeSurj'' = NullPropElim (oDefd χ) (λ z → ∥ fibreData' z ∥₁ , isPropPropTrunc)
  --   (λ n → ∣ (returnNat n) , (¬¬-in (now , (tt , refl))) ∣₁)
  --   step
  --   where
  --     step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ) → ((w : χ n ↓) → ∥ fibreData' (f w) ∥₁) →
  --            ∥ fibreData' (hub n f) ∥₁
  --     step n f ih = do
  --       esWithPrf ← sscc (λ m → ∇.is-this (χ n) m ) (λ m z → fibreData' (f (m , z)))
  --                        (λ m z → ih (m , z))
  --       (e , eWorks) ← ECT'' (λ m e' → (χ n ↓= m) → {!!}) {!!}
  --       {!!}


  -- decodeSurj' : (z : ◯⟨ χ ⟩ ℕ) → ∥ fibreData' z ∥₁
  -- decodeSurj' = NullPropElim (oDefd χ) (λ z → ∥ fibreData' z ∥₁ , isPropPropTrunc)
  --   (λ n → ∣ (returnNat n) , (¬¬-in (now , (tt , refl))) ∣₁)
  --   step
  --   where
  --     step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ) → ((w : χ n ↓) → ∥ fibreData' (f w) ∥₁) →
  --            ∥ fibreData' (hub n f) ∥₁
  --     step n f ih = do
  --       esWithPrf ← sscc (λ m → ∇.is-this (χ n) m ) (λ m z → fibreData' (f (m , z)))
  --                        (λ m z → ih (m , z))
  --       (e , eWorks) ← ECT' λ m → record { domain = ∇.is-this (χ n) m
  --                                          ; value = λ z → Iso.inv Codectbl (fst (esWithPrf m z)) }
  --       let w = do
  --         (m , u) ← ∇.almost-inh (χ n)
  --         let ((k , z) , q) = eWorks m ((Iso.inv Codectbl (fst (esWithPrf m u))) , ¬¬resize-in (u , refl))
  --         (t , (d , p)) ← snd (esWithPrf m u)
  --         ¬¬-in (later k t , (λ v → {!!} , {!!}) , (cong (hub n) (funExt (λ v' → {!!}))))
  --       ∣ (queryOracleAndContinue n e) , w ∣₁

  -- decodeSurj : (z : ◯⟨ χ ⟩ ℕ) → ∥ fibreData z ∥₁
  -- decodeSurj = NullPropElim (oDefd χ) (λ z → ∥ fibreData z ∥₁ , isPropPropTrunc )
  --              (λ n → ∣ (pair 0 n) , ¬¬-in (now , ((pairβ₀ 0 n) , cong ∣_∣ (pairβ₁ 0 n))) ∣₁)
  --              step
  --   where
  --     step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ) → ((w : χ n ↓) → ∥ fibreData (f w) ∥₁) →
  --            ∥ fibreData (hub n f) ∥₁

  --     step n f ih = do
  --       esWithPf ← sscc (λ m → ∇.is-this (χ n) m) (λ m z → fibreData (f (m , z)))
  --                       λ m z → ih (m , z)
  --       (e , eWorks) ← ECT' (λ m → record { domain = ∇.is-this (χ n) m
  --                                          ; value = λ z → fst (esWithPf m z) })
  --       let w = do
  --         (m , u) ← ∇.almost-inh (χ n)
  --         let ((k , v) , p) = eWorks m ((fst (esWithPf m u)) , ¬¬resize-in (u , refl))
  --         (t , (d , q)) ← snd (esWithPf m u)
  --         ¬¬-in ((later k t) , ((n , +-comm n 1 ∙ sym (pairβ₀ _ _)) , λ w' → {!!}) , cong (hub n) (funExt (λ w' → {!!})))
  --       ∣ (pair (suc n) e) , w ∣₁

--   {- domain of the decode function referred to as s' in Section VI -}
--   decodeDom : ℕ → ℕ → Type
--   decodeDom e zero = p₀ e ≡ 0
--   decodeDom e (suc k) = Σ[ z ∈ p₀ e > 0 ] ((w : χ (fst z) ↓) → Σ[ u ∈ φ (p₁ e) (fst w) ↓ ] decodeDom (fst u) k)

--   decodeDomProp : (e : ℕ) → (k : ℕ) → (u v : decodeDom e k) → u ≡ v
--   decodeDomProp e zero u v = isSetℕ _ _ u v
--   decodeDomProp e (suc k) u v = isPropΣ isProp≤ (λ _ → isPropΠ (λ _ → isPropΣ (φ-domainIsProp _ _) (λ _ → decodeDomProp _ k))) _ _

--   decodeDomStable : (e : ℕ) → (k : ℕ) → Stable (decodeDom e k)
--   decodeDomStable e zero = separatedℕ _ _
--   decodeDomStable e (suc k) p = z , (λ w → u w , decodeDomStable (fst (u w)) k (s w))
--     where
--       z : p₀ e > 0
--       z = ≤Stable _ _ (¬¬-map fst p)

--       p2 : (w : χ (fst z) ↓) → NonEmpty (Σ[ u ∈ φ (p₁ e) (fst w) ↓ ] decodeDom (fst u) k)
--       p2 w = do
--         (z' , f) ← p
--         ¬¬-in (f (subst (λ z'' → χ (fst z'') ↓) (isProp≤ z z') w))

--       u : (w : χ (fst z) ↓) → φ (p₁ e) (fst w) ↓
--       u w = φ-domainStable' (p₁ e) (fst w) (¬¬-map fst (p2 w))

--       s : (w : χ (fst z) ↓) → NonEmpty (decodeDom (fst (u w)) k)
--       s w = do
--         (u' , t) ← p2 w
--         ¬¬-in (subst (λ u'' → decodeDom (fst u'') k) (φ-domainIsProp _ _ u' (u w)) t)

--   decodeFromDom : (e k : ℕ) → (decodeDom e k) → ◯⟨ χ ⟩ ℕ
--   decodeFromDom e zero z = ∣ p₁ e ∣
--   decodeFromDom e (suc k) (nz , w) = hub (fst nz) λ s → decodeFromDom (fst (fst (w s))) k (snd (w s))

--   {- Called s' in Section VI. -} 
--   decodeAt : ℕ → ℕ → ∂ (◯⟨ χ ⟩ ℕ)
--   ∂.domain (decodeAt e k) = ¬¬resize (decodeDom e k)
--   ∂.value (decodeAt e k) z = decodeFromDom e k (decodeDomStable e k (¬¬resize-out z))
--     where
--       dom : decodeDom e k
--       dom = decodeDomStable e k (¬¬resize-out z)

--   decodeWellDefd : (e k : ℕ) → (z : decodeDom e k) → (decodeAt e k ↓= decodeFromDom e k z)
--   decodeWellDefd e k z = ↓=compose≡ (decodeAt e k)
--                                     (¬¬resize-in ((¬¬resize-in (decodeDomStable e k (¬¬resize-out (¬¬resize-in z)))) , refl))
--                                       (cong (decodeFromDom e k)
--                                             (decodeDomProp e k (decodeDomStable e k (¬¬resize-out (¬¬resize-in (decodeDomStable e k (¬¬resize-out (¬¬resize-in z))))))
--                                             z))

--   decodeWellDefdLemma : (e k n : ℕ) → (f : χ n ↓ → ◯⟨ χ ⟩ ℕ) →
--                    (w : χ n ↓) → (u : φ e (fst w) ↓) → (decodeAt (fst u) k ↓= f w) →
--                    decodeAt (pair (suc n) e) (suc k) ↓= hub n f
--   decodeWellDefdLemma e k n f w u v = ↓=compose≡ (decodeAt (pair (suc n) e) (suc k)) (decodeWellDefd (pair (suc n) e) (suc k) dom') (cong (hub n) (funExt (λ s → separated◯⟨⟩ χ separatedℕ separatedℕ _ _ (partialUnique (decodeAt (fst u) k) (decodeWellDefd (fst u) k _) (↓=compose≡ (decodeAt (fst u) k) v (cong f (∇defd-prop separatedℕ (χ n) w s)))))))
--     where
--       dom' : decodeDom (pair (suc n) e) (suc k)
--       dom' = (n , +-comm n 1 ∙  sym (pairβ₀ _ _)) , λ w' → ((fst u) , ≡compose↓= (cong₂ φ (pairβ₁ _ _) (separatedℕ _ _ (∇.well-defd (χ n) _ _ (snd w') (snd w)))) (snd u)) , decodeDomStable (fst u) k ((¬¬resize-out v) >>= (¬¬resize-out ∘ fst))

--   decodeAtDec : (e k : ℕ) → ◯⟨ χ ⟩ (Dec (decodeDom e k))
--   decodeAtDec e zero = ∣ discreteℕ _ _ ∣
--   decodeAtDec e (suc k) = decRec ifcondition1 (λ ¬c1 → ∣ no (λ w → ¬c1 (fst w)) ∣) (<Dec 0 (p₀ e))
--     where
--       ifcondition1 : (p₀ e > 0) → ◯⟨ χ ⟩ (Dec (decodeDom e (suc k)))
--       ifcondition1 z = do
--         w ← query χ (fst z)
       
--         ∣ {!!} ∣
  

--   decode : ℕ → ∂ (◯⟨ χ ⟩ ℕ)
--   ∂.domain (decode e) = ¬¬resize (Σ[ k ∈ ℕ ] decodeAt e k ↓)
--   ∂.value (decode e) = {!!}

--   {- Every element of ◯⟨ χ ⟩ ℕ can be coded by some natural number. Theorem VI.3 -}
--   decodeSurj : (z : ◯⟨ χ ⟩ ℕ) → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decodeAt e k ↓= z)) ∥₁
--   decodeSurj = NullPropElim (oDefd χ) (λ z → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decodeAt e k ↓= z)) ∥₁ , isPropPropTrunc) (λ n → ∣ (pair 0 n) , ¬¬-in (0 , (¬¬resize-in ((¬¬resize-in (pairβ₀ _ _)) , cong ∣_∣ (pairβ₁ _ _)))) ∣₁) step
--     where
--       step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ)  →
--               ((s : χ n ↓) → ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decodeAt e k ↓= f s)) ∥₁) →
--               ∥ Σ[ e ∈ ℕ ] ¬ ¬ (Σ[ k ∈ ℕ ] (decodeAt e k ↓= hub n f)) ∥₁
--       step n f ih = do
--          esWithPf ← sscc (λ m → ∇.is-this (χ n) m) (λ m z → Σ[ e ∈ ℕ ] (¬ ¬ (Σ[ k ∈ ℕ ] (decodeAt e k ↓= f (m , z))))) λ m z → ih (m , z)
--          (e , eworks) ← ECT (λ m → record { domain = ∇.is-this (χ n) m ; value = λ z → fst (esWithPf m  z) })
--          let w = do
--            (m , u) ← ∇.almost-inh (χ n)
--            let v = eworks m (fst (esWithPf m u) , (¬¬resize-in (u , refl)))
--            (k , x) ← snd (esWithPf m u)
--            x' ← ¬¬resize-out x
--            ¬¬-in (suc k , decodeWellDefdLemma e k n f (m , u) (fst (esWithPf m u) ,
--                      ≡compose↓= v (¬¬resize-in (u , refl))) (¬¬resize-in x'))
--          ∣ (pair (suc n) e) , w ∣₁
            
-- --  relCT : (f : ℕ → ∂ (◯⟨ χ ⟩ ℕ)) → ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (φ e n) >>= decode
