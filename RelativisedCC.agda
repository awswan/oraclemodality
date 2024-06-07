module RelativisedCC where

open import Includes

open import Cubical.Functions.Surjection
open import Cubical.Data.List hiding ([_] ; rec)

open import Axioms.NegativeResizing
open import Axioms.ComputableChoice

open import Util.PartialElements
open import Util.StablePartial
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import Util.HasUnderlyingType
open import Util.PropTruncationModalInstance
open import Util.LexNull
open import Util.Nullification
open import Util.Encodings
open import Util.Misc

open import OracleModality
open import DoubleNegationSheaves

module _ (χ : Oracle ℕ ℕ) where
  decodeAtDom : Code → haltingTime → Type
  decodeAtDom (returnNat x) now = Unit
  decodeAtDom (queryOracleAndContinue _ _) now = ⊥
  decodeAtDom (returnNat n) (later k t) = ⊥
  decodeAtDom (queryOracleAndContinue n e) (later k t) =
    (w : χ n ↓) → Σ[ z ∈ isJust (φ₀ e (fst w) k) ] decodeAtDom (ℕ→Code (fromJust _ z)) t

  isPropDecodeAtDom : {c : Code} {t : haltingTime} → isProp (decodeAtDom c t)
  isPropDecodeAtDom {returnNat n} {now} = isPropUnit
  isPropDecodeAtDom {returnNat n} {later k t} = isProp⊥
  isPropDecodeAtDom {queryOracleAndContinue n e} {now} = isProp⊥
  isPropDecodeAtDom {queryOracleAndContinue n e} {later k t} = isPropΠ (λ _ → isPropΣ isPropIsJust (λ _ → isPropDecodeAtDom))

  haltingTimeUnique : {c : Code} (t t' : haltingTime) (d : decodeAtDom c t) (d' : decodeAtDom c t') → t ≡ t'
  haltingTimeUnique {returnNat x} now now d d' = refl
  haltingTimeUnique {returnNat x₁} now (later x t') d d' = ⊥rec d'
  haltingTimeUnique {queryOracleAndContinue n e} now (later k t') d d' = ⊥rec d
  haltingTimeUnique {queryOracleAndContinue n e} (later k t) (later k' t') d d' = separatedHaltingTime _ _ do
    z ← ∇.almost-inh (χ n)
    let kPath = φ₀-haltsOnce _ _ _ _ (fst (d z)) (fst (d' z))
    ¬¬-in (cong₂ later kPath (haltingTimeUnique t t' (transport (cong₂ (λ k ij → decodeAtDom (ℕ→Code (fromJust (φ₀ e (fst z) k) ij)) t) kPath (isProp→PathP (λ _ → isPropIsJust) _ _)) (snd (d z))) (snd (d' z))))

  decodeAtDomDec : (c : Code) (t : haltingTime) → ◯[ χ ] (Dec (decodeAtDom c t))
  decodeAtDomDec (returnNat n) now = ∣ yes tt ∣
  decodeAtDomDec (returnNat n) (later k t) = ∣ no (λ x → x) ∣
  decodeAtDomDec (queryOracleAndContinue n e) now = ∣ no (λ x → x) ∣
  decodeAtDomDec (queryOracleAndContinue n e) (later k t) = do
    w ← query χ n
    yes z ← ∣ isJustDec (φ₀ e (fst w) k) ∣
      where no ¬z → ∣ no (λ f → ¬z (fst (f w))) ∣
    yes p ← decodeAtDomDec (ℕ→Code (fromJust _ z)) t
      where no ¬p → ∣ no (λ f → ¬p (subst (λ z → decodeAtDom (ℕ→Code (fromJust (φ₀ e (fst w) k) z)) t) (isPropIsJust _ _) (snd (f w)))) ∣
    ∣ yes (λ w' → subst (λ w' → Σ-syntax (isJust (φ₀ e (fst w') k))
      (λ z₁ → decodeAtDom (ℕ→Code (fromJust (φ₀ e (fst w') k) z₁)) t))
         (∇defd-prop separatedℕ (χ n) w w') (z , p)) ∣

  decodeAt : (c : Code) (t : haltingTime) → (decodeAtDom c t) → ◯[ χ ] ℕ
  decodeAt (returnNat n) now d = ∣ n ∣
  decodeAt (queryOracleAndContinue n e) (later k t) d =
    hub n (λ w → decodeAt (ℕ→Code (fromJust _ (fst (d w)))) t (snd (d w)))

  decodeAtUnique : {c c' : Code} (p : c ≡ c') (t t' : haltingTime) (d : decodeAtDom c t)
    (d' : decodeAtDom c' t') → (decodeAt c t d ≡ decodeAt c' t' d')
  decodeAtUnique p t t' d d' i = decodeAt (p i) (tPath i) (dPath i)
    where
      tPath : t ≡ t'
      tPath = haltingTimeUnique t t' (subst (λ c → decodeAtDom c t) p d) d'

      dPath : PathP (λ i → decodeAtDom (p i) (tPath i)) d d'
      dPath = isProp→PathP (λ _ → isPropDecodeAtDom) d d'

  decodeDom : Code → Type
  decodeDom e = ¬ ¬ (Σ[ k ∈ haltingTime ] (decodeAtDom e k))

  computeHaltingTime : (c : Code) → ¬ ¬ (Σ[ k ∈ haltingTime ] decodeAtDom c k) →
    ◯[ χ ] (Σ[ k ∈ haltingTime ] decodeAtDom c k)
  computeHaltingTime c p = natVersion >>= λ {(n , d) → ∣ (ℕ→HT n) , d ∣}
    where
      natVersion : ◯[ χ ] (Σ[ n ∈ ℕ ] decodeAtDom c (ℕ→HT n))
      natVersion =
        search-unique χ
                      ((λ n → decodeAtDom c (ℕ→HT n)))
                      (λ n m x y → equiv→Inj (snd (invEquiv haltingTimeCtbl))
                        (haltingTimeUnique _ _ x y))
                        ((λ x → p (λ (t , d) →
                          x ((fst haltingTimeCtbl t) ,
                            (subst (decodeAtDom c) (sym (retEq haltingTimeCtbl t)) d)))))
                            (λ n → decodeAtDomDec c (ℕ→HT n))

  abstract -- otherwise type checking seems to get stuck
    decodeWithPath : (e : Code) → ⟨ ¬¬resize (Σ[ k ∈ haltingTime ] decodeAtDom e k) ⟩ → Σ[ z ∈ ◯[ χ ] ℕ ] ((k : haltingTime) → (w : decodeAtDom e k) → z ≡ decodeAt e k w)
    decodeWithPath e w = nullRec (isNullΣ (isNull-Null (oDefd χ)) (λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null (oDefd χ)))))) (λ x → x) fromOracle
      where
        fromOracle : ◯[ χ ] (Σ[ z ∈ ◯[ χ ] ℕ ] ((k : haltingTime) → (w : decodeAtDom e k) → z ≡ decodeAt e k w))
        fromOracle = do
          (k , d) ← computeHaltingTime e (¬¬resize-out w)
          ∣ (decodeAt e k d) , (λ k' d' → cong₂ (decodeAt e) (haltingTimeUnique _ _ d d') (isProp→PathP (λ _ → isPropDecodeAtDom) _ _)) ∣

  private
    fibreData : (z : ◯[ χ ] ℕ) → Type
    fibreData z = (Σ[ e ∈ Code ] ¬ ¬ (Σ[ t ∈ haltingTime ]  Σ[ d ∈ decodeAtDom e t ] decodeAt e t d ≡ z))

  decodeSurj₀ : (z : ◯[ χ ] ℕ) → ∥ fibreData z ∥₁
  decodeSurj₀ = NullPropElim (oDefd χ) (λ z → ∥ fibreData z ∥₁ , isPropPropTrunc)
    (λ n → ∣ returnNat n , (¬¬-in (now , tt , refl)) ∣₁) step
    where
      step : (n : ℕ) (f : χ n ↓ → ◯[ χ ] ℕ) → ((w : χ n ↓) → ∥ fibreData (f w) ∥₁) →
             ∥ fibreData (hub n f) ∥₁
      step n f ih = do
        (e , eWorks) ← ComputableChoice (λ m → ∇.is-this (χ n) m) (λ m d e → ¬¬resize (Σ[ t ∈ haltingTime ] (Σ[ d' ∈ decodeAtDom (ℕ→Code e) t ] decodeAt (ℕ→Code e) t d' ≡ f (m , d))))
          λ m d → ih (m , d) >>= λ z → ∣ (Code→ℕ (fst z)) ,
            (¬¬resize-in-from¬¬ (¬¬-map (λ {(t , p) → t , subst (λ c → Σ[ t' ∈ decodeAtDom c t ] decodeAt c t t' ≡ f (m , d)) (sym (retEq CodeCtbl (fst z))) p}) (snd z))) ∣₁
        let w = do
          (m , u) ← ∇.almost-inh (χ n)
          let ((k , w) , v) = eWorks m u
          (t , (d' , p)) ← ¬¬resize-out v
          let adjust = λ mu' → subst (λ mu' → Σ[ z ∈ isJust (φ₀ e (fst mu') (fst (fst (eWorks m u)))) ] decodeAtDom (ℕ→Code (fromJust _ z)) t)
                                        (∇defd-prop separatedℕ (χ n) (m , u) mu') (w , d')
          ¬¬-in (later k t , adjust , cong (hub n) (funExt λ mu' → lemma _ mu' (m , u) _ _ _ _ _ _ ∙∙ p ∙∙ cong f (∇defd-prop separatedℕ (χ n) _ _)))
        ∣ (queryOracleAndContinue n e) , w ∣₁
        where
          lemma : (e : ℕ) (mu mu' : χ n ↓) (k : ℕ) (t : haltingTime) (z : isJust (φ₀ e (fst mu) k)) (z' : isJust (φ₀ e (fst mu') k))
            (w : decodeAtDom (ℕ→Code (fromJust (φ₀ e (fst mu) k) z)) t) (w' : decodeAtDom (ℕ→Code (fromJust (φ₀ e (fst mu') k) z')) t) →
            decodeAt (ℕ→Code (fromJust (φ₀ e (fst mu) k) z)) t w ≡ decodeAt (ℕ→Code (fromJust (φ₀ e (fst mu') k) z')) t w'
          lemma e mu mu' k t z z' w w' i = decodeAt (ℕ→Code (fromJust (φ₀ e (fst (muP i)) k) (zP i))) t (wP i)
            where
              muP : mu ≡ mu'
              muP = ∇defd-prop separatedℕ (χ n) mu mu'

              zP : PathP (λ i → isJust (φ₀ e (fst (muP i)) k)) z z'
              zP = isProp→PathP (λ _ → isPropIsJust) _ _

              wP : PathP (λ i → decodeAtDom (ℕ→Code (fromJust (φ₀ e (fst (muP i)) k) (zP i))) t) w w'
              wP = isProp→PathP (λ _ → isPropDecodeAtDom) _ _

  decode : Code → ∂ (◯[ χ ] ℕ)
  ∂.domain (decode c) = ¬¬resize (Σ[ k ∈ haltingTime ] decodeAtDom c k)
  ∂.value (decode c) d = fst (decodeWithPath c d)

  decodeSurj : (z : ◯[ χ ] ℕ) → ∥ Σ[ e ∈ Code ] decode e ↓= z ∥₁
  decodeSurj z = do
      (e , w) ← decodeSurj₀ z
      let resizedDom = ¬¬resize-in-from¬¬ (¬¬-map (λ {(k , t , _) → (k , t)}) w)
      let p = do
        (t , d , q) ← w
        ¬¬-in (snd (decodeWithPath e resizedDom) t d ∙ q)
      ∣ e , resizedDom , separated◯[] χ separatedℕ separatedℕ _ _ p ∣₁

  ψ : ℕ → ℕ → ∂ (◯[ χ ] ℕ)
  ψ e n = φ e n >>= (decode ∘ ℕ→Code)

  decodeCtbl : (z : ◯[ χ ] ℕ) → ∥ Σ[ n ∈ ℕ ] (decode (ℕ→Code n) ↓= z) ∥₁
  decodeCtbl z = do
    (c , u) ← decodeSurj z
    ∣ (Code→ℕ c) , (subst (λ c → decode c ↓= z) (sym (retEq CodeCtbl c)) u) ∣₁

  relativisedECT : (f : ℕ → ∂ (◯[ χ ] ℕ)) →
    ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (z : f n ↓) → ψ e n ↓= ∂.value (f n) z) ∥₁
  relativisedECT f = do
    (e , g) ← generalisedComputableChoice (◯[ χ ] ℕ) (decode ∘ ℕ→Code) decodeCtbl (λ n → ∂.domain (f n)) (λ n d z → ¬¬resize (z ≡ ∂.value (f n) d))
      λ n d → ∣ (∂.value (f n) d) , (¬¬resize-in refl) ∣₁
    ∣ e , (λ n d → (¬¬resize-in ((¬¬resize-in (fst (g n d))) , ¬¬resize-in-from¬¬ (¬¬-map (λ (k , u) → k , subst (λ u → decodeAtDom (ℕ→Code (φ-fromDomain e n u)) k) (φ-isPropDomain _ _) u) (¬¬resize-out (fst (snd (g n d))))))) , snd (∂bindDesc (φ e n) (decode ∘ ℕ→Code) (¬¬resize-in (fst (g n d))) (¬¬resize-in-from¬¬ (¬¬-map (λ (k , u) → k , subst (λ u → decodeAtDom (ℕ→Code (φ-fromDomain e n u)) k) (φ-isPropDomain _ _) u) (¬¬resize-out (fst (snd (g n d))))))) ∙∙ cong₂ (λ u v → fst (decodeWithPath (ℕ→Code (φ-fromDomain e n u)) v)) (φ-isPropDomain _ _) (isProp→PathP (λ _ → Ω¬¬-props _) _ _) ∙∙ separated◯[] χ separatedℕ separatedℕ _ _ (¬¬resize-out (snd (snd (g n d))))) ∣₁

  relativisedCT : (f : ℕ → ◯[ χ ] ℕ) →
    ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → ψ e n ↓= f n) ∥₁
  relativisedCT f = do
    (e , h) ← relativisedECT (λ n → ι (f n))
    ∣ e , (λ n → h n (¬¬resize-in tt)) ∣₁

  TuringJump : (ℕ × ℕ) → ∇ ℕ
  TuringJump (e , n) = byCases (ψ e n ↓) 1 0

  diag : ℕ → ∇ ℕ
  diag e = byCases (ψ e e ↓= ∣ 0 ∣) 1 0

  diagNonComputable₀ : (f : ℕ → ◯[ χ ] ℕ) → diag ≡ erase χ separatedℕ ∘ f → ⊥
  diagNonComputable₀ f p = rec isProp⊥ (λ x → x) do
    (e , h) ← relativisedCT f
    ∣ contr e (h e) ∣₁
    where
      ifzero : (e : ℕ) → (z : ψ e e ↓= f e) →
        (∂.value (ψ e e) (fst z) ≡ ∣ 0 ∣) → ⊥
      ifzero e z q = znots (separatedℕ _ _ (∇.well-defd (diag e) _ _ isZ isOne))
        where
          isOne : diag e ↓= 1
          isOne = byCasesβ⊤ (ψ e e ↓= ∣ 0 ∣) 1 0 (fst z , q)

          p' : diag e ≡ erase χ separatedℕ ∣ 0 ∣
          p' = funExt⁻ p e ∙ cong (erase χ separatedℕ) (sym (snd z) ∙ q)

          isZ : diag e ↓= 0
          isZ = subst (λ x → x ↓= 0) (sym p') (¬¬resize-in refl)

      contr : (e : ℕ) → (z : ψ e e ↓= f e) → ⊥
      contr e z = q (fst isZ') (snd isZ')
        where
          q : (w : ⟨ ∂.domain (ψ e e) ⟩) → (∂.value (ψ e e) w ≡ ∣ 0 ∣) → ⊥
          q w u = ifzero e z (cong (∂.value (ψ e e)) (Ω¬¬-props _ _ _) ∙ u)
        
          isZ : diag e ↓= 0
          isZ = byCasesβ⊥ (ψ e e ↓= ∣ 0 ∣) 1 0 λ r → q (fst r) (snd r)

          isZ' : ψ e e ↓= ∣ 0 ∣
          isZ' = (fst z) , (
            ∂.value (ψ e e) (fst z)
              ≡⟨ snd z ⟩
            f e
              ≡⟨ eraseInj χ separatedℕ separatedℕ (sym (funExt⁻ p e) ∙ ∇-defd→path (diag e) 0 isZ) ⟩
            ∣ 0 ∣
              ∎
            )

  diagNonComputable : ¬ (diag ≤T χ)
  diagNonComputable (Tred red) = diagNonComputable₀ (fst ∘ mWithPath) (funExt (λ n → snd (mWithPath n)))
    where
      mWithPath : (n : ℕ) → Σ[ m ∈ ◯[ χ ] ℕ ] (diag n ≡ erase χ separatedℕ m)
      mWithPath n = nullRec (isNullΣ (isNull-Null (oDefd χ)) (λ _ → isNull≡ (¬¬Sheaf→Null {χ = χ} separatedℕ ∇isSheaf)))
                          (λ (m , p) → ∣ m ∣ , ∇-defd→path (diag n) m p) (red n)
