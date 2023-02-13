module RelativisedCT where

open import Includes

open import Cubical.Functions.Surjection

open import Axioms.NegativeResizing
open import Axioms.ChurchsThesis
open import Axioms.ComputableChoice

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

  decodeAtDomDec : (c : Code) (t : haltingTime) → ◯⟨ χ ⟩ (Dec (decodeAtDom c t))
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

  decodeAt : (c : Code) (t : haltingTime) → (decodeAtDom c t) → ◯⟨ χ ⟩ ℕ
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
    ◯⟨ χ ⟩ (Σ[ k ∈ haltingTime ] decodeAtDom c k)
  computeHaltingTime c p = natVersion >>= λ {(n , d) → ∣ (ℕ→HT n) , d ∣}
    where
      natVersion : ◯⟨ χ ⟩ (Σ[ n ∈ ℕ ] decodeAtDom c (ℕ→HT n))
      natVersion = search χ (λ n → decodeAtDom c (ℕ→HT n))
        (λ x → p (λ (t , d) → x ((Iso.inv htctbl t) , (subst (decodeAtDom c) (sym (Iso.rightInv htctbl t)) d))))
        λ n → decodeAtDomDec c (ℕ→HT n)

  decodeWithPath : (e : Code) → ⟨ ¬¬resize (Σ[ k ∈ haltingTime ] decodeAtDom e k) ⟩ → Σ[ z ∈ ◯⟨ χ ⟩ ℕ ] ((k : haltingTime) → (w : decodeAtDom e k) → z ≡ decodeAt e k w)
  decodeWithPath e w = nullRec (isNullΣ (isNull-Null (oDefd χ)) (λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null (oDefd χ)))))) (λ x → x) fromOracle
    where
      fromOracle : ◯⟨ χ ⟩ (Σ[ z ∈ ◯⟨ χ ⟩ ℕ ] ((k : haltingTime) → (w : decodeAtDom e k) → z ≡ decodeAt e k w))
      fromOracle = do
        (k , d) ← computeHaltingTime e (¬¬resize-out w)
        ∣ (decodeAt e k d) , (λ k' d' → cong₂ (decodeAt e) (haltingTimeUnique _ _ d d') (isProp→PathP (λ _ → isPropDecodeAtDom) _ _)) ∣

  private
    fibreData' : (z : ◯⟨ χ ⟩ ℕ) → Type
    fibreData' z = (Σ[ e ∈ Code ] ¬ ¬ (Σ[ t ∈ haltingTime ]  Σ[ d ∈ decodeAtDom e t ] decodeAt e t d ≡ z))


  decodeSurj₀ : (z : ◯⟨ χ ⟩ ℕ) → ∥ fibreData' z ∥₁
  decodeSurj₀ = NullPropElim (oDefd χ) (λ z → ∥ fibreData' z ∥₁ , isPropPropTrunc)
    (λ n → ∣ returnNat n , (¬¬-in (now , tt , refl)) ∣₁) step
    where
      step : (n : ℕ) (f : χ n ↓ → ◯⟨ χ ⟩ ℕ) → ((w : χ n ↓) → ∥ fibreData' (f w) ∥₁) →
             ∥ fibreData' (hub n f) ∥₁
      step n f ih = do
        (e , eWorks) ← compChoice (λ m → ∇.is-this (χ n ) m) (λ m d e → ¬ ¬ (Σ[ t ∈ haltingTime ]  Σ[ d' ∈ decodeAtDom (ℕ→Code e) t ] decodeAt (ℕ→Code e) t d' ≡ f (m , d)))
                  λ m d → ih (m , d) >>= λ z →
                    ∣ (Code→ℕ (fst z)) , ¬¬-map (λ {(t , p) → t ,
                      subst (λ c → Σ[ t' ∈ decodeAtDom c t ] decodeAt c t t' ≡ f (m , d)) (sym (Iso.rightInv Codectbl (fst z))) p}) (snd z) ∣₁
        let w = do
          (m , u) ← ∇.almost-inh (χ n)
          let ((k , w) , v) = eWorks m u
          (t , (d' , p)) ← v
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

  abstract -- otherwise type checking seems to get stuck
    decode : Code → ∂ (◯⟨ χ ⟩ ℕ)
    ∂.domain (decode c) = ¬¬resize (Σ[ k ∈ haltingTime ] decodeAtDom c k)
    ∂.value (decode c) d = fst (decodeWithPath c d)

    decodeSurj : (z : ◯⟨ χ ⟩ ℕ) → ∥ Σ[ e ∈ Code ] decode e ↓= z ∥₁
    decodeSurj z = do
      (e , w) ← decodeSurj₀ z
      let resizedDom = ¬¬resize-in-from¬¬ (¬¬-map (λ {(k , t , _) → (k , t)}) w)
      let p = do
        (t , d , q) ← w
        ¬¬-in (snd (decodeWithPath e resizedDom) t d ∙ q)
      ∣ e , resizedDom , separated◯⟨⟩ χ separatedℕ separatedℕ _ _ p ∣₁

  ψ : ℕ → ℕ → ∂ (◯⟨ χ ⟩ ℕ)
  ψ e n = φ e n >>= (decode ∘ ℕ→Code)

  relativisedECT : (f : ℕ → ∂ (◯⟨ χ ⟩ ℕ)) →
    ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → (z : f n ↓) → ψ e n ↓= ∂.value (f n) z) ∥₁
  relativisedECT f = do
    (e , g) ← compChoice (λ n → ∂.domain (f n))
                         (λ n z e → decode (ℕ→Code e) ↓= ∂.value (f n) z)
                         λ n z → decodeSurj (∂.value (f n) z) >>=
                           λ {(c , u) → ∣ (Code→ℕ c) , (subst (λ c → decode c ↓= ∂.value (f n) z) (sym (Iso.rightInv Codectbl c)) u) ∣₁}
    ∣ e , (λ n z → (fst (lemma2 e n z (g n z))) ,
             (snd (lemma2 e n z (g n z)) ∙∙ cong₂ (λ x y → ∂.value (decode (ℕ→Code (φ-fromDomain e n x))) y) (φ-isPropDomain _ _) (isProp→PathP (λ _ → Ω¬¬-props _) _ _) ∙∙ snd (snd (g n z)))) ∣₁
    where
      lemma : (e : ℕ) (n : ℕ) (z : f n ↓)
        (fgnz : φ-domain e n) →
        ⟨ ∂.domain (decode (ℕ→Code (φ-fromDomain e n fgnz))) ⟩ →
        ⟨ ∂.domain (decode (ℕ→Code (φ-fromDomain e n (φ-domainStable (¬¬resize-out (¬¬resize-in fgnz)))))) ⟩
      lemma e n z fgnz = subst (λ x → ⟨ ∂.domain (decode (ℕ→Code (φ-fromDomain e n x))) ⟩)
        (φ-isPropDomain _ _)
      lemma2 : (e : ℕ) (n : ℕ) (z : f n ↓) →
        (gnz : Σ[ d ∈ φ-domain e n ] (decode (ℕ→Code (φ-fromDomain e n d)) ↓= ∂.value (f n) z)) →
        ψ e n ↓= ∂.value (decode (ℕ→Code (∂.value (φ e n) (¬¬resize-in (fst gnz)))))
        (lemma e n z (fst gnz) (fst (snd gnz)))
      lemma2 e n z gnz = ∂bindDesc (φ e n) (decode ∘ ℕ→Code) (¬¬resize-in (fst gnz))
                                      (lemma e n z (fst gnz) (fst (snd gnz)))

  relativisedCT : (f : ℕ → ◯⟨ χ ⟩ ℕ) →
    ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → ψ e n ↓= f n) ∥₁
  relativisedCT f = do
    (e , h) ← relativisedECT (λ n → ι (f n))
    ∣ e , (λ n → h n (ιdefd (f n))) ∣₁

  TuringJump : (ℕ × ℕ) → ∇ ℕ
  TuringJump (e , n) = byCases (ψ e n ↓) 1 0

  diag : ℕ → ∇ ℕ
  diag e = byCases (ψ e e ↓= ∣ 0 ∣) 1 0

  diagNonComputable₀ : (f : ℕ → ◯⟨ χ ⟩ ℕ) → diag ≡ erase χ separatedℕ ∘ f → ⊥
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
      mWithPath : (n : ℕ) → Σ[ m ∈ ◯⟨ χ ⟩ ℕ ] (diag n ≡ erase χ separatedℕ m)
      mWithPath n = nullRec (isNullΣ (isNull-Null (oDefd χ)) (λ _ → isNull≡ (¬¬Sheaf→Null {χ = χ} separatedℕ ∇isSheaf)))
                          (λ (m , p) → ∣ m ∣ , ∇-defd→path (diag n) m p) (red n)
