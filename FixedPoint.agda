module FixedPoint where

open import Includes hiding (_≤_)

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Data.Sigma

open import Cubical.Functions.Surjection

open import Util.StablePartial
open import Util.PartialElements
open import Util.ModalOperatorSugar
open import Util.PropTruncationModalInstance
open import Util.DoubleNegation
open import Util.HasUnderlyingType

open import Axioms.ChurchsThesis
open import Axioms.MarkovInduction
open import Axioms.NegativeResizing

record PosetStr (P : Type) : Type (ℓ-suc ℓ-zero) where
  field
    _≤_ : P → P → Type

open PosetStr ⦃...⦄ public

instance
  ∂ℕPoset : {Y : Type} → PosetStr (∂ Y)
  PosetStr._≤_ ∂ℕPoset μ ν =
    (m : μ ↓) → ν ↓= ∂.value μ m

  PointwisePoset : {X Y : Type} ⦃ XPoset : PosetStr X ⦄ → PosetStr (Y → X)
  PosetStr._≤_ (PointwisePoset {Y = Y}) f g = (y : Y) → f y ≤ g y
  
ECT≤ : (f : ℕ → ∂ ℕ) → ∥ (Σ[ e ∈ ℕ ] f ≤ φ e) ∥₁
ECT≤ = ECT

module Fixed {X Y : Type} ⦃ PosetY : PosetStr Y ⦄
  (s : X → (X → Y)) (sDense : (f : X → Y) → ∥ Σ[ x₀ ∈ X ] ((x : X) → f x ≤ s x₀ x) ∥₁)
  (F : Y → Y) where
  
  t : X → Y
  t x = F (s x x)
  
  fixed : ∥ Σ[ y ∈ Y ] F y ≤ y ∥₁
  fixed = truncMap (λ (x₀ , p) → (s x₀ x₀) , (p x₀)) (sDense t)

  ifMaximal : ((x y : Y) → F x ≤ y → F x ≡ y) → ∥ Σ[ y ∈ Y ] F y ≡ y ∥₁
  ifMaximal maximalF = map (λ (x₀ , p) → s x₀ x₀ , maximalF _ _ (p x₀)) (sDense t)


fixed3 : (F : ℕ → (ℕ → ∂ ℕ)) → ∥ Σ[ e ∈ ℕ ] F e ≤ φ e ∥₁
fixed3 F = do
  (diagCode , f) ← diagCompute
  let e = φ-fromDomain diagCode diagCode (fst (f diagCode))
  ∣ e , (λ n u → fst (snd (f diagCode) n (¬¬resize-in ((fst (f diagCode)) , u))) ,
           snd (snd (f diagCode) n (¬¬resize-in ((fst (f diagCode)) , u))) ∙
             diagExplicit diagCode n (fst (f diagCode)) u) ∣₁
  where
    diag : ℕ → (ℕ → ∂ ℕ)
    ∂.domain (diag e n) =
      ¬¬resize (Σ[ u ∈ φ-domain e e ] ⟨ ∂.domain (F (φ-fromDomain e e u) n) ⟩)
    ∂.value (diag e n) u = ∂.value (F (φ-fromDomain e e d) n) v
      where
        d : φ-domain e e
        d = φ-domainStable (¬¬-map fst (¬¬resize-out u))

        v : ⟨ ∂.domain (F (φ-fromDomain e e d) n) ⟩
        v = Ω¬¬-stab _ do
          (d' , v') ← ¬¬resize-out u
          ¬¬-in (subst (λ d'' → ⟨ ∂.domain (F (φ-fromDomain e e d'') n) ⟩)
            (φ-isPropDomain d' d) v')

    diagExplicit : (e : ℕ) → (n : ℕ) → (u : φ-domain e e) →
      (v : ⟨ ∂.domain (F (φ-fromDomain e e u) n) ⟩) →
      ∂.value (diag e n) (¬¬resize-in (u , v)) ≡ ∂.value (F (φ-fromDomain e e u) n) v

    diagExplicit e n u v = cong₂ (λ u' v' → ∂.value (F (φ-fromDomain e e u') n) v')
      (φ-isPropDomain _ _) (isProp→PathP (λ _ → Ω¬¬-props _) _ _)

    diagCompute :
      ∥ Σ[ diagCode ∈ ℕ ] ((e : ℕ) →
        Σ[ u ∈ φ-domain diagCode e ] (diag e ≤ φ (φ-fromDomain diagCode e u))) ∥₁
    diagCompute = do
      (diagCode , dcWorks) ← ccInstance
      ∣ diagCode ,
        (λ e → (fst (dcWorks e (¬¬resize-in tt))) ,
          λ n u → ∂defEqStable separatedℕ _ _
            (¬¬-map (λ f → f n u) (¬¬resize-out (snd (dcWorks e (¬¬resize-in tt)))))) ∣₁
      where
        dom : ℕ → Ω¬¬
        dom _ = ¬¬⊤

        works : (e : ℕ) → ⟨ dom e ⟩ → ℕ → Ω¬¬
        works e u m = ¬¬resize (diag e ≤ φ m)
        
        total : (e : ℕ) → (u : ⟨ dom e ⟩) → ∥ Σ[ m ∈ ℕ ] ⟨ works e u m ⟩ ∥₁
        total e u = do
          (m , v) ← ECT (diag e)
          ∣ m , (¬¬resize-in v) ∣₁

        ccInstance = ComputableChoice dom works total

φoneDefd : (e f n m : ℕ) → (¬ φ e n ≡ φ f m) → (φ e n ↓) ⊎ (φ f m ↓)
φoneDefd e f n m p =
  ⊎map (λ j → ¬¬resize-in ((fst MPinstance) , j))
       (λ j → ¬¬resize-in ((fst MPinstance) , j)) (snd MPinstance)
  where
    P : ℕ → Type
    P k = isJust (φ₀ e n k) ⊎ isJust (φ₀ f m k)

    Pdec : (k : ℕ) → Dec (P k)
    Pdec k = isJustDec _ ⊎? isJustDec _

    MPinstance : Σ[ k ∈ ℕ ] P k
    MPinstance = markovsPrinciple P Pdec
      (λ w → p (∂undefdUnique
        (λ u → ¬¬⊥→⊥ (¬¬-map (λ (k , j) → w (k , (inl j))) (¬¬resize-out u)))
        λ u → ¬¬⊥→⊥ (¬¬-map (λ (k , j) → w (k , (inr j))) (¬¬resize-out u))))

φoneDefd' : (e f n m : ℕ) → ¬ ((¬ (φ e n) ↓) × (¬ (φ f m) ↓)) → (φ e n ↓) ⊎ (φ f m ↓)
φoneDefd' e f n m p =
  ⊎map (λ j → ¬¬resize-in ((fst MPinstance) , j))
       (λ j → ¬¬resize-in ((fst MPinstance) , j)) (snd MPinstance)
  where
    P : ℕ → Type
    P k = isJust (φ₀ e n k) ⊎ isJust (φ₀ f m k)

    Pdec : (k : ℕ) → Dec (P k)
    Pdec k = isJustDec _ ⊎? isJustDec _

    MPinstance : Σ[ k ∈ ℕ ] P k
    MPinstance = markovsPrinciple P Pdec
      λ w → p ((λ u → ¬¬⊥→⊥ (¬¬-map (λ (k , j) → w (k , (inl j))) (¬¬resize-out u))) ,
              λ u → ¬¬⊥→⊥ (¬¬-map (λ (k , j) → w (k , (inr j))) (¬¬resize-out u)))

n≢sucn : (n : ℕ) → ¬ (n ≡ suc n)
n≢sucn n p = ¬m<m (subst (λ m → n < m) (sym p) ≤-refl)

ι-inj : (a b : A) → ι a ≡ ι b → a ≡ b
ι-inj a b p i = ∂.value (p i) (subst-filler (λ w → [ ∂.domain w ]) p (¬¬resize-in tt) i)

Ω¬¬-indiscrete : ((x : Ω¬¬) → Dec [ x ]) → ⊥
Ω¬¬-indiscrete dec = rec isProp⊥ (λ (x , u) → Fnofixed x u) fixed
  where
    F : ∂ ℕ → ∂ ℕ
    F z with (dec (∂.domain z))
    ... | yes p = record { domain = ∂.domain z ; value = suc ∘ ∂.value z }
    ... | no p = record { domain = ¬¬⊤ ; value = λ _ → 0 }

    Fdefd : (z : ∂ ℕ) → F z ↓
    Fdefd z with (dec (∂.domain z))
    ... | yes p = p
    ... | no p = ¬¬resize-in tt

    Fnofixed : (z : ∂ ℕ) → ¬ (F z ≡ z)
    Fnofixed z with (dec (∂.domain z))
    ... | (yes u) =
      λ q → n≢sucn (∂.value z u)
                   λ i → ∂.value (q (~ i))
                     (isProp→PathP (λ i → Ω¬¬-props (∂.domain (q (~ i)))) u u i)
    ... | no p = λ q → p (subst ([_] ∘ ∂.domain) q (¬¬resize-in tt))

    fixed : ∥ Σ[ x ∈ ∂ ℕ ] F x ≡ x ∥₁
    fixed = Fixed.ifMaximal φ ECT F
            (λ x y f → ∂defdUnique (Fdefd x) (fst (f (Fdefd x))) (sym (snd (f (Fdefd x)))))

Ω¬¬→ℕconst : (f : Ω¬¬ → ℕ) → (x y : Ω¬¬) → f x ≡ f y
Ω¬¬→ℕconst f x y = separatedℕ _ _ λ p → xtodec y x (p ∘ sym) (ytrue p)
  where
    xtodec : (x y : Ω¬¬) → ¬ (f x ≡ f y) → [ x ] → ⊥
    xtodec x y p u = Ω¬¬-indiscrete dec
      where
        yfalse : ¬ [ y ]
        yfalse v = p (cong f (Ω¬¬-ext _ _ (λ _ → v) (λ _ → u)))
        
        dec : (a : Ω¬¬) → Dec [ a ]
        dec a with (discreteℕ (f a) (f x))
        ... | yes v = yes (Ω¬¬-stab _
          (λ w → p (sym v ∙ cong f (Ω¬¬-ext _ _ (λ nw → ⊥rec (w nw))
                                                (λ d → ⊥rec (yfalse d))))))
        ... | no q = no (λ z → q (cong f (Ω¬¬-ext _ _ (λ _ → u) (λ _ → z))))

    xfalse : ¬ (f x ≡ f y) → ¬ [ x ]
    xfalse = xtodec x y

    ytrue : ¬ (f x ≡ f y) → [ y ]
    ytrue p = Ω¬¬-stab _ (λ u → p (cong f (Ω¬¬-ext _ _ (λ v → ⊥rec (xfalse p v))
                                                       (λ v → ⊥rec (u v)))))


record StableSubset (X : Type) : Type where
  field
    charFn : X → Ω¬¬
    stableInh : ¬ ¬ (Σ[ x ∈ X ] ⟨ charFn x ⟩) → ∥ Σ[ x ∈ X ] ⟨ charFn x ⟩ ∥₁
    

instance
  stableSubsetReln : {X : Type} → PosetStr (StableSubset X)
  PosetStr._≤_ (stableSubsetReln {X = X}) f g =
    ¬ ¬ (Σ[ x ∈ X ] ⟨ StableSubset.charFn f x ⟩) →
      ((y : X) → ⟨ StableSubset.charFn g y ⟩ → ⟨ StableSubset.charFn f y ⟩) ×
      (¬ ¬ (Σ[ x ∈ X ] ⟨ StableSubset.charFn g x ⟩))

φ' : ℕ → (ℕ → StableSubset ℕ)
StableSubset.charFn (φ' e n) m = ¬¬resize (φ e n ↓= m)
StableSubset.stableInh (φ' e n) u =
  ∣ ∂.value (φ e n) φdefd , (¬¬resize-in (φdefd , refl)) ∣₁
  where
    φdefd : φ e n ↓
    φdefd = Ω¬¬-stab _ do
      (m , z) ← u
      (z , _) ← ¬¬resize-out z
      ¬¬-in z

φ'Dense : (f : ℕ → StableSubset ℕ) → ∥ Σ[ e ∈ ℕ ] f ≤ φ' e ∥₁
φ'Dense f = do
  (e , u) ← ComputableChoice D R stableDom
  ∣ e , (λ n v →
           (λ m' w →
             Ω¬¬-stab _ do
               (d , p) ← ¬¬resize-out w
               v ← v
               let (d' , z) = u n (¬¬resize-in v)
               ¬¬-in (subst (λ m'' → ⟨ R n (¬¬resize-in v) m'' ⟩)
                            (cong (φ-fromDomain e n) (φ-isPropDomain _ _) ∙ p) z) ),
        do
          (m , v) ← v
          let (d , r) = u n (¬¬resize-in (m , v))
          ¬¬-in (∂.value (φ e n) (¬¬resize-in d) , (¬¬resize-in ((¬¬resize-in d) , refl)))) ∣₁
  where
    D : ℕ → Ω¬¬
    D n = ¬¬resize (Σ[ m ∈ ℕ ] ⟨ StableSubset.charFn (f n) m ⟩)

    R : (n : ℕ) → ⟨ D n ⟩ → ℕ → Ω¬¬
    R n u m = StableSubset.charFn (f n) m

    stableDom : (n : ℕ) → (u : ⟨ D n ⟩) → ∥ (Σ[ m ∈ ℕ ] ⟨ R n u m ⟩) ∥₁
    stableDom n u = StableSubset.stableInh (f n) (¬¬resize-out u)

record ℕ∞ : Type where
  field
    f : ℕ → Bool
    unique : (n m : ℕ) → (f n ≡ true) → (f m ≡ true) → n ≡ m

instance
  ℕ∞-prop : HasUnderlyingType ℕ∞
  HasUnderlyingType.get-underlying-type ℕ∞-prop α = Σ[ n ∈ ℕ ] ℕ∞.f α n ≡ true

partialCT : (d : ℕ → ℕ∞) (f : (n : ℕ) → ⟨ d n ⟩ → ℕ) →
  ∥ Σ[ e ∈ ℕ ] ((n : ℕ) → ((u : ⟨ d n ⟩) → φ e n ↓= f n u) × (φ e n ↓ → ⟨ d n ⟩)) ∥₁
partialCT d f = do
  (e , g) ← fixed3 (λ e n → fst (FwithPf e n))
  ∣ e , (λ n →
    (λ u → ⊎rec
      (λ (u' , p) →
        (fst (g n ((¬¬resize-in ((fst u) , (inl (snd u))))))) ,
          (snd (g n (((¬¬resize-in ((fst u) , (inl (snd u))))))) ∙∙
          sym p ∙∙
          cong (f n) (Σ≡Prop (λ _ → isSetBool _ _)
               (ℕ∞.unique (d n) _ _ (snd u') (snd u)))))
        (λ (u' , w) → ⊥rec (w (cong (get (φ e n)) (Ω¬¬-props _ _ _) ∙
                           snd (g n ((¬¬resize-in (fst u , inl (snd u))))))))
        (snd (FwithPf e n) (¬¬resize-in ((fst u) , (inl (snd u)))))) ,
        λ v → ⊎rec fst (λ (u , w) →
          ⊥rec (w (cong (get (φ e n)) (Ω¬¬-props _ _ _) ∙
            snd (g n ((¬¬resize-in-from¬¬ (¬¬-map (λ (k , p) → k , (inr p))
                                       (¬¬resize-out v)))))))) (snd (FwithPf e n)
                   (¬¬resize-in-from¬¬ (¬¬-map (λ (k , p) → k , (inr p))
                                       (¬¬resize-out v))))) ∣₁
  where
    FwithPf : (e : ℕ) → (n : ℕ) →
      Σ[ μ ∈ ∂ ℕ ]
        ((v : μ ↓) →
        (Σ[ u ∈ ⟨ d n ⟩ ] f n u ≡ ∂.value μ v) ⊎
          (Σ[ u ∈ φ e n ↓ ] ¬ get (φ e n) u ≡ ∂.value μ v))
    FwithPf e n =
      μ ,
      λ v → snd (mWithPf v)
      where
        P : ℕ → Type
        P k = (ℕ∞.f (d n) k ≡ true) ⊎ isJust (φ₀ e n k)

        mWithPf : ⟨ ¬¬resize (Σ[ k ∈ ℕ ] P k) ⟩ →
          Σ[ m ∈ ℕ ] (Σ[ u ∈ ⟨ d n ⟩ ] f n u ≡ m) ⊎
                          (Σ[ u ∈ φ e n ↓ ] ¬ get (φ e n) u ≡ m)
        mWithPf z with
          markovsPrinciple P (λ k → discreteBool _ _ ⊎? isJustDec _) (¬¬resize-out z)
        ... | (k , inl p) = (f n (k , p)) , (inl ((k , p) , refl))
        ... | (k , inr z) = (suc (get (φ e n) (¬¬resize-in (k , z)))) ,
                            inr ((¬¬resize-in (k , z)) , n≢sucn _)

        μ : ∂ ℕ
        ∂.domain μ = ¬¬resize (Σ[ k ∈ ℕ ] P k)
        ∂.value μ z = fst (mWithPf z)

