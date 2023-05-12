module DoubleNegationSheaves where

open import Includes

open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Axioms.NegativeResizing

open import Util.HasUnderlyingType
open import Util.ModalOperatorSugar
open import Util.PartialElements

open import Util.DoubleNegation

    
{- Implementation of 0-truncated ¬¬-sheafification using negative resizing. -}
record ∇ (A : Type ℓ) : Type ℓ where
  field
    is-this : A → Ω¬¬
    well-defd : (a a' : A) → ⟨ is-this a ⟩ → ⟨ is-this a' ⟩ → ¬ ¬ a ≡ a'
    almost-inh : ¬ ¬ Σ A (λ a → ⟨ is-this a ⟩)

{- Description of ∇ as a Σ-type -}
∇-as-Σ : (A : Type ℓ) →
  Iso (∇ A) ( Σ[ P ∈ (A → Ω¬¬) ] (((a b : A) → ⟨ P a ⟩ → ⟨ P b ⟩ → ¬ ¬ (a ≡ b)) ×
                            (¬ ¬ (Σ[ a ∈ A ] ⟨ P a ⟩))))
∇-as-Σ A = iso f g f-g g-f
  where
    target = Σ[ P ∈ (A → Ω¬¬) ] (((a b : A) → ⟨ P a ⟩ → ⟨ P b ⟩ → ¬ ¬ (a ≡ b)) ×
                            (¬ ¬ (Σ[ a ∈ A ] ⟨ P a ⟩)))
  
    f : ∇ A → target
    f x = ∇.is-this x , ((∇.well-defd x) , (∇.almost-inh x))

    g : target → ∇ A
    g (it , (p , q)) = record { is-this = it ; well-defd = p ; almost-inh = q }

    f-g : (y : target) → f (g y) ≡ y
    f-g (it , (p , q)) = refl

    g-f : (x : ∇ A) → g (f x) ≡ x
    g-f x = refl

∇=-in' : (x y : ∇ A) → ((a : A) → ∇.is-this x a ≡ ∇.is-this y a) → x ≡ y
∇=-in' {A = A} x y p =
  isoFunInjective (∇-as-Σ A) x y
    (Σ≡Prop (λ a → isProp× (isPropΠ5 (λ _ _ _ _ _ → isProp⊥)) (isProp¬ _)) (funExt p))

{- Lemma for showing two elements of ∇ A are equal -}
∇=-in : (x y : ∇ A) → ((a : A) → (⟨ ∇.is-this x a ⟩ ↔ ⟨ ∇.is-this y a ⟩)) → x ≡ y
∇=-in x y p = ∇=-in' x y (λ a → Ω¬¬-ext _ _ (λ z → fst (p a) z) λ z → snd (p a) z)

{- Unit -}
∇-in : {A : Type ℓ} → A → ∇ A
∇.is-this    (∇-in a) b       = ¬¬resize (b ≡ a)
∇.well-defd  (∇-in a) b c x y = do
             is-b ← ¬¬resize-out x
             is-c ← ¬¬resize-out y
             ¬¬-in (is-b ∙ sym is-c)
∇.almost-inh (∇-in a)         = ¬¬-in (a , (¬¬resize-in refl))

{- We can view elements of ∇ A as partial elements and so use all the notation in PartialElements -}
∇hasUnderlyingPartialVF : HasUnderlyingPartialValueFirst {ℓ = ℓ} ∇
HasUnderlyingPartialValueFirst.is-this ∇hasUnderlyingPartialVF α a = ⟨ ∇.is-this α a ⟩
--  well-defd ∇hasUnderlyingPartialVF = ∇.well-defd
HasUnderlyingPartialValueFirst.includeTotal ∇hasUnderlyingPartialVF = ∇-in
HasUnderlyingPartialValueFirst.totalIs ∇hasUnderlyingPartialVF a = ¬¬resize-in refl

instance
  ∇hasUnderlyingPartial : HasUnderlyingPartial {ℓ = ℓ} ∇
  ∇hasUnderlyingPartial = HasUnderlyingPartialFromValue ∇hasUnderlyingPartialVF

∇defd-prop : {A : Type ℓ} → (Separated A) → (x : ∇ A) → isProp (x ↓)
∇defd-prop Asep x (a , z) (a' , z') = Σ≡Prop (λ b → Ω¬¬-props _) (Asep a a' (∇.well-defd x a a' z z'))


{- Definition of ¬¬-sheaf -}
¬¬Sheaf : (A : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
¬¬Sheaf {ℓ' = ℓ'} = isNull {A = Σ[ P ∈ Type ℓ' ] isProp P × (¬ ¬ P)} typ

StableProp→¬¬Sheaf : {A : Type ℓ} (Aprop : isProp A) → Stable A → ¬¬Sheaf {ℓ' = ℓ'} A
isPathSplitEquiv.sec (StableProp→¬¬Sheaf Aprop Astab (P , (Pprop , Pconn))) =
  (λ f → Astab λ na → Pconn (λ p → na (f p))) , λ f → funExt (λ p → Aprop _ _)
isPathSplitEquiv.secCong (StableProp→¬¬Sheaf Aprop Astab (P , _)) a b =
  (λ _ → Aprop _ _) , (λ p → isSet→ (isProp→isSet Aprop) (λ _ → a) (λ _ → b) _ _)

isProp¬¬Sheaf : {A : Type ℓ} → isProp (¬¬Sheaf {ℓ' = ℓ'} A)
isProp¬¬Sheaf = isPropΠ (λ _ → isPropIsPathSplitEquiv _)

¬¬SheafProp→Stable : (A : Type ℓ) → (isProp A) → (¬¬Sheaf {ℓ' = ℓ} A) → Stable A
¬¬SheafProp→Stable A Aprop Ash nna = fst (isPathSplitEquiv.sec (Ash (A , Aprop , nna))) λ x → x

{- 0-truncated ¬¬sheaves are separated -}
¬¬SheafSet→Separated : isSet A → ¬¬Sheaf A → Separated A
¬¬SheafSet→Separated {A = A} Aset Ash a a' = ¬¬SheafProp→Stable _ (Aset a a') (isNull≡ Ash)

{- ∇ A is always ¬¬-separated, and in particular a set -}
Separated∇ : {A : Type ℓ} → Separated (∇ A)
Separated∇ x y z = ∇=-in' _ _ λ a → SeparatedΩ¬¬ _ _ (¬¬-map (cong _) z)

isSet∇ : {A : Type ℓ} → isSet (∇ A)
isSet∇ {A = A} = Separated→isSet Separated∇

∇-in-inj : {a b : A} → (∇-in a ≡ ∇-in b) → ¬ ¬ (a ≡ b)
∇-in-inj {A = A} {a = a} {b = b} p = ∇.well-defd (∇-in b) a b (lem1 a (lem2 a)) (lem2 b)
  where
    lem1 : (c : A) → ⟨ ¬¬resize (c ≡ a) ⟩ → ⟨ ¬¬resize (c ≡ b) ⟩
    lem1 c z = subst (λ x → ⟨ ∇.is-this x c ⟩) p z

    lem2 : (c : A) → ⟨ ∇.is-this (∇-in c) c ⟩
    lem2 c = ¬¬resize-in refl

∇∩-to-→ : (x y : ∇ A) (a : A) → ⟨ ∇.is-this x a ⟩ → ⟨ ∇.is-this y a ⟩ →
  (b : A) → ⟨ ∇.is-this x b ⟩ → ⟨ ∇.is-this y b ⟩
∇∩-to-→ x y a u v b z = Ω¬¬-stab _ (¬¬-map (λ p → subst _ p v) (∇.well-defd x a b u z))

∇∩→≡ : (x y : ∇ A) (a : A) → ⟨ ∇.is-this x a ⟩ → ⟨ ∇.is-this y a ⟩ → x ≡ y
∇∩→≡ x y a u v = ∇=-in x y (λ b → (∇∩-to-→ x y a u v b) , ∇∩-to-→ y x a v u b)

∇-defd→path : {A : Type ℓ} (α : ∇ A) (a : A) → ⟨ ∇.is-this α a ⟩ → α ≡ ∇-in a
∇-defd→path α a z = ∇∩→≡ _ _ a z (¬¬resize-in refl)

∇-path→defd : {A : Type ℓ} (α : ∇ A) (a : A) → α ≡ ∇-in a → ⟨ ∇.is-this α a ⟩
∇-path→defd α a p = subst (λ α' → ⟨ ∇.is-this α' a ⟩) (sym p) (¬¬resize-in refl)

{- ∇ A is always a ¬¬-sheaf -}
∇isSheaf : {A : Type ℓ} → ¬¬Sheaf {ℓ' = ℓ'} (∇ A)
isPathSplitEquiv.sec (∇isSheaf {A = A} (P , (Pprop , Pconn))) = sec , secpath
  where
    sec : (P → ∇ A) → ∇ A
    ∇.is-this (sec f) a = ¬¬resize ((p : P) → f p ↓= a)
    ∇.almost-inh (sec f ) = do
      p ← Pconn
      (a , u) ← ∇.almost-inh (f p)
      ¬¬-in (a , (¬¬resize-in (λ p' → subst (λ p → f p ↓= a) (Pprop _ _) u)))
    ∇.well-defd (sec f) a b u v = do
      u ← ¬¬resize-out u
      v ← ¬¬resize-out v
      p ← Pconn
      ∇.well-defd (f p) a b (u p) (v p)

    secpath : (f : P → ∇ A) → (λ _ → sec f) ≡ f
    secpath f = funExt λ p → Separated∇ _ _ do
      (a , u) ← ∇.almost-inh (f p)
      ¬¬-in (∇∩→≡ _ _ a (¬¬resize-in (λ _ → subst (λ p → f p ↓= a) (Pprop _ _) u)) u)

isPathSplitEquiv.secCong (∇isSheaf {A = A} (P , (Pprop , Pconn))) α β =
  sec , λ p → isSetΠ (λ _ → isSet∇) _ _ _ _
  where
    sec : (λ _ → α) ≡ (λ _ → β) → α ≡ β
    sec p = Separated∇ _ _ (¬¬-map (funExt⁻ p) Pconn)

∇injective : {A : Type ℓ} (P : hProp ℓ') → (¬ ¬ ⟨ P ⟩) → (f : ⟨ P ⟩ → ∇ A) → Σ[ α ∈ ∇ A ] ((p : ⟨ P ⟩) → f p ≡ α)
∇injective P p₀ f = (fst s f) , funExt⁻ (sym (snd s f))
  where
    s = isPathSplitEquiv.sec (∇isSheaf ((fst P) , ((snd P) , p₀)))

{- ∇ reflects onto ¬¬-separated ¬¬-sheaves. Note that this satisfies Definition 1.3 in [RSS]. -}
∇reflSubuniverse : {A : Type ℓ} (B : Type ℓ') (Bsh : ¬¬Sheaf B) (Bsep : Separated B) →
  (isPathSplitEquiv λ f → f ∘ ∇-in)
isPathSplitEquiv.sec (∇reflSubuniverse {A = A} B Bsh Bsep) = sec , secPath
  where
    Bset : isSet B
    Bset = Separated→isSet Bsep

    secParts : (f : A → B) → (α : ∇ A) → _
    secParts f α = isPathSplitEquiv.sec (Bsh ((Σ[ b ∈ B ] ((z : α ↓) → (f (fst z) ≡ b))) ,
             (λ {(b , u) (c , v) →
               Σ≡Prop (λ _ → isPropΠ (λ _ → Bset _ _))
                             (Bsep _ _ (¬¬-map (λ z → sym (u z) ∙ v z) (∇.almost-inh α)))}) ,
             ¬¬-map (λ {(a , u) → (f a) , (λ {(b , v) → Bsep _ _ (¬¬-map (cong f) (∇.well-defd α _ _ v u))})}) (∇.almost-inh α)))

    sec : (A → B) → (∇ A → B)
    sec f α = fst (secParts f α) fst

    secPath : (f : A → B) → (sec f ∘ ∇-in ≡ f)
    secPath f = funExt (λ a → funExt⁻ (snd (secParts f (∇-in a)) fst) ((f a) , λ {(b , u) → Bsep _ _ (¬¬-map (cong f) (¬¬resize-out u))}))

isPathSplitEquiv.secCong (∇reflSubuniverse {A = A} B Bsh Bsep) g h = (λ p → funExt (λ α → Bsep _ _ (lemma α p))) , λ q → isSetΠ (λ _ → Bset) _ _ _ _
  where
    Bset : isSet B
    Bset = Separated→isSet Bsep

    lemma : (α : ∇ A) → (g ∘ ∇-in ≡ h ∘ ∇-in) → ¬ ¬ (g α ≡ h α)
    lemma α p = do
      (a , u) ← ∇.almost-inh α
      ¬¬-in (cong g (∇∩→≡ _ _ _ u (¬¬resize-in refl)) ∙∙ funExt⁻ p a ∙∙ cong h (∇∩→≡ _ _ _ (¬¬resize-in refl) u))

{- ∇ restricts to double negation on propositions. -}
∇-prop : {A : Type ℓ} (Aprop : isProp A) → ∇ A ≃ (¬ ¬ A)
∇-prop {A = A} Aprop = propBiimpl→Equiv ∇A-isprop (isProp¬ _) f g
  where
    f : ∇ A → ¬ ¬ A
    f x = ¬¬-map fst (∇.almost-inh x)

    g : ¬ ¬ A → ∇ A
    g nna = record { is-this = λ _ → ¬¬⊤
                   ; well-defd = λ a b _ _ → ¬¬-in (Aprop a b)
                   ; almost-inh = ¬¬-map (λ a → a , (¬¬resize-in tt)) nna }

    lem : (a : A) → (x : ∇ A) → ⟨ ∇.is-this x a ⟩
    lem a x = Ω¬¬-stab _ (¬¬-map (λ {(a' , z) → subst _ (Aprop a' a) z}) (∇.almost-inh x))

    ∇A-isprop : isProp (∇ A)
    ∇A-isprop x x' = ∇=-in x x' λ a → (λ _ → lem a x') , λ _ → lem a x

instance
  {- Since ∇ is a modal operator we can use do notation for it -}
  open ModalOperator
  ∇-bind : ∀ {ℓa ℓb} → ModalOperator ℓ-zero ℓa ℓb ∇
  bind (∇-bind) x f = fst (isPathSplitEquiv.sec (∇reflSubuniverse _ ∇isSheaf Separated∇)) f x

∇defd : {A : Type ℓ} → (α : ∇ A) → (∇ (α ↓))
∇.is-this (∇defd α) (a , z) = ¬¬⊤
∇.well-defd (∇defd α) (a , u) (b , v) _ _ = ¬¬-map (Σ≡Prop (λ _ → Ω¬¬-props _)) (∇.well-defd α _ _ u v)
∇.almost-inh (∇defd α) = ¬¬-map (λ {(a , u) → (a , u) , (¬¬resize-in tt)}) (∇.almost-inh α)

byCases : {A : Type ℓ} (P : Type ℓ') → A → A → ∇ A
∇.is-this (byCases P a b) c = ¬¬resize ((P → c ≡ a) × (¬ P → c ≡ b))
∇.well-defd (byCases P a b) c d u v = do
  u' ← ¬¬resize-out u
  v' ← ¬¬resize-out v
  l ← ¬¬LEM P
  ¬¬-in (⊎rec (λ p → fst u' p ∙ sym (fst v' p)) (λ ¬p → snd u' ¬p ∙ sym (snd v' ¬p)) l)
∇.almost-inh (byCases P a b) = do
  l ← ¬¬LEM P
  ¬¬-in (⊎rec (λ p → a , (¬¬resize-in ((λ _ → refl) , (λ ¬p → ⊥rec (¬p p)))))
              (λ ¬p → b , ¬¬resize-in ((λ p → ⊥rec (¬p p)) , (λ _ → refl))) l)

byCasesβ⊤ : {A : Type ℓ} (P : Type ℓ') (a b : A) → P → (byCases P a b ↓= a)
byCasesβ⊤ P a b p = ¬¬resize-in ((λ _ → refl) , (λ ¬p → ⊥rec (¬p p)))

byCasesβ⊥ : {A : Type ℓ} (P : Type ℓ') (a b : A) → ¬ P → (byCases P a b ↓= b)
byCasesβ⊥ P a b ¬p = ¬¬resize-in ((λ p → ⊥rec (¬p p)) , (λ _ → refl))

∇2 : ∇ Bool ≃ Ω¬¬
∇2 = isoToEquiv (iso f g f-g g-f)
  where
    f : ∇ Bool → Ω¬¬
    f x = ∇.is-this x true

    g' : Ω¬¬ → ∇ Bool
    g' y = byCases ⟨ y ⟩ true false

    g : Ω¬¬ → ∇ Bool
    g y = record { is-this = it
                 ; well-defd = wd
                 ; almost-inh = a-i }
        where
          it : Bool → Ω¬¬
          it false = Ω¬¬-invert y
          it true = y

          wd : (a b : Bool) → ⟨ it a ⟩ → ⟨ it b ⟩ → ¬ ¬ (a ≡ b)
          wd false false u v = ¬¬-in refl
          wd false true u v = λ _ → ¬¬resize-out u (¬¬-in v)
          wd true false u v = λ _ → ¬¬resize-out v (¬¬-in u)
          wd true true u v = ¬¬-in refl

          a-i : ¬ ¬ (Σ Bool (λ a → ⟨ it a ⟩))
          a-i x = x (false , (¬resize-in _ (¬¬-in ny)))
            where
              ny : ¬ ⟨ y ⟩
              ny z = x (true , z)

    f-g : (z : Ω¬¬) → f (g z) ≡ z
    f-g z = refl

    g-f : (x : ∇ Bool) → g (f x) ≡ x
    g-f x = ∇=-in (g (f x)) x (λ {true → (λ x → x) , (λ x → x) ; false → lem2 , lem1})
      where
        lem1 : ⟨ ∇.is-this x false ⟩ → ⟨ ¬¬resize (¬ ⟨ ∇.is-this x true ⟩) ⟩
        lem1 z = ¬¬resize-in λ w → ∇.well-defd x _ _ w z true≢false

        lem2 : ⟨ ¬¬resize (¬ ⟨ ∇.is-this x true ⟩) ⟩ → ⟨ ∇.is-this x false ⟩
        lem2 z = Ω¬¬-stab _ do
          w ← ¬¬resize-out z
          (true , v) ← ∇.almost-inh x
            where (false , v) → ¬¬-in v
          λ _ → w v

instance
  ∇2UnderlyingType : HasUnderlyingType (∇ Bool)
  HasUnderlyingType.get-underlying-type ∇2UnderlyingType b = ⟨ ∇.is-this b true ⟩

∇→¬¬ :  {A : Type ℓ} → ∇ A → ¬ ¬ A
∇→¬¬ α = ¬¬-map fst (∇.almost-inh α)
