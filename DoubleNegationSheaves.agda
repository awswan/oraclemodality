module DoubleNegationSheaves where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure hiding (⟨_⟩)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.HITs.PropositionalTruncation

open import Util.HasUnderlyingType
open import Util.ModalOperatorSugar
open import NegativeResizing
open import PartialElements

open import Util.DoubleNegation

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

{- ∇ is the plus construction for double negation. It follows that it restricts to
   double negation on propositions, and that we can think of it as
   sheafication for the double negation topology on ¬¬-separated types. -}

record ∇ (A : Type ℓ) : Type ℓ where
  field
    is-this : A → Ω¬¬
    well-defd : (a a' : A) → ⟨ is-this a ⟩ → ⟨ is-this a' ⟩ → ¬ ¬ a ≡ a'
    almost-inh : ¬ ¬ Σ A (λ a → ⟨ is-this a ⟩)

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

∇=-in : (x y : ∇ A) → ((a : A) → (⟨ ∇.is-this x a ⟩ ↔ ⟨ ∇.is-this y a ⟩)) → x ≡ y
∇=-in x y p = ∇=-in' x y (λ a → Ω¬¬-ext _ _ (λ z → fst (p a) z) λ z → snd (p a) z)

∇-in : {A : Type ℓ} → A → ∇ A
∇.is-this    (∇-in a) b       = ¬¬resize (b ≡ a)
∇.well-defd  (∇-in a) b c x y = do
             is-b ← ¬¬resize-out x
             is-c ← ¬¬resize-out y
             ¬¬-in (is-b ∙ sym is-c)
∇.almost-inh (∇-in a)         = ¬¬-in (a , (¬¬resize-in refl))

instance
  open HasUnderlyingPartial
  ∇hasUnderlyingPartial : HasUnderlyingPartial {ℓ = ℓ} ∇
  ∂.is-this (getUnderlyingPartial ∇hasUnderlyingPartial α) = ∇.is-this α
  ∂.well-defd (getUnderlyingPartial ∇hasUnderlyingPartial α) = ∇.well-defd α
  includeTotal ∇hasUnderlyingPartial = ∇-in
  totalIs ∇hasUnderlyingPartial a = ¬¬resize-in refl

∇defd-prop : {A : Type ℓ} → (Separated A) → (x : ∇ A) → isProp (x ↓)
∇defd-prop Asep x (a , z) (a' , z') = Σ≡Prop (λ b → Ω¬¬-props _) (Asep a a' (∇.well-defd x a a' z z'))



¬¬Sheaf : (A : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
¬¬Sheaf {ℓ' = ℓ'} A = (P : hProp ℓ') → (¬ ¬ ⟨ P ⟩) → (f : ⟨ P ⟩ → A) →
                       isContr (Σ A (λ a → (p : ⟨ P ⟩) → f p ≡ a))

StableProp→¬¬Sheaf : {A : Type ℓ} (Aprop : isProp A) → Stable A → ¬¬Sheaf {ℓ' = ℓ'} A
StableProp→¬¬Sheaf Aprop Astab P Pconn f =
  ((Astab (¬¬-map f Pconn)) , (λ _ → Aprop _ _)) ,
  λ {(a , w) → Σ≡Prop (λ _ → isPropΠ (λ _ → isProp→isSet Aprop _ _)) (Aprop _ _)}

isProp¬¬Sheaf : {A : Type ℓ} → isProp (¬¬Sheaf {ℓ' = ℓ'} A)
isProp¬¬Sheaf = isPropΠ3 (λ _ _ _ → isPropIsContr)

¬¬SheafSet→Separated : isSet A → ¬¬Sheaf A → Separated A
¬¬SheafSet→Separated {A = A} Aset Ash a a' p = sym q ∙ r
  where
    af : (a ≡ a') → A
    af _ = a

    c : isContr (Σ A (λ b → (z : a ≡ a') → a ≡ b))
    c = Ash ((a ≡ a') , (Aset _ _)) p af

    q = cong fst (snd c (a , (λ _ → refl)))
    r = cong fst (snd c (a' , (λ z → z)))

¬¬SheafΣ : {A : Type ℓ} {B : A → Type ℓ'} → ¬¬Sheaf A → ((a : A) → ¬¬Sheaf {ℓ' = ℓ''} (B a)) →
           ¬¬Sheaf (Σ A B)
¬¬SheafΣ {A = A} {B = B} Ash Bsh P Pconn f =
  isOfHLevelRetractFromIso 0 (compIso eq eq2) (Bsh _ P Pconn _)
    
  where
    eq : Iso (Σ[ ab ∈ Σ A B ] ((z : ⟨ P ⟩) → f z ≡ ab))
         (Σ (Σ[ a ∈ A ] ((z : ⟨ P ⟩) → fst (f z) ≡ a))
           (λ {(a , p) → Σ[ b ∈ B a ]
                         ((z : ⟨ P ⟩) → PathP (λ i → B (p z i)) (snd (f z)) b)}))

    Iso.fun eq ((a , b) , p) = (a , (λ z i → fst (p z i))) , (b , (λ z i → snd (p z i)))
    Iso.inv eq ((a , p) , (b , q)) = (a , b) , (λ z i → (p z i) , (q z i))
    Iso.rightInv eq ((a , p) , (b , q)) = refl
    Iso.leftInv eq ((a , b) , p) = refl

    ap = Ash P Pconn (fst ∘ f)

    eq2 : Iso (Σ (Σ[ a ∈ A ] ((z : ⟨ P ⟩) → fst (f z) ≡ a))
                  (λ {(a , p) → Σ[ b ∈ B a ]
                            ((z : ⟨ P ⟩) → PathP (λ i → B (p z i)) (snd (f z)) b)}))
               (Σ[ b ∈ B (fst (fst ap)) ] ((z : ⟨ P ⟩) → subst B (snd (fst ap) z) (snd (f z)) ≡ b))
    eq2 =
      Σ (Σ[ a ∈ A ] ((z : ⟨ P ⟩) → fst (f z) ≡ a))
                  (λ {(a , p) → Σ[ b ∈ B a ]
                           ((z : ⟨ P ⟩) → PathP (λ i → B (p z i)) (snd (f z)) b)})
            Iso⟨ Σ-contractFstIso ap ⟩
      Σ[ b ∈ B (fst (fst ap)) ] ((z : ⟨ P ⟩) → PathP (λ i → B (snd (fst ap) z i))
                         (snd (f z)) b)
           Iso⟨ Σ-cong-iso-snd (λ b → codomainIsoDep (λ z → PathPIsoPath _ _ _)) ⟩
      (Σ[ b ∈ B (fst (fst ap)) ] ((z : ⟨ P ⟩) → subst B (snd (fst ap) z) (snd (f z)) ≡ b))
          ∎Iso

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

∇-isSheaf : {A : Type ℓ} → ¬¬Sheaf {ℓ' = ℓ'} (∇ A)
∇-isSheaf {A = A} P Pconn f = (α , path) , to
  where
    α : ∇ A
    ∇.is-this α a = ¬¬resize (Σ ⟨ P ⟩ (λ z → ⟨ ∇.is-this (f z) a ⟩))
    ∇.well-defd α a b u v = do
      ( p , u' ) ← ¬¬resize-out u
      ( q , v' ) ← ¬¬resize-out v
      let u'' = subst _ (str P p q) u'
      ∇.well-defd (f q) a b u'' v'
    ∇.almost-inh α = do
      p ← Pconn
      (a , u) ← ∇.almost-inh (f p)
      ¬¬-in (a , ¬¬resize-in (p , u))

    path : (p : ⟨ P ⟩) → f p ≡ α
    path p = ∇=-in (f p) α (λ a → ltr a , rtl a)
      where
        ltr : (a : A) → ⟨ ∇.is-this (f p) a ⟩ → ⟨ ∇.is-this α a ⟩
        ltr a z = ¬¬resize-in (p , z)

        rtl : (a : A) → ⟨ ∇.is-this α a ⟩ → ⟨ ∇.is-this (f p) a ⟩
        rtl a w = Ω¬¬-stab _ (¬¬-map (λ {(q , w') → subst _ (str P q p) w'}) (¬¬resize-out w))

    to : (y : Σ (∇ A) (λ a → (p : ⟨ P ⟩) → f p ≡ a)) → (α , path) ≡ y
    to (β , u) = Σ≡Prop (λ _ → isPropΠ (λ _ → isSet∇ _ _)) h
      where
        h : α ≡ β
        h = Separated∇ _ _ (¬¬-map (λ p → sym (path p) ∙ u p) Pconn)

module _ (A : Type ℓ) (B : ∇ A → Type ℓ') (Bsep : (α : ∇ A) → Separated (B α))
  (Bsh : (α : ∇ A) → ¬¬Sheaf (B α)) (b₀ : (a : A) → B (∇-in a)) where

  private
    variable
      α : ∇ A

    Bset : isSet (B α)
    Bset {α = α} = Separated→isSet (Bsep α)

    targets : (α : ∇ A) → Type _
    targets α = Σ[ b ∈ B α ] ((a : A) → (p : ∇-in a ≡ α) → subst B p (b₀ a) ≡ b)

    target-unique : isProp (targets α)
    target-unique {α = α} (b , u) (c , v) = Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → Bset _ _)) (Bsep _ _ _ p)
      where
        p : ¬ ¬ (b ≡ c)
        p = do
          (a , w) ← ∇.almost-inh α
          let q = sym (∇-defd→path _ _ w)
          ¬¬-in (sym (u a q) ∙ v a q)

    target-almost-inh : ¬ ¬ (targets α)
    target-almost-inh {α = α} =
      ¬¬-map (λ {(a , z) → subst B (sym (∇-defd→path _ a z))
                                   (b₀ a) , λ a' p → Bsep _ _ _
                                   (¬¬-map (λ r → lem a' a p _ r) (∇-in-inj (sym (∇-defd→path _ _ z) ∙ sym p)))})
                      (∇.almost-inh α)
      where
        lem : (a a' : A) (p : ∇-in a ≡ α) (p' : ∇-in a' ≡ α) (r : a' ≡ a) →
              (subst B p (b₀ a) ≡ subst B p' (b₀ a'))
        lem a a' p p' r =
          subst B p (b₀ a)
            ≡⟨ cong (subst B p) (sym (substCommSlice (λ _ → A) (B ∘ ∇-in) (λ a'' _ → b₀ a'') r a)) ⟩
          subst B p (subst B (cong ∇-in r) (b₀ a'))
            ≡⟨ sym (substComposite B (cong ∇-in r) p (b₀ a')) ⟩
          subst B (cong ∇-in r ∙ p) (b₀ a')
            ≡⟨ cong (λ q → subst B q (b₀ a')) (isSet∇ _ _ _ _) ⟩
          subst B p' (b₀ a')
            ∎

  ∇-elim : (α : ∇ A) → (B α)
  ∇-elim α = fst (fst (Bsh α ((targets α) , target-unique) target-almost-inh fst))

  ∇-elim-β : (a : A) → (∇-elim (∇-in a) ≡ (b₀ a))
  ∇-elim-β a = sym (snd (fst (Bsh (∇-in a) _ target-almost-inh fst)) ((b₀ a) , λ a' p → Bsep _ _ _ (¬¬-map (λ q → cong (λ r → subst B r (b₀ a')) (isSet∇ _ _ p (cong ∇-in q)) ∙ fromPathP (cong b₀ q)) (∇-in-inj p))))


module ∇-rec (A : Type ℓ) (B : Type ℓ') (Bsep : Separated B) (Bsh : ¬¬Sheaf {ℓ' = ℓ-max ℓ ℓ'} B) where
  private
    Bset = Separated→isSet Bsep
  
    f-with-comm : (g : A → B) → (α : ∇ A) → Σ[ b ∈ B ] ((a : A) → α ≡ ∇-in a → b ≡ g a)
    f-with-comm g = ∇-elim A _ (λ α → λ x y z → Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → Bset _ _))
                           (Bsep _ _ (¬¬-map (cong fst) z)))
                           shf (λ a → (g a) , (λ a' p → Bsep _ _ (¬¬-map (cong g) (∇-in-inj p))))
      where
        shf : (α : ∇ A) → ¬¬Sheaf (Σ[ b ∈ B ] ((a : A) → α ≡ ∇-in a → b ≡ g a))
        shf α =
          ¬¬SheafΣ Bsh
                   (λ b → StableProp→¬¬Sheaf (isPropΠ2 (λ _ _ → Bset _ _))
                          (λ z a p → Bsep _ _ (λ w → z (λ u → w (u a p)))))

  f : (A → B) → (∇ A → B)
  f g = fst ∘ (f-with-comm g)

  comm : (g : A → B) → (a : A) → (f g (∇-in a) ≡ g a)
  comm g a = snd (f-with-comm g (∇-in a)) a refl

  unique : (g : A → B) → (f' : ∇ A → B) → (comm' : (a : A) → (f' (∇-in a)) ≡ g a) →
           (α : ∇ A) → (f' α ≡ f g α)
  unique g f' comm' = ∇-elim A (λ α → f' α ≡ f g α) (λ _ _ _ _ → Bset _ _ _ _)
                             (λ α → StableProp→¬¬Sheaf (Bset _ _) (Bsep _ _))
                             λ a → comm' a ∙ sym (comm g a)

  equiv : (∇ A → B) ≃ (A → B)
  fst equiv h = h ∘ ∇-in
  equiv-proof (snd equiv) g = ((f g) , funExt (comm g)) ,
    λ {(f' , comm') → Σ≡Prop (λ _ → isSetΠ (λ _ → Bset) _ _)
      (sym (funExt (λ α → unique g f' (λ a i → comm' i a) α)))}

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


∇-map : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → ∇ A → ∇ B 
∇-map {A = A} {B = B} f = ∇-rec.f _ _ Separated∇ ∇-isSheaf (∇-in ∘ f)


instance
  open ModalOperator
  ∇-bind : ∀ {ℓa ℓb} → ModalOperator ℓ-zero ℓa ℓb ∇
  bind (∇-bind) x f = ∇-rec.f _ _ Separated∇ ∇-isSheaf f x

∇2 : ∇ Bool ≃ Ω¬¬
∇2 = isoToEquiv (iso f g f-g g-f)
  where
    f : ∇ Bool → Ω¬¬
    f x = ∇.is-this x true

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

