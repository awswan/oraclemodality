module DoubleNegationPlus where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Bool

open import Cubical.HITs.PropositionalTruncation

open import Util.ModalOperatorSugar
open import NegativeResizing
open import Util.DoubleNegation

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ

{- ∇ is the plus construction for double negation. It follows that it restricts to
   double negation on propositions, and that we can think of it as
   sheafication for the double negation topology on ¬¬-separated types. -}

record ∇ (A : Type ℓ) : Type ℓ where
  field
    is-this : A → Ω¬¬
    well-defd : (a b : A) → [ is-this a ] → [ is-this b ] → ¬ ¬ (a ≡ b)
    almost-inh : ¬ ¬ Σ A (λ a → [ is-this a ])

{- We say x is defined, or that it denotes an element of A. -}

_↓ : {A : Type ℓ} → ∇ A → Type ℓ
_↓ {A = A} x = Σ A λ a → [ ∇.is-this x a ]

∇defd-prop : {A : Type ℓ} → (Separated A) → (x : ∇ A) → isProp (x ↓)
∇defd-prop Asep x (a , z) (a' , z') = Σ≡Prop (λ b → Ω¬¬-props _) (Asep a a' (∇.well-defd x a a' z z'))

∇-as-Σ : (A : Type ℓ) →
  Iso (∇ A) (Σ (A → Ω¬¬) (λ it → ((a b : A) → [ it a ] → [ it b ] → ¬ ¬ (a ≡ b)) ×
                            (¬ ¬ Σ A (λ a → [ it a ]))))
∇-as-Σ A = iso f g f-g g-f
  where
    target = Σ (A → Ω¬¬) (λ it → ((a b : A) → [ it a ] → [ it b ] → ¬ ¬ (a ≡ b)) ×
                            (¬ ¬ Σ A (λ a → [ it a ])))
  
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

∇=-in : (x y : ∇ A) → ((a : A) → ([ ∇.is-this x a ] ↔ [ ∇.is-this y a ])) → x ≡ y
∇=-in x y p = ∇=-in' x y (λ a → Ω¬¬-ext _ _ (λ z → fst (p a) z) λ z → snd (p a) z)

¬¬Sheaf : (A : Type ℓ) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
¬¬Sheaf {ℓ' = ℓ'} A = (P : hProp ℓ') → (¬ ¬ ⟨ P ⟩) → (f : ⟨ P ⟩ → A) →
                       isContr (Σ A (λ a → (p : ⟨ P ⟩) → f p ≡ a))


∇-in : {A : Type ℓ} → A → ∇ A
∇.is-this (∇-in a) b = ¬¬resize (b ≡ a)
∇.well-defd (∇-in a) b c x y = do
  is-b ← ¬¬resize-out x
  is-c ← ¬¬resize-out y
  ¬¬-in (is-b ∙ sym is-c)
∇.almost-inh (∇-in a) = ¬¬-in (a , (¬¬resize-in refl))

Separated∇ : {A : Type ℓ} → Separated (∇ A)
Separated∇ x y z = ∇=-in' _ _ λ a → SeparatedΩ¬¬ _ _ (¬¬-map (cong _) z)

∇-in-inj : {a b : A} → (∇-in a ≡ ∇-in b) → ¬ ¬ (a ≡ b)
∇-in-inj {A = A} {a = a} {b = b} p = ∇.well-defd (∇-in b) a b (lem1 a (lem2 a)) (lem2 b)
  where
    lem1 : (c : A) → [ ¬¬resize (c ≡ a) ] → [ ¬¬resize (c ≡ b) ]
    lem1 c z = subst (λ x → [ ∇.is-this x c ]) p z

    lem2 : (c : A) → [ ∇.is-this (∇-in c) c ]
    lem2 c = ¬¬resize-in refl

∇∩-to-→ : (x y : ∇ A) (a : A) → [ ∇.is-this x a ] → [ ∇.is-this y a ] →
  (b : A) → [ ∇.is-this x b ] → [ ∇.is-this y b ]
∇∩-to-→ x y a u v b z = Ω¬¬-stab _ (¬¬-map (λ p → subst _ p v) (∇.well-defd x a b u z))

∇∩→≡ : (x y : ∇ A) (a : A) → [ ∇.is-this x a ] → [ ∇.is-this y a ] → x ≡ y
∇∩→≡ x y a u v = ∇=-in x y (λ b → (∇∩-to-→ x y a u v b) , ∇∩-to-→ y x a v u b)

isSet∇ : {A : Type ℓ} → isSet (∇ A)
isSet∇ {A = A} = isOfHLevelRetractFromIso 2 (∇-as-Σ A) (isSetΣSndProp (isSet→ Ω¬¬Set)
  (λ _ → isProp× (isPropΠ5 (λ _ _ _ _ _ → isProp⊥)) (isProp→ isProp⊥)))

-- ∇-in-fibre : {A : Type ℓ} (α : ∇ A) → Iso (α ↓) (fiber ∇-in α)
-- Iso.fun (∇-in-fibre α) (a , z) = a , ∇∩→≡ _ _ a (¬¬resize-in refl) z
-- Iso.inv (∇-in-fibre α) (a , p) = a , subst (λ α' → [ ∇.is-this α' a ]) p (¬¬resize-in refl)
-- Iso.rightInv (∇-in-fibre α) (a , p) = Σ≡Prop (λ _ → isSet∇ _ _) refl
-- Iso.leftInv (∇-in-fibre α) (a , z) = Σ≡Prop (λ _ → Ω¬¬-props _) refl

∇-defd→path : {A : Type ℓ} (α : ∇ A) (a : A) → [ ∇.is-this α a ] → α ≡ ∇-in a
∇-defd→path α a z = ∇∩→≡ _ _ a z (¬¬resize-in refl)

∇-path→defd : {A : Type ℓ} (α : ∇ A) (a : A) → α ≡ ∇-in a → [ ∇.is-this α a ]
∇-path→defd α a p = subst (λ α' → [ ∇.is-this α' a ]) (sym p) (¬¬resize-in refl)

∇-isSheaf : {A : Type ℓ} → ¬¬Sheaf {ℓ' = ℓ'} (∇ A)
∇-isSheaf {A = A} P Pconn f = (α , path) , to
  where
    α : ∇ A
    ∇.is-this α a = ¬¬resize (Σ ⟨ P ⟩ (λ z → [ ∇.is-this (f z) a ]))
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
        ltr : (a : A) → [ ∇.is-this (f p) a ] → [ ∇.is-this α a ]
        ltr a z = ¬¬resize-in (p , z)

        rtl : (a : A) → [ ∇.is-this α a ] → [ ∇.is-this (f p) a ]
        rtl a w = Ω¬¬-stab _ (¬¬-map (λ {(q , w') → subst _ (str P q p) w'}) (¬¬resize-out w))

    to : (y : Σ (∇ A) (λ a → (p : ⟨ P ⟩) → f p ≡ a)) → (α , path) ≡ y
    to (β , u) = Σ≡Prop (λ _ → isPropΠ (λ _ → isSet∇ _ _)) h
      where
        h : α ≡ β
        h = Separated∇ _ _ (¬¬-map (λ p → sym (path p) ∙ u p) Pconn)

∇-elim : (A : Type ℓ) (B : ∇ A → Type ℓ') → ((α : ∇ A) → Separated (B α)) →
  ((α : ∇ A) → ¬¬Sheaf (B α)) → ((a : A) → B (∇-in a)) → (α : ∇ A) → (B α)

∇-elim A B Bsep Bsh b₀ α = fst (fst (Bsh α (targets , target-unique) target-almost-inh fst))
  where
    Bset : isSet (B α)
    Bset = Separated→isSet (Bsep α)
  
    targets : Type _
    targets = Σ[ b ∈ B α ] ((a : A) → (p : ∇-in a ≡ α) → subst B p (b₀ a) ≡ b)

    targets' : Type _
    targets' = Σ[ b ∈ B α ] ((a : A) → (p : ∇-in a ≡ α) → PathP (λ i → B (p i)) (b₀ a) b)

    target-unique : isProp targets
    target-unique (b , u) (c , v) = Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → Bset _ _)) (Bsep _ _ _ p)
      where
        p : ¬ ¬ (b ≡ c)
        p = do
          (a , w) ← ∇.almost-inh α
          let q = sym (∇-defd→path _ _ w)
          ¬¬-in (sym (u a q) ∙ v a q)

    target-almost-inh : ¬ ¬ targets
    target-almost-inh = 
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

module ∇-rec (A : Type ℓ) (B : Type ℓ') (Bsep : Separated B) (Bsh : ¬¬Sheaf {ℓ' = ℓ-max ℓ ℓ'} B) where
  private
    Bset = Separated→isSet Bsep
  
    f-with-comm : (g : A → B) → (α : ∇ A) → Σ[ b ∈ B ] ((a : A) → α ≡ ∇-in a → b ≡ g a)
    f-with-comm g = ∇-elim A _ (λ α → λ x y z → Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → Bset _ _)) (Bsep _ _ (¬¬-map (cong fst) z))) shf (λ a → (g a) , (λ a' p → Bsep _ _ (¬¬-map (cong g) (∇-in-inj p))))
      where
        -- TODO: instance of more general result
        shf : (α : ∇ A) → ¬¬Sheaf (Σ[ b ∈ B ] ((a : A) → α ≡ ∇-in a → b ≡ g a))
        shf α P x f = (((fst (fst bc)) , λ a p → Bsep _ _ (¬¬-map (λ z → sym (snd (fst bc) z) ∙ snd (f z) a p) x)) , λ z → Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → Bset _ _)) (snd (fst bc) z)) , λ y → Σ≡Prop (λ _ → isPropΠ (λ _ → isSetΣSndProp Bset (λ _ → isPropΠ2 (λ _ _ → Bset _ _)) _ _)) (Σ≡Prop (λ _ → isPropΠ2 (λ _ _ → Bset _ _)) (cong fst (snd bc ((fst (fst y)) , (λ p → cong fst (snd y p))))))
          where
            bc = Bsh P x (fst ∘ f)

  f : (A → B) → (∇ A → B)
  f g = fst ∘ (f-with-comm g)

  comm : (g : A → B) → (a : A) → (f g (∇-in a) ≡ g a)
  comm g a = snd (f-with-comm g (∇-in a)) a refl


∇-prop : {A : Type ℓ} (Aprop : isProp A) → ∇ A ≃ (¬ ¬ A)
∇-prop {A = A} Aprop = propBiimpl→Equiv ∇A-isprop (isProp¬ _) f g
  where
    f : ∇ A → ¬ ¬ A
    f x = ¬¬-map fst (∇.almost-inh x)

    g : ¬ ¬ A → ∇ A
    g nna = record { is-this = λ _ → ¬¬⊤
                   ; well-defd = λ a b _ _ → ¬¬-in (Aprop a b)
                   ; almost-inh = ¬¬-map (λ a → a , (¬¬resize-in tt)) nna }

    lem : (a : A) → (x : ∇ A) → [ ∇.is-this x a ]
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

          wd : (a b : Bool) → [ it a ] → [ it b ] → ¬ ¬ (a ≡ b)
          wd false false u v = ¬¬-in refl
          wd false true u v = λ _ → ¬¬resize-out u (¬¬-in v)
          wd true false u v = λ _ → ¬¬resize-out v (¬¬-in u)
          wd true true u v = ¬¬-in refl

          a-i : ¬ ¬ (Σ Bool (λ a → [ it a ]))
          a-i x = x (false , (¬resize-in _ (¬¬-in ny)))
            where
              ny : ¬ [ y ]
              ny z = x (true , z)

    f-g : (z : Ω¬¬) → f (g z) ≡ z
    f-g z = refl

    g-f : (x : ∇ Bool) → g (f x) ≡ x
    g-f x = ∇=-in (g (f x)) x (λ {true → (λ x → x) , (λ x → x) ; false → lem2 , lem1})
      where
        lem1 : [ ∇.is-this x false ] → [ ¬¬resize (¬ [ ∇.is-this x true ]) ]
        lem1 z = ¬¬resize-in λ w → ∇.well-defd x _ _ w z true≢false

        lem2 : [ ¬¬resize (¬ [ ∇.is-this x true ]) ] → [ ∇.is-this x false ]
        lem2 z = Ω¬¬-stab _ do
          w ← ¬¬resize-out z
          (true , v) ← ∇.almost-inh x
            where (false , v) → ¬¬-in v
          λ _ → w v
