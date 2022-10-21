module DoubleNegationPlus where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv

open import Cubical.Relation.Nullary

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Bool

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

∇=-in : (x y : ∇ A) → ((a : A) → ([ ∇.is-this x a ] ↔ [ ∇.is-this y a ])) → x ≡ y
∇=-in {A = A}
      x@(record { is-this = is-this
                ; well-defd = well-defd
                ; almost-inh = almost-inh })
      y@(record { is-this = is-this'
                ; well-defd = well-defd'
                ; almost-inh = almost-inh' }) eq =
      isoFunInjective (∇-as-Σ A) x y
                      (Σ≡Prop (λ a → isProp× (isPropΠ5 (λ _ _ _ _ _ → isProp⊥))
                              (isProp¬ _)) (funExt (λ a → Ω¬¬-ext _ _ (fst (eq a)) (snd (eq a)))))

∇-in : {A : Type ℓ} → A → ∇ A
∇-in {A = A} a =
  record { is-this = is-this
         ; well-defd = well-defd
         ; almost-inh = ¬¬-in (a , (¬¬resize-in refl)) }
  where
    is-this : A → Ω¬¬
    is-this b = ¬¬resize (b ≡ a)
    
    well-defd : (a b : A) → [ is-this a ] → [ is-this b ] → ¬ ¬ (a ≡ b)
    well-defd a b x y = do
      is-a ← ¬¬resize-out x
      is-b ← ¬¬resize-out y
      ¬¬-in (is-a ∙ sym is-b)

∇-in-inj : {a b : A} → (∇-in a ≡ ∇-in b) → ¬ ¬ (a ≡ b)
∇-in-inj {A = A} {a = a} {b = b} p = ∇.well-defd (∇-in b) a b (lem1 a (lem2 a)) (lem2 b)
  where
    lem1 : (c : A) → [ ¬¬resize (c ≡ a) ] → [ ¬¬resize (c ≡ b) ]
    lem1 c z = subst (λ x → [ ∇.is-this x c ]) p z

    lem2 : (c : A) → [ ∇.is-this (∇-in c) c ]
    lem2 c = ¬¬resize-in refl

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
∇-map {A = A} {B = B} f x =
  record { is-this = is-this
         ; well-defd = well-defd
         ; almost-inh = almost-inh }
  where
    module ∇A = ∇ x

    is-this : B → Ω¬¬
    is-this b = ¬¬resize (Σ A λ a → (b ≡ f a) × [ ∇A.is-this a ])

    well-defd : (b b' : B) → [ is-this b ] → [ is-this b' ] → ¬ ¬ (b ≡ b')
    well-defd b b' x x' = do
      (a , (p , z)) ← ¬¬resize-out x
      (a' , (p' , z')) ← ¬¬resize-out x'
      q ← ∇A.well-defd a a' z z'
      ¬¬-in (p ∙ cong f q ∙ sym p')

    almost-inh : ¬ ¬ (Σ B (λ b → [ is-this b ]))
    almost-inh = do
      (a , z) ← ∇A.almost-inh
      ¬¬-in ((f a) , (¬¬resize-in (a , (refl , z))))

∇-mult : ∇ (∇ A) → ∇ A
∇-mult {A = A} x =
  record { is-this = is-this ; well-defd = well-defd ; almost-inh = almost-inh }
  where
    is-this : A → Ω¬¬
    is-this a = ∇.is-this x (∇-in a)

    well-defd1 : (a b : A) → [ is-this a ] → [ is-this b ] → ¬ ¬ (∇-in a ≡ ∇-in b)
    well-defd1 a b u v = ∇.well-defd x _ _ u v

    well-defd : (a b : A) → [ is-this a ] → [ is-this b ] → ¬ ¬ (a ≡ b)
    well-defd a b u v = do
      p ← ∇.well-defd x _ _ u v
      ∇-in-inj p

    lem : (z : ∇ A) → (a : A) → [ ∇.is-this z a ] → z ≡ (∇-in a)
    lem z a w = ∇=-in z (∇-in a) (λ a' → f a' , g a')
      where
        f : (a' : A) → [ ∇.is-this z a' ] → [ ∇.is-this (∇-in a) a' ]
        f a' v = Ω¬¬-stab _ do
          p ← ∇.well-defd z a' a v w
          ¬¬-in (¬¬resize-in p)

        g : (a' : A) → [ ∇.is-this (∇-in a) a' ] → [ ∇.is-this z a' ]
        g a' u = Ω¬¬-stab _ do
          p ← ¬¬resize-out u
          ¬¬-in (subst _ (sym p) w)

    almost-inh : ¬ ¬ (Σ A (λ a → [ is-this a ]))
    almost-inh = do
      (x' , z) ← ∇.almost-inh x
      (a , w) ← ∇.almost-inh x'
      let q = lem x' a w
      ¬¬-in (a , subst (λ z → [ ∇.is-this x z ]) q z)

instance
  open ModalOperator
  ∇-bind : ModalOperator {ℓbase = ℓ-zero} {ℓ = ℓ} {ℓ' = ℓ'} ∇
  bind (∇-bind) x f = ∇-mult (∇-map f x)

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
