module Util.Nullification where

open import Includes

open import Cubical.Data.List

open import Util.HasUnderlyingType
open import Util.ModalOperatorSugar
open import Util.List

private variable
  ℓα ℓs : Level

instance
  open ModalOperator
  Null-bind : ∀ {A : Type ℓa} {S : A → Type ℓb} {ℓc ℓd : Level} →
              ModalOperator (ℓ-max ℓa ℓb) ℓc ℓd (Null S)
  bind (Null-bind {S = S}) a g = nullRec (isNull-Null S) g a
    -- Nullification.rec is more flexible than ◯-rec in allowing differing universe levels


NullPropElim : {A : Type ℓα} (S : A → Type ℓs) (P : Null S X → hProp ℓ) → ((x : X) → ⟨ P ∣ x ∣ ⟩) →
  ((α : A) → (f : S α → Null S X) → ((s : S α) → ⟨ P (f s) ⟩) → ⟨ P (hub α f) ⟩) →  ((z : Null S X) → ⟨ P z ⟩)
NullPropElim S P p₀ step ∣ x ∣ = p₀ x
NullPropElim S P p₀ step (hub α f) = step α f (λ s → NullPropElim S P p₀ step (f s))
NullPropElim S P p₀ step (spoke α f s i) =
  isProp→PathP (λ j → snd (P (spoke α f s j)))
                  (step α f (λ s → NullPropElim S P p₀ step (f s)))
                  (NullPropElim S P p₀ step (f s)) i
NullPropElim S P p₀ step (≡hub {x = x} {y = y} p i) =
  isProp→PathP (λ j → snd (P (≡hub p j)))
                  (NullPropElim S P p₀ step x)
                  (NullPropElim S P p₀ step y) i
NullPropElim S P p₀ step (≡spoke {x = x} {y = y} p s i j) =
  isSet→SquareP (λ i' j' → isProp→isSet (snd (P (≡spoke p s i' j'))))
                (isProp→PathP (λ j → snd (P (≡hub p j))) (NullPropElim S P p₀ step x) (NullPropElim S P p₀ step y))
                (λ j → NullPropElim S P p₀ step (p s j))
                (λ i → NullPropElim S P p₀ step x)
                (λ i → NullPropElim S P p₀ step y)
                i j

module _ {A : Type ℓα} (S : A → Type ℓs) where
  isNull⊥ : (dense : (a : A) → ¬ ¬ ( S a )) → (isNull S ⊥)
  isNull⊥ dense a = fromIsEquiv _ (snd (propBiimpl→Equiv isProp⊥ (isProp→ isProp⊥) _ (dense a)))

  ¬Null : (dense : (a : A) → ¬ ¬ ( S a ))
          {X : Type ℓ} → ¬ X → ¬ (Null S X)
  ¬Null dense ¬x x = nullRec (isNull⊥ dense) ¬x x

  module _ {X : Type ℓ} {Y : (Null S X) → Type ℓ'} where
    private
      pack : (x : Null S X) → (Null S (Y x)) → Null S (Σ X (Y ∘ ∣_∣))
      pack = nullElim (λ _ → isNullΠ (λ _ → isNull-Null S))
                      (λ x → nullRec (isNull-Null S) (λ y → ∣ x , y ∣))

    nullΣIso : Iso (Null S (Σ X (Y ∘ ∣_∣))) (Σ (Null S X) ((Null S) ∘ Y))
    Iso.fun nullΣIso = nullRec (isNullΣ (isNull-Null S) (λ _ → isNull-Null S))
                             (λ (x , y) → ∣ x ∣ , ∣ y ∣)
    Iso.inv nullΣIso (x , y) = pack x y
    Iso.leftInv nullΣIso = nullElim (λ _ → isNull≡ (isNull-Null S)) (λ (x , y) → refl)
    Iso.rightInv nullΣIso (x , y) =
      nullElim {Y = λ x → (y : Null S (Y x)) → Iso.fun nullΣIso (Iso.inv nullΣIso (x , y)) ≡ (x , y)}
               (λ _ → isNullΠ (λ _ → isNull≡ (isNullΣ (isNull-Null S) (λ _ → isNull-Null S))))
               (λ x' → nullElim (λ _ → isNull≡ (isNullΣ (isNull-Null S) (λ _ → isNull-Null S)))
                                (λ y' → refl)) x y

    nullΣEquiv = isoToEquiv nullΣIso

  nullList : {X : Type ℓ} (P : X → Type ℓ') (l : List X) → (allList (λ x → Null S (P x)) l) →
    Null S (allList P l)
  nullList P .[] allNil = ∣ allNil ∣
  nullList P .(a ∷ l) (checkList a p l z) = do
    ih ← nullList P l z
    step ← p
    ∣ checkList a step l ih ∣
