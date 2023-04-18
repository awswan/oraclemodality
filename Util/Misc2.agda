open import Includes

open import Util.DoubleNegation
open import Cubical.Data.List
open import Cubical.Data.Bool

module Util.Misc2 where

inj→Separated : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → ((a a' : A) → f a ≡ f a' → a ≡ a') →
  Separated B → Separated A

inj→Separated f finj sepB a a' p = finj _ _ (sepB _ _ (¬¬-map (cong f) p))

separatedΠ : {A : Type ℓ} {B : A → Type ℓ'} (sepB : (a : A) → Separated (B a)) →
  Separated ((a : A) → B a)

separatedΠ sepB f g p = funExt (λ a → sepB a _ _ (¬¬-map (λ p' → funExt⁻ p' a) p))

separatedMaybe : {A : Type} → (Separated A) → (Separated (Maybe A))
separatedMaybe sepA nothing nothing p = refl
separatedMaybe sepA nothing (just a) p = ⊥rec (p ¬nothing≡just)
separatedMaybe sepA (just a) nothing p = ⊥rec (p ¬just≡nothing)
separatedMaybe sepA (just a) (just a') p = cong just (sepA _ _ (¬¬-map (just-inj _ _) p))

data allList {A : Type ℓ} (P : A → Type ℓ') : (List A) → Type (ℓ-max ℓ ℓ') where
  allNil : allList P []
  checkList : (a : A) → (p : P a) → (l : List A) → (q : allList P l) → allList P (a ∷ l)

all→allList : {A : Type ℓ} (P : A → Type ℓ') (all : (a : A) → P a) (l : List A) →
  allList P l
all→allList P all [] = allNil
all→allList P all (a ∷ l) = checkList a (all a) l (all→allList P all l)

inh→isContr→isProp : (A → isContr A) → isProp A
inh→isContr→isProp ic a a' = sym (snd (ic a) a) ∙ snd (ic a) a'

separatedBool : Separated Bool
separatedBool = Discrete→Separated Cubical.Data.Bool._≟_

