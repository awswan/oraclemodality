open import Includes

open import Cubical.Data.List

module Util.List where

data allList {A : Type ℓ} (P : A → Type ℓ') : (List A) → Type (ℓ-max ℓ ℓ') where
  allNil : allList P []
  checkList : (a : A) → (p : P a) → (l : List A) → (q : allList P l) → allList P (a ∷ l)

all→allList : {A : Type ℓ} (P : A → Type ℓ') (all : (a : A) → P a) (l : List A) →
  allList P l
all→allList P all [] = allNil
all→allList P all (a ∷ l) = checkList a (all a) l (all→allList P all l)

range : (n : ℕ) → List ℕ
range zero = []
range (suc n) = n ∷ range n

allRange→allFin : (X : ℕ → Type ℓ) (n : ℕ) → (allList X (range n)) → (k : Fin n) → X (fst k)
allRange→allFin X zero z k = ⊥rec (¬-<-zero (snd k))
allRange→allFin X (suc n) (checkList .n p .(range n) z) k =
  ⊎rec (λ q → allRange→allFin X n z ((fst k) , q)) (λ q → subst X (sym q) p) (<-split (snd k))

Lmax : List ℕ → ℕ
Lmax [] = 0
Lmax (x ∷ l) = max x (Lmax l)

LmaxAllFin→allList : (X : ℕ → Type ℓ) (l : List ℕ) (g : (k : Fin (suc (Lmax l))) → X (fst k)) →
  allList X l
LmaxAllFin→allList X [] g = allNil
LmaxAllFin→allList X (x ∷ l) g =
  checkList x (g (x , ≤<-trans left-≤-max ≤-refl)) l
    (LmaxAllFin→allList X l (λ k → g ((fst k) , <≤-trans (snd k) (suc-≤-suc right-≤-max))))
