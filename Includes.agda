module Includes where

open import Cubical.Core.Everything public
open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Function public
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Isomorphism public
open import Cubical.Foundations.Equiv public
open import Cubical.Foundations.Univalence public
open import Cubical.Foundations.Equiv.PathSplit public
open import Cubical.Foundations.Equiv.Properties public
open import Cubical.Foundations.Structure hiding (⟨_⟩) public

open import Cubical.Relation.Nullary public
open import Cubical.Induction.WellFounded public

open import Cubical.Data.Unit public
open import Cubical.Data.Empty public renaming (rec to ⊥rec ; elim to ⊥elim)
open import Cubical.Data.Sigma public
open import Cubical.Data.Nat public renaming (elim to ℕelim)
open import Cubical.Data.Nat.Order public
open import Cubical.Data.Fin public renaming (elim to FinElim)
open import Cubical.Data.Sum public renaming (rec to ⊎rec ; elim to ⊎elim ; map to ⊎map)
open import Cubical.Data.Bool public hiding (_≤_ ; _≥_ ; isProp≤) renaming (_≟_ to discreteBool)
open import Cubical.Data.Maybe public renaming (rec to maybeRec ; elim to maybeElim)

open import Cubical.HITs.Nullification public renaming (rec to nullRec ; elim to nullElim)

variable
  ℓ ℓ' ℓ'' : Level
  ℓa ℓb ℓa' ℓb' : Level
  A B X : Type ℓ
