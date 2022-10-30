module SNERCT where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.PathSplit
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.Sum renaming (rec to ⊎rec)
open import Cubical.Data.Maybe renaming (rec to MaybeRec ; elim to MaybeElim)
open import Cubical.Data.Unit
open import Cubical.Data.Empty renaming (rec to ⊥rec)

open import NegativeResizing
open import PartialElements
open import OracleModality
open import ChurchsThesis
open import DoubleNegationSheaves
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import Util.HasUnderlyingType
open import Util.ModalOperatorInstances.PropTruncation


ℕwithVec : Type
ℕwithVec = ℕ × (Σ[ n ∈ ℕ ] (Fin n → ℕ))

postulate
  codeℕwithVecIso : Iso ℕwithVec ℕ

decodeℕ→ℕwithVec = Iso.inv codeℕwithVecIso
encodeℕwithVec→ℕ = Iso.fun codeℕwithVecIso

finiteSearchMaybe : (n : ℕ) → (A : Type ℓ) → (f : (m : Fin n) → Maybe A) → ((m : Fin n) → f m ≡ nothing) ⊎ (Σ[ (m , a) ∈ Fin n × A ] f m ≡ just a)
finiteSearchMaybe zero A f = inl (λ (m , p) → ⊥rec (¬-<-zero p))
finiteSearchMaybe (suc n) A f = ⊎rec (λ z → ⊎rec (λ p → inl (λ m → ⊎rec (λ q → cong f (toℕ-injective refl) ∙ z ((fst m) , q)) (λ q → cong f (toℕ-injective q) ∙ p) (<-split (snd m)))) (λ {(a , p) → inr (((n , ≤-refl) , a) , p)}) (lem (f (n , ≤-refl)))) (λ {((m , a) , p) → inr ((((fst m) , (≤-suc (snd m))) , a) , p)}) (finiteSearchMaybe n A λ m → f ((fst m) , (≤-suc (snd m))))
  where -- TODO: Cleanup
    lem : (w : Maybe A) → (w ≡ nothing) ⊎ (Σ[ a ∈ A ] w ≡ just a)
    lem nothing = inl refl
    lem (just x) = inr (x , refl)

module _ (χ : Oracle ℕ ℕ) where
  initialSeg : (l : ℕ) → (Fin l) → ∇ ℕ
  initialSeg l (i , _) = χ i

  -- eth Turing machine halts on input n in < l steps given first l - 1 values of oracle but may halt on other fragments of χ
  ψ₀ : ℕ → ℕ → (l : ℕ) → ((k : Fin l) → initialSeg l k ↓) → Maybe ℕ
  ψ₀ e n l approx = ⊎rec (λ _ → nothing) (λ { ((l' , m) , p) → just m}) (finiteSearchMaybe l ℕ λ l' → φ₀ e (encodeℕwithVec→ℕ (n , (l , λ k → fst (approx k)))) (fst l'))
  
  -- eth Turing machine halts on input from the first l values of oracle in ≤ l steps and this does not occur for any smaller values of l
  ψ₁ : ℕ → ℕ → (l : ℕ) → ((k : Fin l) → initialSeg l k ↓) → Maybe ℕ 
  ψ₁ e n l approx = ⊎rec (λ _ → ψ₀ e n l approx) (λ _ → nothing) (finiteSearchMaybe l ℕ (λ l' → ψ₀ e n (fst l') λ {(k , p) → approx (k , (<-trans p (snd l')))}))

  ψ : ℕ → ℕ → ∇ ℕ
  ψ e n = {!!}
