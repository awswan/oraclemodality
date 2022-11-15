module SymNat2 where

open import Util.Everything

open import Cubical.Data.Int
open import Includes

open import Cubical.HITs.PropositionalTruncation
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Univalence.Dependent
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.GroupoidLaws

open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Homotopy.Loopspace


open import MarkovInduction
open import ChurchsThesis
open import OracleModality
open import DoubleNegationSheaves
open import NegativeResizing
open import PartialElements
open import Util.LexNull
open import Util.Sigma

slice→Arrow : {A : Type ℓ} → (A → Type ℓ) → (Σ[ A' ∈ Type ℓ ] (A' →  Type ℓ))
slice→Arrow B = _ , B

dom : Σ[ A ∈ Type ℓ ] (A →  Type ℓ) → Type ℓ
dom (A , B) = Σ A B

module _ {ℓ : Level} where
  module S = Util.Sigma {A = Type ℓ} (λ A → A → Type ℓ)

  ΣEquivFst : {A A' : Type ℓ} {B : A → Type ℓ} (e : A' ≃ A) → (A , B) ≡ (A' , B ∘ transport (ua e))
  ΣEquivFst {A} {A'} {B} e = S.ΣPathFst (sym (ua e))

  ΣEquivFst' : {A A' : Type ℓ} {B : A → Type ℓ} (e : A' ≃ A) → (A , B) ≡ (A' , B ∘ equivFun e)
  ΣEquivFst' {A' = A'} {B = B} e = ΣEquivFst e ∙ λ i → A' , λ a' → B (uaβ e a' i)

  ΣEquivSnd : {A : Type ℓ} {B B' : A → Type ℓ} → ((a : A) → B a ≃ B' a) → (A , B) ≡ (A , B')
  ΣEquivSnd f = S.ΣPathSnd (funExt (λ a → ua (f a)))

  transpSq : {A A' : Type ℓ} (e : A' ≃ A) {B B' : A → Type ℓ}
    (f : (a : A) → B a ≃ B' a) →
    PathP (λ i → _,_ {B = λ A' → A' → Type ℓ} A' (λ a' → B (uaβ e a' i)) ≡
                                                 (A' , λ a' → B' (uaβ e a' i)))
             (ΣEquivSnd (f ∘ transport (ua e))) (ΣEquivSnd (f ∘ equivFun e))

  transpSq {A' = A'} e {B = B} {B' = B'} f i j = A' , λ a → ua (f (uaβ e a i)) j

  conjugateEquivSquare₀ : {A A' : Type ℓ} (e : A' ≃ A) {B B' : A → Type ℓ}
    (f : (a : A) → B a ≃ B' a) → PathP (λ i → ΣEquivFst {B = B} e i ≡ ΣEquivFst {B = B'} e i)
                                          (ΣEquivSnd f) (ΣEquivSnd (f ∘ (transport (ua e))))
  conjugateEquivSquare₀ e f = S.conjugatePathSquare (sym (ua e)) (funExt (λ a → ua (f a)))

  conjugateEquivSquare : {A A' : Type ℓ} (e : A' ≃ A) {B B' : A → Type ℓ}
    (f : (a : A) → B a ≃ B' a) → PathP (λ i → ΣEquivFst' {B = B} e i ≡ ΣEquivFst' {B = B'} e i)
                                          (ΣEquivSnd f) (ΣEquivSnd (f ∘ equivFun e))
  conjugateEquivSquare {A = A} {A' = A'} e {B} {B'} f i j =
    hcomp (λ k → λ {(i = i0) → ΣEquivSnd f j
                 ; (i = i1) → transpSq e f k j
                 ; (j = i0) → compPath-filler (ΣEquivFst {B = B} e) (λ i' → A' , λ a' → B (uaβ e a' i')) k i
                 ; (j = i1) → compPath-filler (ΣEquivFst {B = B'} e) (λ i' → A' , λ a' → B' (uaβ e a' i')) k i})
          (conjugateEquivSquare₀ e f i j)

