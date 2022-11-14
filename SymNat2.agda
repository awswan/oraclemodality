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

open import MarkovInduction
open import ChurchsThesis
open import OracleModality
open import DoubleNegationSheaves
open import NegativeResizing
open import PartialElements
open import Util.LexNull

slice→Arrow : {A : Type ℓ} → (A → Type ℓ) → (Σ[ A' ∈ Type ℓ ] (A' →  Type ℓ))
slice→Arrow B = _ , B

dom : Σ[ A ∈ Type ℓ ] (A →  Type ℓ) → Type ℓ
dom (A , B) = Σ A B


composeLeft₀ : {A : Type ℓ} (B : A → Type ℓ) → (p : A ≡ A') →
  (slice→Arrow B ≡ slice→Arrow (B ∘ transport⁻ p))
composeLeft₀ B p i = (p i) , (λ a → B (comp (λ j → p (i ∧ ~ j))
  (λ j → λ {(i = i0) → a ; (i = i1) → transport⁻-filler p a j}) a))

composeLeft0 : {A : Type ℓ} (B : A → Type ℓ) → (p : A ≡ A') →
  (slice→Arrow B ≡ slice→Arrow (B ∘ transport⁻ p))
composeLeft0 B = J (λ _ p → slice→Arrow B ≡ slice→Arrow (B ∘ transport⁻ p))
                   λ i → slice→Arrow (λ a → B (transportRefl a (~ i)))

composeRight₀ : {A : Type ℓ} (B B' : A → Type ℓ) → (p : B ≡ B') →
  (slice→Arrow B ≡ slice→Arrow B')

composeRight₀ B B' = cong slice→Arrow


composeLeft : {A A' : Type ℓ} (B : A → Type ℓ) → (e : A' ≃ A) →
  (slice→Arrow B ≡ slice→Arrow (B ∘ (equivFun e)))
composeLeft B e i = ua e (~ i) , λ x → B (ua-unglue e (~ i) x)

composeLeftRefl : {A : Type ℓ} (B : A → Type ℓ) →
  (composeLeft B (idEquiv A) ≡ refl)
composeLeftRefl {A = A} B = λ j i → (ua (idEquiv A) (~ i)) , {!!}


composeRight : {A : Type ℓ} (B : A → Type ℓ) (e : (a : A) → B a ≃ B a) →
  (slice→Arrow B ≡ slice→Arrow B)
composeRight B e = cong slice→Arrow (funExt (λ a → ua (e a)))


left : ∀ {ℓ} → Type (ℓ-suc ℓ)
left = Σ[ X ∈ (Bool ⊎ ℤ → Type _) ] ∥ Σ (Bool ⊎ ℤ) X ≃ ℕ ∥₁

