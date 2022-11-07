module IndexedHomotopy where

open import Includes

open import Util.Everything

open import MarkovInduction
open import ChurchsThesis
open import OracleModality
open import DoubleNegationSheaves
open import NegativeResizing
open import PartialElements

open import Cubical.HITs.S1.Base
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Univalence
open import Cubical.Homotopy.Loopspace

-- countable product of circles
∏S¹ : Type
∏S¹ = ℕ → S¹

-- relativised product of circles indexed by C
∏_S¹⟨_⟩ : (C : Type ℓ) → (Oracle A B) → Type _
∏ C S¹⟨ χ ⟩ = C → ◯⟨ χ ⟩ S¹

∏_S¹⟨_⟩∙ : (C : Type ℓ) → (Oracle A B) → Pointed _
∏ C S¹⟨ χ ⟩∙ = ∏ C S¹⟨ χ ⟩ , (λ _ → ∣ base ∣)

∣loop∣ : (χ : Oracle A B) → ∣ base ∣ ≡ ∣ base ∣
∣loop∣ χ = cong {B = λ _ → ◯⟨ χ ⟩ S¹} ∣_∣ loop

encodeOracle : (χ : Oracle ℕ Bool) → ⟨ Ω ∏ (Bool ⊎ ℕ) S¹⟨ χ ⟩∙ ⟩
encodeOracle χ = funExt (λ {(inl false) → refl
                              ; (inl true) → ∣loop∣ χ
                              ; (inr n) → ≡hub {α = n} λ {(false , _) → refl ; (true , _) → ∣loop∣ χ} })

plus : (χ : Oracle A B) → ◯⟨ χ ⟩ Bool → ◯⟨ χ ⟩ Bool → ◯⟨ χ ⟩ Bool
plus χ a b = do
  a' ← a
  b' ← b
  ∣ a' ⊕ b' ∣

plusInv : (χ : Oracle A B) → (a : ◯⟨ χ ⟩ Bool) → (b : ◯⟨ χ ⟩ Bool) → (plus χ a (plus χ a b)) ≡ b
plusInv χ = nullElim (λ _ → NullPreservesΠ (λ _ → ≡-isNull (isNull-Null _)))
                  λ a → nullElim (λ _ → ≡-isNull (isNull-Null _)) (λ b → cong ∣_∣ (⊕-invol a b))

plusIso : (χ : Oracle A B) → ◯⟨ χ ⟩ Bool → Iso (◯⟨ χ ⟩ Bool) (◯⟨ χ ⟩ Bool)
Iso.fun (plusIso χ a) b = plus χ a b
Iso.inv (plusIso χ a) b = plus χ a b
Iso.rightInv (plusIso χ a) b = plusInv χ a b
Iso.leftInv (plusIso χ a) b = plusInv χ a b


decodeAt : {χ : Oracle ℕ Bool} {C : Type ℓ} → ⟨ Ω ∏ C S¹⟨ χ ⟩∙ ⟩ → C → Bool
decodeAt {χ = χ} {C = C} p c = {!!}
  where
    action : ◯⟨ χ ⟩ S¹ → Type _
    action ∣ base ∣ = ◯⟨ χ ⟩ Bool
    action ∣ loop i ∣ = isoToPath (plusIso χ ∣ true ∣) i
    action (hub α f) = ◯⟨ χ ⟩ Bool
    action (spoke α f s i) = {!◯⟨ χ ⟩ Bool!}
    action (≡hub p i) = {!!}
    action (≡spoke p s i i₁) = {!!}
