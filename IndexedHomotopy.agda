module IndexedHomotopy where

open import Includes

open import Util.Everything

open import MarkovInduction
open import ChurchsThesis
open import OracleModality
open import DoubleNegationSheaves
open import NegativeResizing
open import PartialElements
open import Util.LexNull

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

-- encodeOracle : (χ : Oracle ℕ Bool) → ⟨ Ω ∏ ℕ S¹⟨ χ ⟩∙ ⟩
-- encodeOracle χ = funExt λ n → nullRec (≡-isNull (isNull-Null _)) (λ b → if b then ∣loop∣ χ else refl) (hub n (∣_∣ ∘ fst))
--   where
--     encodeLocal : ◯⟨ χ ⟩ Bool → ◯⟨ χ ⟩ (∣ base ∣ ≡ ∣ base ∣)
--     encodeLocal z = do
--       b ← z
--       ∣ if b then ∣loop∣ χ else refl ∣

-- checkEncodeFalse : (χ : Oracle ℕ Bool) (n : ℕ) → (χ n ↓= false) → (funExt⁻ (encodeOracle χ) n) ≡ refl
-- checkEncodeFalse χ n u = cong (λ b → nullRec (≡-isNull (isNull-Null _)) (λ b → if b then ∣loop∣ χ else refl) b) (spoke n (∣_∣ ∘ fst) (false , u))


-- plus : (χ : Oracle A B) → ◯⟨ χ ⟩ Bool → ◯⟨ χ ⟩ Bool → ◯⟨ χ ⟩ Bool
-- plus χ a b = do
--   a' ← a
--   b' ← b
--   ∣ a' ⊕ b' ∣

-- plusInv : (χ : Oracle A B) → (a : ◯⟨ χ ⟩ Bool) → (b : ◯⟨ χ ⟩ Bool) → (plus χ a (plus χ a b)) ≡ b
-- plusInv χ = nullElim (λ _ → NullPreservesΠ (λ _ → ≡-isNull (isNull-Null _)))
--                   λ a → nullElim (λ _ → ≡-isNull (isNull-Null _)) (λ b → cong ∣_∣ (⊕-invol a b))

-- plusIso : (χ : Oracle A B) → ◯⟨ χ ⟩ Bool → Iso (◯⟨ χ ⟩ Bool) (◯⟨ χ ⟩ Bool)
-- Iso.fun (plusIso χ a) b = plus χ a b
-- Iso.inv (plusIso χ a) b = plus χ a b
-- Iso.rightInv (plusIso χ a) b = plusInv χ a b
-- Iso.leftInv (plusIso χ a) b = plusInv χ a b

Type◯⟨_⟩ : {A : Type ℓa} {B : Type ℓb} → Oracle A B → {ℓ : Level} → Type (ℓ-suc (ℓ-max ℓ (ℓ-max ℓa ℓb)))
Type◯⟨_⟩ {ℓa = ℓa} {ℓb = ℓb} χ {ℓ = ℓ} = TypeWithStr (ℓ-max ℓ (ℓ-max ℓa ℓb)) (isNull (OM.domain χ {ℓ = ℓ-zero}))

isNullType◯⟨_⟩ :{A : Type} {B : Type} → (χ : Oracle A B) → Separated B → isNull (OM.domain χ {ℓ = ℓ-zero}) (Type◯⟨ χ ⟩ {ℓ = ℓ})
isNullType◯⟨_⟩ {ℓ = ℓ} χ sepB = Type◯-Null {ℓ = ℓ} (λ a → (χ a ↓) , (∇defd-prop sepB (χ a)))

Bool→loop : (χ : Oracle A B) → ◯⟨ χ ⟩ Bool → ⟨ Ω ((◯⟨ χ ⟩ S¹) , ∣ base ∣) ⟩
Bool→loop χ = nullRec (isNull≡ (isNull-Null (oDefd χ))) λ b → if b then ∣loop∣ χ else refl

loop→Bool : {A : Type} (χ : Oracle A Bool) → ⟨ Ω ((◯⟨ χ ⟩ S¹) , ∣ base ∣) ⟩ → ◯⟨ χ ⟩ Bool
loop→Bool χ p = subst (λ a → ⟨ action a ⟩) p ∣ false ∣
  where
    action₀ : S¹ → Type◯⟨ χ ⟩
    action₀ base = ◯⟨ χ ⟩ Bool , isNull-Null (oDefd χ)
    action₀ (loop i) = ◯⟨ χ ⟩ (notEq i) , isNull-Null (oDefd χ)
  
    action : ◯⟨ χ ⟩ S¹ → Type◯⟨ χ ⟩
    action = nullRec (isNullType◯⟨ χ ⟩ (Discrete→Separated discreteBool)) action₀

BoolLoopRetract : (χ : Oracle A Bool) → (z : ◯⟨ χ ⟩ Bool) → loop→Bool χ (Bool→loop χ z) ≡ z
BoolLoopRetract χ =
  nullElim (λ _ → isNull≡ (isNull-Null (oDefd χ)))
           λ {false → refl ; true → refl} -- the magic of cubical TT!


encodeOracle : (χ : Oracle ℕ Bool) → ⟨ Ω ∏ (Bool ⊎ ℕ) S¹⟨ χ ⟩∙ ⟩
encodeOracle χ = funExt (λ {(inl b) → Bool→loop χ ∣ b ∣ ; (inr n) → Bool→loop χ (hub n (∣_∣ ∘ fst)) })

τ : (χ : Oracle ℕ Bool) → ℕ → ⟨ Ω ∏ (Bool ⊎ ℕ) S¹⟨ χ ⟩∙ ⟩
τ χ n = {!!}

decodeAt : (χ : Oracle ℕ Bool) {C : Type ℓ} → ⟨ Ω ∏ C S¹⟨ χ ⟩∙ ⟩ → C → ◯⟨ χ ⟩ Bool
decodeAt χ {C = C} p c = {!!}

