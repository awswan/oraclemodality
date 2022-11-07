module Util.LexNull where

open import Includes

open import Util.HasUnderlyingType
open import Cubical.Foundations.Univalence

module _ {ℓa ℓs ℓ} {A : Type ℓa} (S : A → hProp ℓs) where
--  open Modality (TopModality {ℓ = ℓ} S)

  ℓm = ℓ-max ℓ (ℓ-max ℓa ℓs)

  Type◯ : Type (ℓ-suc ℓm)
  Type◯ = Σ (Type ℓm) λ X → isNull (fst ∘ S) X

  module ExtendTop (α : A) (f : ⟨ S α ⟩ → Type◯) where
    private
      f0 : ⟨ S α ⟩ → Type ℓm
      f0 z = fst (f z)

      f1 : (x : ⟨ S α ⟩) → isNull (fst ∘ S) (f0 x)
      f1 = snd ∘ f

    extn-type = (x : ⟨ S α ⟩) → f0 x

    extn-null : isNull (fst ∘ S) extn-type
    extn-null = NullPreservesΠ f1


    extn-equiv : (x0 : ⟨ S α ⟩) → extn-type ≃ f0 x0
    extn-equiv x0 =
      extn-type
        ≃⟨ invEquiv (equivΠ
                    (invEquiv
                      (isContr→≃Unit
                        (inhProp→isContr x0 (snd (S α)))))
                          (λ {tt → idEquiv _})) ⟩
      ((x : Unit) → c x)
        ≃⟨ ΠUnit c ⟩
      f0 x0 ■

      where
        c : Unit → Type ℓm
        c tt = f0 x0

    toextn : (X : Type ℓ) → (p : (z : ⟨ S α ⟩) → (X ≃ ⟨ f z ⟩)) → X → extn-type
    toextn X p x z = fst (p z) x

    extn-unique : (X : Type◯) → (p : (z : ⟨ S α ⟩) → (⟨ X ⟩ ≃ ⟨ f z ⟩)) → ⟨ X ⟩ ≃ extn-type
    extn-unique X p =
      ⟨ X ⟩
        ≃⟨ pathSplitToEquiv (_ , snd X α) ⟩
      (⟨ S α ⟩ → ⟨ X ⟩)
        ≃⟨ equivΠCod p ⟩
      extn-type
        ■


  Type◯-Null : isNull (fst ∘ S) Type◯
  Type◯-Null α = fromIsEquiv _ (isoToIsEquiv (iso _ (λ f → (extn-type f) , (extn-null f)) (λ f → funExt (λ z → Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _)) (ua (extn-equiv f z)))) λ X → Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _)) (sym (ua (extn-unique (λ _ → X) X (λ _ → idEquiv _))))))
    where
      open ExtendTop α
