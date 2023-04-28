open import Includes

open import Util.ModalOperatorSugar

open import OracleModality

module Relativised.Bool where

module _ (χ : Oracle A B) where
  not[_] : ◯[ χ ] Bool → ◯[ χ ] Bool
  not[_] = map[ χ ] not

  not[_]≡ : ◯[ χ ] Bool ≡ ◯[ χ ] Bool
  not[_]≡ = cong ◯[ χ ] notEq

  notnot[] : (z : ◯[ χ ] Bool) → (not[_] (not[_] z) ≡ z)
  notnot[] = nullElim (λ _ → isNull≡ (isNull-Null (oDefd χ))) λ {false → refl ; true → refl}

  _⊕[]_ : ◯[ χ ] Bool → ◯[ χ ] Bool → ◯[ χ ] Bool
  _⊕[]_ = nullRec (isNullΠ (λ _ → isNull-Null (oDefd χ))) (λ {false → λ x → x ; true → not[_]})

  ⊕invol[] : (a b : ◯[ χ ] Bool) → (a ⊕[] (a ⊕[] b) ≡ b)
  ⊕invol[] = nullElim (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null (oDefd χ))))
                      (λ {false _ → refl ; true → notnot[]})

  ⊕unitR[] : (a : ◯[ χ ] Bool) → (a ⊕[] ∣ false ∣ ≡ a)
  ⊕unitR[] = nullElim (λ _ → isNull≡ (isNull-Null _)) (λ {false → refl ; true → refl})

  ⊕Iso[] : ◯[ χ ] Bool → Iso (◯[ χ ] Bool) (◯[ χ ] Bool)
  Iso.fun (⊕Iso[] a) b = a ⊕[] b
  Iso.inv (⊕Iso[] a) b = a ⊕[] b
  Iso.leftInv (⊕Iso[] a) = ⊕invol[] a 
  Iso.rightInv (⊕Iso[] a) = ⊕invol[] a

  ⊕≡[] : ◯[ χ ] Bool → (◯[ χ ] Bool ≡ ◯[ χ ] Bool)
  ⊕≡[] a = ua (isoToEquiv (⊕Iso[] a))

  ⊕≡Inj[] : (a a' : ◯[ χ ] Bool) → (⊕≡[] a ≡ ⊕≡[] a') → a ≡ a'
  ⊕≡Inj[] a a' p =
    a
      ≡⟨ sym (⊕unitR[] a) ⟩
    a ⊕[] ∣ false ∣
      ≡⟨ sym (uaβ (isoToEquiv (⊕Iso[] a)) ∣ false ∣) ⟩
    transport (⊕≡[] a) ∣ false ∣
      ≡⟨ cong (λ x → transport x ∣ false ∣) p ⟩
    transport (⊕≡[] a') ∣ false ∣
      ≡⟨ uaβ (isoToEquiv (⊕Iso[] a')) ∣ false ∣ ⟩
    a' ⊕[] ∣ false ∣
      ≡⟨ ⊕unitR[] a' ⟩
    a'
      ∎

