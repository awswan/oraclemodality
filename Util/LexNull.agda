module Util.LexNull where

open import Includes


open import Util.ModalOperatorSugar
open import Util.Nullification
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
    extn-null = isNullΠ f1


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

  ∣∣-inj : {X : Type ℓ} → (x y : X) → (∣ x ∣ ≡ ∣ y ∣) → Null (fst ∘ S) (x ≡ y)
  ∣∣-inj {X = X} x y p = subst (fst ∘ Z) p ∣ refl ∣
    where
      Z : Null (fst ∘ S) X → Type◯
      Z = nullRec Type◯-Null (λ y' → Null (fst ∘ S) (x ≡ y') , isNull-Null _)

  ∣∣cong : {X : Type ℓ} → (x y : X) → Null (fst ∘ S) (x ≡ y) → ∣ x ∣ ≡ ∣ y ∣
  ∣∣cong x y = nullRec (isNull≡ (isNull-Null (fst ∘ S))) (cong ∣_∣)

  ∣∣≡Retract : {X : Type ℓ} → (x y : X) → Σ[ g ∈ (∣ x ∣ ≡ ∣ y ∣ → Null (fst ∘ S) (x  ≡  y)) ] ((p : ∣ x ∣ ≡ ∣ y ∣) → (∣∣cong _ _ (g p)) ≡ p)
  ∣∣≡Retract {X = X} x y = (λ p → ≡→Z ∣ y ∣ p) , λ p → ≡ZZ≡' ∣ y ∣ p
    where
      Z : Null (fst ∘ S) X → Type◯
      Z = nullRec Type◯-Null (λ y' → Null (fst ∘ S) (x ≡ y') , isNull-Null _)

      -- lemma : (y : Null (fst ∘ S) X) → (p : ∣ x ∣ ≡ y) → Σ[ y' ∈ X ] (Σ[ q ∈ x ≡ y' ] Σ[ r ∈ ∣ y' ∣ ≡ y ] p ≡ cong ∣_∣ q ∙ r)
      -- lemma y p = J (λ y p → Σ[ y' ∈ X ] (Σ[ q ∈ x ≡ y' ] Σ[ r ∈ ∣ y' ∣ ≡ y ] p ≡ cong ∣_∣ q ∙ r)) (x , refl , (refl , {!!})) p

      Z→≡ : (y : Null (fst ∘ S) X) → fst (Z y) → Null (fst ∘ S) (∣ x ∣ ≡ y)
      Z→≡ = nullElim (λ _ → isNullΠ (λ _ → isNull-Null _)) λ y' z → nullRec (isNull-Null _) (λ p → ∣ cong ∣_∣ p ∣) z

      Z→≡' : (y : Null (fst ∘ S) X) → fst (Z y) → (∣ x ∣ ≡ y)
      Z→≡' = nullElim (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null (fst ∘ S)))) (λ y → ∣∣cong _ _)

      ≡→Z : (y : Null (fst ∘ S) X) → (∣ x ∣ ≡ y) → fst (Z y)
      ≡→Z y p = subst (fst ∘ Z) p ∣ refl ∣

      ≡→Z' : (y : Null (fst ∘ S) X) → (Null (fst ∘ S) (∣ x ∣ ≡ y)) → (fst (Z y))
      ≡→Z' y = nullRec (snd (Z y)) (≡→Z y)

      ≡ZZ≡' : (y : Null (fst ∘ S) X) → (p : ∣ x ∣ ≡ y) → (Z→≡' y (≡→Z y p) ≡ p)
      ≡ZZ≡' y p = J (λ y p → (Z→≡' y (≡→Z y p) ≡ p)) base p
        where
          base : Z→≡' ∣ x ∣ (≡→Z ∣ x ∣ refl) ≡ refl
          base =
            Z→≡' ∣ x ∣ (≡→Z ∣ x ∣ refl)
              ≡⟨ congS (Z→≡' ∣ x ∣) (substRefl {B = fst ∘ Z} {x = ∣ x ∣} ∣ refl ∣) ⟩
            (Z→≡' ∣ x ∣ ∣ refl ∣)
              ≡⟨⟩
            refl
              ∎


      ≡ZZ≡ : (y : Null (fst ∘ S) X) → (p : ∣ x ∣ ≡ y) → (Z→≡ y (≡→Z' y ∣ p ∣) ≡ ∣ p ∣)
      ≡ZZ≡ y p = J (λ y p → (Z→≡ y (≡→Z' y ∣ p ∣) ≡ ∣ p ∣)) base p
        where
          base : Z→≡ ∣ x ∣ (≡→Z' ∣ x ∣ ∣ refl ∣) ≡ ∣ refl ∣
          base =
            (Z→≡ ∣ x ∣ (≡→Z' ∣ x ∣ ∣ refl ∣))
              ≡⟨⟩
            (Z→≡ ∣ x ∣ (≡→Z ∣ x ∣ refl))
              ≡⟨ congS {x = ≡→Z ∣ x ∣ refl} {y = ∣ refl ∣} (Z→≡ ∣ x ∣) (substRefl {B = fst ∘ Z} {x = ∣ x ∣} ∣ refl ∣) ⟩
            Z→≡ ∣ x ∣ ∣ refl ∣
              ≡⟨⟩
            ∣ refl ∣
              ∎

--      Z≡≡Z : (y : Null (fst ∘ S) X) → (z : fst (Z y)) → (≡→Z' y (Z→≡ y z) ≡ z)
--      Z≡≡Z = nullElim (λ y → isNullΠ (λ _ → isNull≡ (snd (Z y)))) λ y z → {!!}

  isOfHLevelNull : (n : HLevel) → isNull (fst ∘ S) X → isNull (fst ∘ S) (isOfHLevel n X)
  isOfHLevelNull zero nX = isNullΣ nX λ _ → isNullΠ (λ _ → isNull≡ nX)
  isOfHLevelNull (suc zero) nX = isNullΠ (λ _ → isNullΠ (λ _ → isNull≡ nX))
  isOfHLevelNull (suc (suc n)) nX = isNullΠ (λ _ → isNullΠ (λ _ → isOfHLevelNull (suc n) (isNull≡ nX)))

  nullPreservesLevel : {X : Type ℓ} (n : HLevel) → (isOfHLevel n X) → (isOfHLevel n (Null (fst ∘ S) X))
  nullPreservesLevel 0 l = ∣ fst l ∣ , (nullElim (λ _ → isNull≡ (isNull-Null _)) (λ b → cong ∣_∣ (snd l b)))
  nullPreservesLevel 1 l = nullElim (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null _))) (λ x → nullElim (λ _ → isNull≡ (isNull-Null _)) (λ y → cong ∣_∣ (l x y)))
  nullPreservesLevel (suc (suc n)) l = nullElim (λ _ → isNullΠ (λ _ → isOfHLevelNull _ (isNull≡ (isNull-Null _))))
    (λ x → nullElim (λ _ → isOfHLevelNull _ (isNull≡ (isNull-Null _))) (λ y → isOfHLevelRetract (suc n)
      (λ p → fst (∣∣≡Retract x y) p) (λ z → ∣∣cong x y z) (λ p → snd (∣∣≡Retract x y) p) (nullPreservesLevel (suc n) (l x y))))

  module _ (dense : (a : A) → ¬ ¬ ⟨ S a ⟩) where
    discreteNull : {X : Type ℓ} → (Discrete X) → (x y : Null (fst ∘ S) X) → Null (fst ∘ S) (Dec (x ≡ y))
    discreteNull Xdisc = nullElim (λ _ → isNullΠ (λ _ → isNull-Null _))
      (λ x → nullElim (λ _ → isNull-Null _) (λ y → decRec (λ p → ∣ yes (cong ∣_∣ p) ∣)
                         (λ ¬p → ∣ no (λ p → nullRec (isNull⊥ (fst ∘ S) dense) ¬p (∣∣-inj x y p)) ∣) (Xdisc x y)))

    separatedNull : {X : Type ℓ} → (Separated X) → Separated (Null (fst ∘ S) X)
    separatedNull sepX = nullElim (λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null _))))
                         λ x → nullElim (λ _ → isNullΠ (λ _ → isNull≡ (isNull-Null _)))
                         (λ y nnp → cong ∣_∣ (sepX _ _ (λ np → nnp (λ p → nullRec (isNull⊥ (fst ∘ S) dense) np (∣∣-inj _ _ p)))))
