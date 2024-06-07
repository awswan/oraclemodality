open import Includes

open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Int
open import Cubical.Data.Bool

open import Cubical.Homotopy.Loopspace
open import Cubical.Foundations.Pointed

open import Cubical.Functions.FunExtEquiv

open import Axioms.NegativeResizing
open import DoubleNegationSheaves
open import OracleModality

open import Relativised.Bool

open import Util.HasUnderlyingType
open import Util.ModalOperatorSugar
open import Util.PartialElements
open import Util.DoubleNegation
open import Util.LexNull
open import Util.Nullification
open import Util.Misc
open import Util.Encodings

open import OracleModality
open import ParallelSearch

module HomotopyGroup where

π₀ : (Oracle ℕ Bool) → Type₁
π₀ χ = (◯[ χ ] ℕ) ≡ (◯[ χ ] ℕ)

F : (A : Type) → (A → Type) → (Σ[ A ∈ Type ] (A → Type))
F A Y = A , Y

D : Σ[ A ∈ Type ] (A → Type) → Type
D (X , Y) = Σ X Y

DFFibreLemma : (A X : Type) → fiber (D ∘ F A) X ≃ (X → A)
DFFibreLemma A X =
  fiber (D ∘ F A) X
    ≃⟨ Σ-cong-equiv-fst (invEquiv (fibrationEquiv A ℓ-zero)) ⟩
  (Σ[ (W , f) ∈ (Σ[ W ∈ Type ] (W → A)) ] W ≡ X)
    ≃⟨ isoToEquiv rearrange ⟩
  (Σ[ (W , p) ∈ (Σ[ W ∈ Type ] (X ≡ W)) ] (W → A))
    ≃⟨ Σ-contractFst (isContrSingl _) ⟩
  (X → A)
    ■
  where
    DF' : (Σ[ T ∈ Type ] (T → A)) → Type
    DF' (T , f) = T

    rearrange : Iso (Σ[ (W , f) ∈ (Σ[ W ∈ Type ] (W → A)) ] W ≡ X)
                    (Σ[ (W , p) ∈ (Σ[ W ∈ Type ] (X ≡ W)) ] (W → A))
    Iso.fun rearrange ((W , f) , p) = (W , (sym p)) , f
    Iso.inv rearrange ((W , p) , f) = (W , f) , (sym p)
    Iso.leftInv rearrange z = refl
    Iso.rightInv rearrange z = refl

DFEmbedding : (A X : Type) → (isSet A) → isEmbedding (cong {x = λ _ → X} {y = λ _ → X} (D ∘ (F A)))
DFEmbedding A X Aset =
  hasPropFibersOfImage→isEmbedding λ p → subst isProp (sym (fiberCong (D ∘ (F A)) (cong (D ∘ (F A)) p)))
                                   (isOfHLevelRespectEquiv 2 (invEquiv (DFFibreLemma A _)) (isSetΠ (λ _ → Aset)) _ _)

liftPath : (A B : Type) (p : A ≡ B) (X : A → Type) → F A X ≡ F B (X ∘ transport⁻ p)
liftPath A B p X i = F (p i) λ a → X (transp (λ j → p (~ j ∧ i)) (~ i) a)

conjugateLemma : (X A : Type) (q : A → X ≡ X) → (B : Type) → (p : A ≡ B) →
   (cong (F B) (funExt (q ∘ transport⁻ p))) ≡
               sym (liftPath A B p (λ _ → X)) ∙∙ cong (F A) (funExt q) ∙∙ liftPath A B p (λ _ → X)

conjugateLemma X A q B p =
  J (λ B p → (cong (F B) (funExt (q ∘ transport⁻ p))) ≡
               sym (liftPath A B p (λ _ → X)) ∙∙ cong (F A) (funExt q) ∙∙ liftPath A B p (λ _ → X))
  (λ i j → hcomp (λ k → λ {(i = i0) → F A (transport-filler refl (λ a → q a j) k)
                          ; (j = i0) → liftPath A A refl (λ _ → X) (k ∧ i)
                          ; (j = i1) → liftPath A A refl (λ _ → X) (k ∧ i)}) (cong (F A) (funExt q) j)) p

ℤ∗ = Maybe ℤ

ℕ→ℤ = fst ℤCtbl
ℤ→ℕ = invEq ℤCtbl

private
  ℤB = ℤ∗ × Bool


ℤBCtbl : ℕ ≃ (ℤ∗ × Bool)
ℤBCtbl =
  ℕ
    ≃⟨ invEquiv oddEvenEquiv ⟩
  ℕ ⊎ ℕ
    ≃⟨ ⊎-equiv (isoToEquiv (invIso ℕ+Iso)) (isoToEquiv (invIso ℕ+Iso)) ⟩
  (Unit ⊎ ℕ) ⊎ (Unit ⊎ ℕ)
    ≃⟨ ⊎-equiv (⊎-equiv (idEquiv _) ℤCtbl) (⊎-equiv (idEquiv _) ℤCtbl) ⟩
  (Unit ⊎ ℤ) ⊎ (Unit ⊎ ℤ)
    ≃⟨ ⊎-equiv Maybe≃SumUnit Maybe≃SumUnit ⟩
  ℤ∗ ⊎ ℤ∗
    ≃⟨ isoToEquiv rearrange ⟩
  ℤ∗ × Bool
    ■
  where
    Maybe≃SumUnit = isoToEquiv (invIso (iso Maybe→SumUnit SumUnit→Maybe SumUnit→Maybe→SumUnit Maybe→SumUnit→Maybe))
      where
        open SumUnit
    
    rearrange : Iso (ℤ∗ ⊎ ℤ∗) (ℤ∗ × Bool)
    Iso.fun rearrange (inl n) = n , false
    Iso.fun rearrange (inr n) = n , true
    Iso.inv rearrange (n , false) = inl n
    Iso.inv rearrange (n , true) = inr n
    Iso.leftInv rearrange (inl n) = refl
    Iso.leftInv rearrange (inr n) = refl
    Iso.rightInv rearrange (n , false) = refl
    Iso.rightInv rearrange (n , true) = refl

ℕ→ℤ∗B : ℕ → ℤ∗ × Bool
ℕ→ℤ∗B = fst ℤBCtbl

τ : ℤ → ℤ∗ → ℤ∗
τ n nothing = just n
τ n (just m) with (discreteℤ n m)
... | (yes p) = nothing
... | (no ¬p) = just m

τInvol : (n : ℤ) (m : ℤ∗) → (τ n (τ n m) ≡ m)
τInvol n nothing with (discreteℤ n n)
... | (yes p) = refl
... | (no ¬p) = ⊥rec (¬p refl)
τInvol n (just m) with (discreteℤ n m)
... | (yes p) = cong just p
... | (no ¬p) with (discreteℤ n m)
... | (yes q) = ⊥rec (¬p q)
... | (no ¬q) = refl


module _ (χ : Oracle ℕ Bool) where
  G→EquivEquiv : (◯[ χ ] ℤ∗ × ◯[ χ ] Bool ≡ ◯[ χ ] ℤ∗ × ◯[ χ ] Bool) ≃ (Σ[ f ∈ (ℤ∗ × Bool → ◯[ χ ] (ℤ∗ × Bool)) ] isEquiv (nullRec (isNull-Null (oDefd χ)) f))
  G→EquivEquiv =
               (◯[ χ ] ℤ∗ × ◯[ χ ] Bool) ≡ (◯[ χ ] ℤ∗ × ◯[ χ ] Bool)
                 ≃⟨ univalence ⟩
               ◯[ χ ] ℤ∗ × ◯[ χ ] Bool ≃ ◯[ χ ] ℤ∗ × ◯[ χ ] Bool
                 ≃⟨ equivComp (invEquiv (nullΣEquiv (oDefd χ))) (invEquiv (nullΣEquiv (oDefd χ))) ⟩
               ◯[ χ ] (ℤ∗ × Bool) ≃ ◯[ χ ] (ℤ∗ × Bool)
                 ≃⟨ idEquiv _ ⟩
               Σ[ f ∈ (◯[ χ ] (ℤ∗ × Bool) → ◯[ χ ] (ℤ∗ × Bool)) ] isEquiv f
                 ≃⟨ invEquiv (Σ-cong-equiv-fst (invEquiv (NullRecEquiv (isNull-Null _)))) ⟩
               Σ[ f ∈ (ℤ∗ × Bool → ◯[ χ ] (ℤ∗ × Bool)) ] isEquiv (nullRec (isNull-Null (oDefd χ)) f)
                 ■

  G→Fun : (◯[ χ ] ℤ∗ × ◯[ χ ] Bool ≡ ◯[ χ ] ℤ∗ × ◯[ χ ] Bool) → (ℤ∗ × Bool) → ◯[ χ ] (ℤ∗ × Bool)
  G→Fun g zb = fst (fst G→EquivEquiv g) zb

  G→FunInj : (g h : (◯[ χ ] ℤ∗ × ◯[ χ ] Bool ≡ ◯[ χ ] ℤ∗ × ◯[ χ ] Bool)) → (G→Fun g ≡ G→Fun h) → (g ≡ h)
  G→FunInj g h p = equiv→Inj (snd G→EquivEquiv) (Σ≡Prop (λ _ → isPropIsEquiv _) p)


module _ (χ χ' : Oracle ℕ Bool) where
  distinguishℤB : (f g h k : ℤB → ◯[ χ' ] ℤB) → ¬ ((f ≡ g) × (h ≡ k)) → ◯[ χ' ] ((¬ (f ≡ g)) ⊎ (¬ (h ≡ k)))
  distinguishℤB = subst (λ N → (f g h k : N → ◯[ χ' ] N) → ¬ ((f ≡ g) × (h ≡ k)) → ◯[ χ' ] ((¬ (f ≡ g)) ⊎ (¬ (h ≡ k)))) (ua ℤBCtbl) (distinguish' χ' separatedBool)

  G = ⟨ Ω (Type , (D (F (◯[ χ ] ℤ∗) (λ _ → ◯[ χ ] Bool)))) ⟩
  G' = ⟨ Ω (Type , (D (F (◯[ χ' ] ℤ∗) (λ _ → ◯[ χ' ] Bool)))) ⟩

  G'→Fun = G→Fun χ'
  G'→FunInj = G→FunInj χ'

  χℤ : ℤ → ∇ Bool
  χℤ n = χ (ℤ→ℕ n)

  abstract
    separatedG : Separated G
    separatedG = inj→Separated (fst ∘ fst (G→EquivEquiv χ)) (λ p q r → equiv→Inj (snd (G→EquivEquiv χ)) (Σ≡Prop (λ _ → isPropIsEquiv _) r)) (separatedΠ λ _ → separatedNull (λ n → χ n ↓ , ∇defd-prop separatedBool (χ n)) (λ n → ∇.almost-inh (χ n)) (separatedΣ (separatedMaybe (Discrete→Separated discreteℤ)) λ _ → separatedBool))

    separatedG' : Separated G'
    separatedG' = inj→Separated (fst ∘ fst (G→EquivEquiv χ')) (λ p q r → equiv→Inj (snd (G→EquivEquiv χ')) (Σ≡Prop (λ _ → isPropIsEquiv _) r)) (separatedΠ λ _ → separatedNull (λ n → χ' n ↓ , ∇defd-prop separatedBool (χ' n)) (λ n → ∇.almost-inh (χ' n)) (separatedΣ (separatedMaybe (Discrete→Separated discreteℤ)) λ _ → separatedBool))

  ∇dComp : {X : Pointed ℓ} → ∇ ⟨ Ω X ⟩ → ∇ ⟨ Ω X ⟩ → ∇ ⟨ Ω X ⟩ → ∇ ⟨ Ω X ⟩
  ∇.is-this (∇dComp {X = X} α β γ) s =
    ¬¬resize (Σ[ (a , u) ∈ α ↓ ] Σ[ (b , v) ∈ β ↓ ] Σ[ (c , w) ∈ γ ↓ ] s ≡ (a ∙∙ b ∙∙ c))
  ∇.well-defd (∇dComp {X = X} α β γ) s s' x x' = do
    ((a , u) , (b , v) , (c , w) , p) ← ¬¬resize-out x
    ((a' , u') , (b' , v') , (c' , w') , p') ← ¬¬resize-out x'
    aPath ← ∇.well-defd α a a' u u'
    bPath ← ∇.well-defd β b b' v v'
    cPath ← ∇.well-defd γ c c' w w'
    ¬¬-in (p ∙∙ (λ i → aPath i ∙∙ bPath i ∙∙ cPath i) ∙∙ sym p')
  ∇.almost-inh (∇dComp {X = X} α β γ) = do
    (a , u) ← ∇.almost-inh α
    (b , v) ← ∇.almost-inh β
    (c , w) ← ∇.almost-inh γ
    ¬¬-in ((a ∙∙ b ∙∙ c) , ¬¬resize-in ((a , u) , ((b , v) , ((c , w) , refl))))

  χPaths⊤ : ℤ∗ → (◯[ χ ] Bool ≡ ◯[ χ ] Bool)
  χPaths⊤ nothing = ⊕≡[] χ ∣ true ∣
  χPaths⊤ (just n) = ⊕≡[] χ (hub (ℤ→ℕ n) λ z → ∣ fst z ∣)

  χPaths⊤' : ◯[ χ ] ℤ∗ → (◯[ χ ] Bool ≡ ◯[ χ ] Bool)
  χPaths⊤' z = cong fst (nullRec (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop separatedBool (χ n))))) (λ n → Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _)) {u = (◯[ χ ] Bool) , (isNull-Null _)} {v = ◯[ χ ] Bool , isNull-Null _} (χPaths⊤ n)) z)

  χPaths⊥ : ℤ∗ → (◯[ χ ] Bool ≡ ◯[ χ ] Bool)
  χPaths⊥ nothing = ⊕≡[] χ ∣ false ∣
  χPaths⊥ (just n) = ⊕≡[] χ (hub (ℤ→ℕ n) λ z → ∣ fst z ∣)
 
  χPaths⊥' : ◯[ χ ] ℤ∗ → (◯[ χ ] Bool ≡ ◯[ χ ] Bool)
  χPaths⊥' z = cong fst (nullRec (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop separatedBool (χ n))))) (λ n → Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _)) {u = (◯[ χ ] Bool) , (isNull-Null _)} {v = ◯[ χ ] Bool , isNull-Null _} (χPaths⊥ n)) z)


  module _ (n : ℤ) where
    τχ : ◯[ χ ] ℤ∗ → ◯[ χ ] ℤ∗
    τχ = map[ χ ] (τ n)

    τχInvol : (m : ◯[ χ ] ℤ∗) → (τχ (τχ m) ≡ m)
    τχInvol = nullElim (λ _ → isNull≡ (isNull-Null _)) (λ m → cong ∣_∣ (τInvol n m))

    τχIso : Iso (◯[ χ ] ℤ∗) (◯[ χ ] ℤ∗)
    Iso.fun τχIso = τχ
    Iso.inv τχIso = τχ
    Iso.leftInv τχIso = τχInvol
    Iso.rightInv τχIso = τχInvol

    τχ≡ : (◯[ χ ] ℤ∗) ≡ (◯[ χ ] ℤ∗)
    τχ≡ = ua (isoToEquiv τχIso)

    abstract
      χPaths≡Lemma⊤₀ : χℤ n ↓= true → (m : Maybe ℤ) → ((χPaths⊤ (τ n m)) ≡ χPaths⊤ m)
      χPaths≡Lemma⊤₀ u nothing = cong (⊕≡[] χ) (spoke (ℤ→ℕ n) _ (true , u))
      χPaths≡Lemma⊤₀ u (just m) with (discreteℤ n m)
      ... | yes p = cong (⊕≡[] χ) (sym (spoke (ℤ→ℕ m) _ (true , subst (λ m → χ (ℤ→ℕ m) ↓= true) p u)))
      ... | no ¬p = refl

      χPaths≡Lemma⊤₁ : χℤ n ↓= true → (m : Maybe ℤ) → (χPaths⊤' (transport τχ≡ ∣ m ∣) ≡ χPaths⊤' ∣ m ∣)
      χPaths≡Lemma⊤₁ u m =
        χPaths⊤' (transport τχ≡ ∣ m ∣)
          ≡⟨ (λ i → χPaths⊤' (uaβ (isoToEquiv τχIso) ∣ m ∣ i)) ⟩
        χPaths⊤' (τχ ∣ m ∣)
          ≡⟨⟩
        χPaths⊤ (τ n m )
          ≡⟨ χPaths≡Lemma⊤₀ u m ⟩
        χPaths⊤ m
          ≡⟨⟩
        χPaths⊤' ∣ m ∣
          ∎

      χPaths≡Lemma⊤₂ : χℤ n ↓= true → (χPaths⊤' ∘ (transport τχ≡) ≡ χPaths⊤')
      χPaths≡Lemma⊤₂ u = funExt (nullElim (λ _ → isNull≡ (subst (isNull _) (ua (cong fst , isEmbeddingFstΣProp λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _) )) (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n) ) ) ) {x = (◯[ χ ] Bool) , isNull-Null _} {y = (◯[ χ ] Bool) , (isNull-Null _)}))) (χPaths≡Lemma⊤₁ u))

      χPaths≡Lemma⊤ : ¬ (χPaths⊤' ∘ (transport τχ≡) ≡ χPaths⊤') → χℤ n ↓= false
      χPaths≡Lemma⊤ np = Ω¬¬-stab _ (λ nu → np (χPaths≡Lemma⊤₂ (Ω¬¬-stab _ (λ nv → ∇.almost-inh (χℤ n) (λ {(false , u) → nu u ; (true , v) → nv v})))))

      χPaths≡Converse⊤ : (χPaths⊤' ∘ (transport τχ≡) ≡ χPaths⊤') → χℤ n ↓= true
      χPaths≡Converse⊤ p = Ω¬¬-stab _ (¬¬-map (λ z → subst (λ b → χℤ n ↓= b) (s z) (snd z)) (∇.almost-inh (χℤ n)))
        where
          q : χPaths⊤ (just n) ≡ χPaths⊤ nothing
          q =
            χPaths⊤ (just n)
              ≡⟨⟩
            χPaths⊤' ∣ just n ∣
              ≡⟨⟩
            χPaths⊤' (τχ ∣ nothing ∣)
              ≡⟨⟩
            χPaths⊤' (transport τχ≡ ∣ nothing ∣)
              ≡⟨ funExt⁻ p ∣ nothing ∣ ⟩
            χPaths⊤' ∣ nothing ∣
              ≡⟨⟩
            χPaths⊤ nothing
              ∎

          r : (hub {S = oDefd χ} (ℤ→ℕ n) λ z → ∣ fst z ∣) ≡ ∣ true ∣
          r = ⊕≡Inj[] χ _ _ q

          s : (z : χ (ℤ→ℕ n) ↓) → fst z ≡ true
          s z = separatedBool _ _ (∇→¬¬ (erase χ separatedBool (∣∣-inj (λ m → (oDefd χ m) , (∇defd-prop separatedBool (χ m))) _ _ (sym (spoke _ (λ z → ∣ fst z ∣) z) ∙ r))))

      χPaths≡Lemma⊥₀ : χℤ n ↓= false → (m : Maybe ℤ) → ((χPaths⊥ (τ n m)) ≡ χPaths⊥ m)
      χPaths≡Lemma⊥₀ u nothing = cong (⊕≡[] χ) (spoke (ℤ→ℕ n) _ (false , u))
      χPaths≡Lemma⊥₀ u (just m) with (discreteℤ n m)
      ... | yes p = cong (⊕≡[] χ) (sym (spoke (ℤ→ℕ m) _ (false , subst (λ m → χ (ℤ→ℕ m) ↓= false) p u)))
      ... | no ¬p = refl

      χPaths≡Lemma⊥₁ : χℤ n ↓= false → (m : Maybe ℤ) → (χPaths⊥' (transport τχ≡ ∣ m ∣) ≡ χPaths⊥' ∣ m ∣)
      χPaths≡Lemma⊥₁ u m =
        χPaths⊥' (transport τχ≡ ∣ m ∣)
          ≡⟨ (λ i → χPaths⊥' (uaβ (isoToEquiv τχIso) ∣ m ∣ i)) ⟩
        χPaths⊥' (τχ ∣ m ∣)
          ≡⟨⟩
        χPaths⊥ (τ n m )
          ≡⟨ χPaths≡Lemma⊥₀ u m ⟩
        χPaths⊥ m
          ≡⟨⟩
        χPaths⊥' ∣ m ∣
          ∎

      χPaths≡Lemma⊥₂ : χℤ n ↓= false → (χPaths⊥' ∘ (transport τχ≡) ≡ χPaths⊥')
      χPaths≡Lemma⊥₂ u = funExt (nullElim (λ _ → isNull≡ (subst (isNull _) (ua (cong fst , isEmbeddingFstΣProp λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _) )) (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n) ) ) ) {x = (◯[ χ ] Bool) , isNull-Null _} {y = (◯[ χ ] Bool) , (isNull-Null _)}))) (χPaths≡Lemma⊥₁ u))

      χPaths≡Lemma⊥ : ¬ (χPaths⊥' ∘ (transport τχ≡) ≡ χPaths⊥') → χℤ n ↓= true
      χPaths≡Lemma⊥ np = Ω¬¬-stab _ (λ nu → np (χPaths≡Lemma⊥₂ (Ω¬¬-stab _ (λ nv → ∇.almost-inh (χℤ n) (λ {(true , u) → nu u ; (false , v) → nv v})))))

      χPaths≡Converse⊥ : (χPaths⊥' ∘ (transport τχ≡) ≡ χPaths⊥') → χℤ n ↓= false
      χPaths≡Converse⊥ p = Ω¬¬-stab _ (¬¬-map (λ z → subst (λ b → χℤ n ↓= b) (s z) (snd z)) (∇.almost-inh (χℤ n)))
        where
          q : χPaths⊥ (just n) ≡ χPaths⊥ nothing
          q =
            χPaths⊥ (just n)
              ≡⟨⟩
            χPaths⊥' ∣ just n ∣
              ≡⟨⟩
            χPaths⊥' (τχ ∣ nothing ∣)
              ≡⟨⟩
            χPaths⊥' (transport τχ≡ ∣ nothing ∣)
              ≡⟨ funExt⁻ p ∣ nothing ∣ ⟩
            χPaths⊥' ∣ nothing ∣
              ≡⟨⟩
            χPaths⊥ nothing
              ∎

          r : (hub {S = oDefd χ} (ℤ→ℕ n) λ z → ∣ fst z ∣) ≡ ∣ false ∣
          r = ⊕≡Inj[] χ _ _ q

          s : (z : χ (ℤ→ℕ n) ↓) → fst z ≡ false
          s z = separatedBool _ _ (∇→¬¬ (erase χ separatedBool (∣∣-inj (λ m → (oDefd χ m) , (∇defd-prop separatedBool (χ m))) _ _ (sym (spoke _ (λ z → ∣ fst z ∣) z) ∙ r))))

  module _ (θ : ∇ G → ∇ G') (isEquivθ : isEquiv θ)
    (preservesComp : (α β γ : ∇ G) → θ (∇dComp α β γ) ≡ ∇dComp (θ α) (θ β) (θ γ)) where

    abstract
      compDefd : (α β γ : ∇ G) → (θ α ↓) → (θ β ↓) → (θ γ ↓) → θ (∇dComp α β γ) ↓
      compDefd α β γ (a , u) (b , v) (c , w) =
        subst (λ x → x ↓) (sym (preservesComp α β γ))
              ((a ∙∙ b ∙∙ c) , (¬¬resize-in ((a , u) , ((b , v) , ((c , w) , refl)))))

    private abstract
      getPath : (p p' : ◯[ χ ] ℤ∗ → ◯[ χ ] Bool ≡ ◯[ χ ] Bool) →
                θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt p))) ≡ θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt p'))) →
                p ≡ p'
      getPath p p' q = isoFunInjective funExtIso _ _ (isEmbedding→Inj (DFEmbedding _ _ (nullPreservesLevel (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n))) 2 (isOfHLevelMaybe 0 isSetℤ))) _ _ (separatedG _ _ (∇-in-inj (equiv→Inj isEquivθ q))))

    χPathDefd : (n : ℤ) → (θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt χPaths⊤'))) ↓) →
                          (θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt (χPaths⊤' ∘ transport (τχ≡ n))))) ↓) →
                          (θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt χPaths⊥'))) ↓) →
                          (θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt (χPaths⊥' ∘ transport (τχ≡ n))))) ↓) → ◯[ χ' ] (χℤ n ↓)
    χPathDefd n (top , ut) (toptau , utt) (bot , bt) (bottau , btt) =
      map[ χ' ] (⊎rec (λ p → false , (χPaths≡Lemma⊤ n (λ q → p (lemma⊤2 (sym q))))) (λ p → true , (χPaths≡Lemma⊥ n (λ q → p (lemma⊥2 (sym q)))))) cases
      where
        lemma⊤ : top ≡ toptau → (χPaths⊤' ≡ χPaths⊤' ∘ transport (τχ≡ n))
        lemma⊤ p = getPath χPaths⊤' (χPaths⊤' ∘ transport (τχ≡ n)) (∇-defd→path _ top ut ∙ cong ∇-in p ∙ sym (∇-defd→path _ toptau utt))

        lemma⊤2 : (χPaths⊤' ≡ χPaths⊤' ∘ transport (τχ≡ n)) → top ≡ toptau
        lemma⊤2 p = separatedG' top toptau (∇.well-defd (θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt (χPaths⊤' ∘ transport (τχ≡ n)))))) top toptau (subst (λ f → θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt f))) ↓= top) p ut) utt)

        lemma⊥ : bot ≡ bottau → (χPaths⊥' ≡ χPaths⊥' ∘ transport (τχ≡ n))
        lemma⊥ p = getPath _ _ (∇-defd→path _ bot bt ∙∙ cong ∇-in p ∙∙ sym (∇-defd→path _ bottau btt))

        lemma⊥2 : (χPaths⊥' ≡ χPaths⊥' ∘ transport (τχ≡ n)) → bot ≡ bottau
        lemma⊥2 p = separatedG' bot bottau (∇.well-defd (θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt (χPaths⊥' ∘ transport (τχ≡ n)))))) bot bottau (subst (λ f → θ (∇-in (cong (D ∘ F (◯[ χ ] ℤ∗)) (funExt f))) ↓= bot) p bt) btt)

        cases : ◯[ χ' ] ((¬ (top ≡ toptau)) ⊎ (¬ (bot ≡ bottau)))
        cases = map[ χ' ] (⊎map (λ p q → p (cong G'→Fun q)) λ p q → p (cong G'→Fun q)) (distinguishℤB (G'→Fun top) (G'→Fun toptau) (G'→Fun bot) (G'→Fun bottau) λ (p , q) → ∇.almost-inh (χ (ℤ→ℕ n)) (λ {(true , r) → ∇.well-defd (χℤ n) true false r (χPaths≡Converse⊥ n (sym (lemma⊥ (G'→FunInj _ _ q)))) true≢false ; (false , r) → ∇.well-defd (χℤ n) true false (χPaths≡Converse⊤ n (sym (lemma⊤ (G'→FunInj _ _ p)))) r true≢false}))
