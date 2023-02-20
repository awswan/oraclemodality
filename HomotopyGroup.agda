open import Includes

open import Cubical.Functions.Fibration
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Int

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

open import OracleModality

module HomotopyGroup where

π₀ : (Oracle ℕ Bool) → Type₁
π₀ χ = (◯⟨ χ ⟩ ℕ) ≡ (◯⟨ χ ⟩ ℕ)

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

postulate
  ℤCtbl : Iso ℕ ℤ

ℕ→ℤ = Iso.fun ℤCtbl
ℤ→ℕ = Iso.inv ℤCtbl

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

module _ (χ χ' : Oracle ℕ Bool) where

  G = ⟨ Ω (Type , (D (F (◯⟨ χ ⟩ ℤ∗) (λ _ → ◯⟨ χ ⟩ Bool)))) ⟩
  G' = ⟨ Ω (Type , (D (F (◯⟨ χ' ⟩ ℤ∗) (λ _ → ◯⟨ χ' ⟩ Bool)))) ⟩

  χℤ : ℤ → ∇ Bool
  χℤ n = χ (ℤ→ℕ n)

  separatedG : Separated G
  separatedG p p' = {!!}

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

  χPaths⊤ : ℤ∗ → (◯⟨ χ ⟩ Bool ≡ ◯⟨ χ ⟩ Bool)
  χPaths⊤ nothing = ⊕≡⟨⟩ χ ∣ true ∣
  χPaths⊤ (just n) = ⊕≡⟨⟩ χ (hub (ℤ→ℕ n) λ z → ∣ fst z ∣)

  χPaths⊤' : ◯⟨ χ ⟩ ℤ∗ → (◯⟨ χ ⟩ Bool ≡ ◯⟨ χ ⟩ Bool)
  χPaths⊤' z = cong fst (nullRec (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n))))) (λ n → Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _)) {u = (◯⟨ χ ⟩ Bool) , (isNull-Null _)} {v = ◯⟨ χ ⟩ Bool , isNull-Null _} (χPaths⊤ n)) z)

  χPaths⊥ : ℤ∗ → (◯⟨ χ ⟩ Bool ≡ ◯⟨ χ ⟩ Bool)
  χPaths⊥ nothing = ⊕≡⟨⟩ χ ∣ false ∣
  χPaths⊥ (just n) = ⊕≡⟨⟩ χ (hub (ℤ→ℕ n) λ z → ∣ fst z ∣)

  χPaths⊥' : ◯⟨ χ ⟩ ℤ∗ → (◯⟨ χ ⟩ Bool ≡ ◯⟨ χ ⟩ Bool)
  χPaths⊥' z = cong fst (nullRec (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n))))) (λ n → Σ≡Prop (λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _)) {u = (◯⟨ χ ⟩ Bool) , (isNull-Null _)} {v = ◯⟨ χ ⟩ Bool , isNull-Null _} (χPaths⊥ n)) z)


  module _ (n : ℤ) where
    τχ : ◯⟨ χ ⟩ ℤ∗ → ◯⟨ χ ⟩ ℤ∗
    τχ = map⟨ χ ⟩ (τ n)

    τχInvol : (m : ◯⟨ χ ⟩ ℤ∗) → (τχ (τχ m) ≡ m)
    τχInvol = nullElim (λ _ → isNull≡ (isNull-Null _)) (λ m → cong ∣_∣ (τInvol n m))

    τχIso : Iso (◯⟨ χ ⟩ ℤ∗) (◯⟨ χ ⟩ ℤ∗)
    Iso.fun τχIso = τχ
    Iso.inv τχIso = τχ
    Iso.leftInv τχIso = τχInvol
    Iso.rightInv τχIso = τχInvol

    τχ≡ : (◯⟨ χ ⟩ ℤ∗) ≡ (◯⟨ χ ⟩ ℤ∗)
    τχ≡ = ua (isoToEquiv τχIso)

    χPaths≡Lemma⊤₀ : χℤ n ↓= true → (m : Maybe ℤ) → ((χPaths⊤ (τ n m)) ≡ χPaths⊤ m)
    χPaths≡Lemma⊤₀ u nothing = cong (⊕≡⟨⟩ χ) (spoke (ℤ→ℕ n) _ (true , u))
    χPaths≡Lemma⊤₀ u (just m) with (discreteℤ n m)
    ... | yes p = cong (⊕≡⟨⟩ χ) (sym (spoke (ℤ→ℕ m) _ (true , subst (λ m → χ (ℤ→ℕ m) ↓= true) p u)))
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
    χPaths≡Lemma⊤₂ u = funExt (nullElim (λ _ → isNull≡ (subst (isNull _) (ua (cong fst , isEmbeddingFstΣProp λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _) )) (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n) ) ) ) {x = (◯⟨ χ ⟩ Bool) , isNull-Null _} {y = (◯⟨ χ ⟩ Bool) , (isNull-Null _)}))) (χPaths≡Lemma⊤₁ u))

    χPaths≡Lemma⊤ : ¬ (χPaths⊤' ∘ (transport τχ≡) ≡ χPaths⊤') → χℤ n ↓= false
    χPaths≡Lemma⊤ np = Ω¬¬-stab _ (λ nu → np (χPaths≡Lemma⊤₂ (Ω¬¬-stab _ (λ nv → ∇.almost-inh (χℤ n) (λ {(false , u) → nu u ; (true , v) → nv v})))))

    χPaths≡Lemma⊥₀ : χℤ n ↓= false → (m : Maybe ℤ) → ((χPaths⊥ (τ n m)) ≡ χPaths⊥ m)
    χPaths≡Lemma⊥₀ u nothing = cong (⊕≡⟨⟩ χ) (spoke (ℤ→ℕ n) _ (false , u))
    χPaths≡Lemma⊥₀ u (just m) with (discreteℤ n m)
    ... | yes p = cong (⊕≡⟨⟩ χ) (sym (spoke (ℤ→ℕ m) _ (false , subst (λ m → χ (ℤ→ℕ m) ↓= false) p u)))
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
    χPaths≡Lemma⊥₂ u = funExt (nullElim (λ _ → isNull≡ (subst (isNull _) (ua (cong fst , isEmbeddingFstΣProp λ _ → isPropΠ (λ _ → isPropIsPathSplitEquiv _) )) (isNull≡ (Type◯-Null (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n) ) ) ) {x = (◯⟨ χ ⟩ Bool) , isNull-Null _} {y = (◯⟨ χ ⟩ Bool) , (isNull-Null _)}))) (χPaths≡Lemma⊥₁ u))

    χPaths≡Lemma⊥ : ¬ (χPaths⊥' ∘ (transport τχ≡) ≡ χPaths⊥') → χℤ n ↓= true
    χPaths≡Lemma⊥ np = Ω¬¬-stab _ (λ nu → np (χPaths≡Lemma⊥₂ (Ω¬¬-stab _ (λ nv → ∇.almost-inh (χℤ n) (λ {(true , u) → nu u ; (false , v) → nv v})))))



  module _ (θ : ∇ G → ∇ G') (isEquivθ : isEquiv θ)
    (preservesComp : (α β γ : ∇ G) → θ (∇dComp α β γ) ≡ ∇dComp (θ α) (θ β) (θ γ)) where

    compDefd : (α β γ : ∇ G) → (θ α ↓) → (θ β ↓) → (θ γ ↓) → θ (∇dComp α β γ) ↓
    compDefd α β γ (a , u) (b , v) (c , w) =
      subst (λ x → x ↓) (sym (preservesComp α β γ))
            ((a ∙∙ b ∙∙ c) , (¬¬resize-in ((a , u) , ((b , v) , ((c , w) , refl)))))

    private
      getPath : (p p' : ◯⟨ χ ⟩ ℤ∗ → ◯⟨ χ ⟩ Bool ≡ ◯⟨ χ ⟩ Bool) →
                θ (∇-in (cong (D ∘ F (◯⟨ χ ⟩ ℤ∗)) (funExt p))) ≡ θ (∇-in (cong (D ∘ F (◯⟨ χ ⟩ ℤ∗)) (funExt p'))) →
                p ≡ p'
      getPath p p' q = isoFunInjective funExtIso _ _ (isEmbedding→Inj (DFEmbedding _ _ (nullPreservesLevel (λ n → (χ n ↓) , (∇defd-prop (Discrete→Separated discreteBool) (χ n))) 2 (isOfHLevelMaybe 0 isSetℤ))) _ _ (separatedG _ _ (∇-in-inj (isEmbedding→Inj (isEquiv→isEmbedding isEquivθ) _ _ q))))

    χPathDefd : (n : ℤ) → (θ (∇-in (cong (D ∘ F (◯⟨ χ ⟩ ℤ∗)) (funExt χPaths⊤'))) ↓) →
                          (θ (∇-in (cong (D ∘ F (◯⟨ χ ⟩ ℤ∗)) (funExt (χPaths⊤' ∘ transport (τχ≡ n))))) ↓) →
                          (θ (∇-in (cong (D ∘ F (◯⟨ χ ⟩ ℤ∗)) (funExt χPaths⊥'))) ↓) →
                          (θ (∇-in (cong (D ∘ F (◯⟨ χ ⟩ ℤ∗)) (funExt (χPaths⊥' ∘ transport (τχ≡ n))))) ↓) → ◯⟨ χ' ⟩ (χℤ n ↓)
    χPathDefd n = {!!}
