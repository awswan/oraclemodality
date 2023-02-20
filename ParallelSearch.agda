open import OracleModality

open import Includes
open import Util.Everything
open import Util.PartialElements
open import DoubleNegationSheaves

open import Util.LexNull

module ParallelSearch where

{- Lemma V.4 -}
parallelSearch : (X : ℕ → Type ℓ) (Y : ℕ → Type ℓ') → ((n : ℕ) → ◯⟨ χ ⟩ (Dec (X n))) →
  ((n : ℕ) → ◯⟨ χ ⟩ (Dec (Y n))) → ¬ ¬ ((Σ[ n ∈ ℕ ] X n) ⊎ (Σ[ n ∈ ℕ ] Y n)) →
  ◯⟨ χ ⟩ ((Σ[ n ∈ ℕ ] X n) ⊎ (Σ[ n ∈ ℕ ] Y n))
parallelSearch {χ = χ} X Y decX decY z = do
    (n , xory) ← search χ XY almostXY XYdec
    ∣ ⊎map (λ x → (n , x)) (λ y → (n , y)) xory ∣
  where
    XY : ℕ → Type _
    XY n = (X n) ⊎ (Y n)

    almostXY : ¬ ¬ Σ ℕ XY
    almostXY = ¬¬-map (⊎rec (λ {(n , x) → n , (inl x)}) (λ {(n , y) → n , (inr y)})) z

    XYdec : (n : ℕ) → ◯⟨ χ ⟩ (Dec (XY n))
    XYdec n = do
      no xno ← decX n
        where yes xyes → ∣ yes (inl xyes) ∣
      no yno ← decY n
        where yes yyes → ∣ yes (inr yyes) ∣
      ∣ no (⊎rec xno yno) ∣

{- Lemma along similar lines to Lemmas V.5/V.6 -}
distinguish : {A : Type ℓa} {B : Type ℓb} (χ : Oracle A B) → (Separated B) →
  (Discrete X) → (f g : ℕ → ◯⟨ χ ⟩ X) → ¬ (f ≡ g) → (h : ℕ → ◯⟨ χ ⟩ X) →
  ◯⟨ χ ⟩ ((¬ h ≡ f) ⊎ (¬ h ≡ g))

distinguish {ℓa = ℓa} {ℓb = ℓb} {X = X} χ Bsep decX f g f≠g h = do
  z ← parallelSearch {χ = χ} (λ n → ¬ (h n ≡ f n)) (λ n → ¬ (h n ≡ g n)) (decf f) (decf g)
                     λ w → f≠g (almost w)
  ∣ ⊎map (λ {(n , p) q → p (funExt⁻ q n)}) (λ {(n , p) q → p (funExt⁻ q n)}) z ∣
  where
    -- Since X is discrete, so is ◯⟨ χ ⟩ X. Uses the fact that ◯⟨ χ ⟩ is lex.
    disc◯ : (x y : ◯⟨ χ ⟩ X) → (◯⟨ χ ⟩ (Dec (x ≡ y)))
    disc◯ = nullElim (λ _ → isNullΠ (λ _ → isNull-Null (oDefd χ)))
                     (λ x → nullElim (λ _ → isNull-Null (oDefd χ ))
                            (λ y → decRec (λ p → ∣ yes (cong ∣_∣ p) ∣)
                            (λ np → ∣ no (λ q → extract⊥ χ  (∣∣-inj (λ a → (χ a ↓) ,
                              (∇defd-prop Bsep (χ a))) _ _ q >>= (∣_∣ ∘ np))) ∣) (decX x y)))

    almost₀ : ¬ ((Σ[ n ∈ ℕ ] (¬ (h n ≡ f n)))) ⊎ (Σ[ n ∈ ℕ ] (¬ h n ≡ g n)) → (n : ℕ) →
      ¬ ¬ (f n ≡ g n)
    almost₀ z n = do
      hnfn ← λ u → z (inl (n , u))
      hngn ← λ v → z (inr (n , v))
      ¬¬-in (sym hnfn ∙ hngn)

    almost : ¬ ((Σ[ n ∈ ℕ ] (¬ (h n ≡ f n)))) ⊎ (Σ[ n ∈ ℕ ] (¬ h n ≡ g n)) → f ≡ g
    almost z =
      funExt (λ n → nullRec (isNull≡ (isNull-Null (oDefd χ)))
                            (decRec (λ x → x) (λ q → ⊥rec (almost₀ z n q)))
                            (disc◯ (f n) (g n)))

    decf : (f' : ℕ → ◯⟨ χ ⟩ X) → (n : ℕ) → ◯⟨ χ ⟩ (Dec (¬ h n ≡ f' n))
    decf f' n = disc◯ (h n) (f' n) >>= decRec (λ p → ∣ no (¬¬-in p) ∣) (λ np → ∣ yes np ∣)
