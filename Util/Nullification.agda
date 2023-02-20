module Util.Nullification where

open import Includes

open import Util.HasUnderlyingType

private variable
  ℓα ℓs : Level

NullPropElim : {A : Type ℓα} (S : A → Type ℓs) (P : Null S X → hProp ℓ) → ((x : X) → ⟨ P ∣ x ∣ ⟩) →
  ((α : A) → (f : S α → Null S X) → ((s : S α) → ⟨ P (f s) ⟩) → ⟨ P (hub α f) ⟩) →  ((z : Null S X) → ⟨ P z ⟩)
NullPropElim S P p₀ step ∣ x ∣ = p₀ x
NullPropElim S P p₀ step (hub α f) = step α f (λ s → NullPropElim S P p₀ step (f s))
NullPropElim S P p₀ step (spoke α f s i) =
  isProp→PathP (λ j → snd (P (spoke α f s j)))
                  (step α f (λ s → NullPropElim S P p₀ step (f s)))
                  (NullPropElim S P p₀ step (f s)) i
NullPropElim S P p₀ step (≡hub {x = x} {y = y} p i) =
  isProp→PathP (λ j → snd (P (≡hub p j)))
                  (NullPropElim S P p₀ step x)
                  (NullPropElim S P p₀ step y) i
NullPropElim S P p₀ step (≡spoke {x = x} {y = y} p s i j) =
  isSet→SquareP (λ i' j' → isProp→isSet (snd (P (≡spoke p s i' j'))))
                (isProp→PathP (λ j → snd (P (≡hub p j))) (NullPropElim S P p₀ step x) (NullPropElim S P p₀ step y))
                (λ j → NullPropElim S P p₀ step (p s j))
                (λ i → NullPropElim S P p₀ step x)
                (λ i → NullPropElim S P p₀ step y)
                i j
