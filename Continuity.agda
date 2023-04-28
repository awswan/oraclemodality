open import Includes

open import OracleModality
open import RelativisedCT
open import Axioms.ChurchsThesis
open import Axioms.NegativeResizing


open import Util.PartialElements
open import Util.Encodings
open import Util.ModalOperatorSugar
open import Util.Nullification
open import Util.List
open import Util.StablePartial
open import Util.PropTruncationModalInstance
open import Util.DoubleNegation
open import DoubleNegationSheaves

open import Cubical.Data.List

module Continuity where

module _ (χ : Oracle ℕ ℕ) where
  decodeAt→Modulus : (e : Code) (t : haltingTime) → (z : decodeAtDom χ e t) →
    ◯[ χ ] (Σ[ f ∈ List ℕ ] ((χ' : Oracle ℕ ℕ) → allList (λ n → χ n ≡ χ' n) f → Σ[ w ∈ decodeAtDom χ' e t ] erase χ separatedℕ (decodeAt χ e t z) ≡ erase χ' separatedℕ (decodeAt χ' e t w)))
  decodeAt→Modulus (returnNat n) now z = ∣ [] , (λ χ' _ → tt , refl) ∣
  decodeAt→Modulus (queryOracleAndContinue n e) (later k t) z = do
    x ← query χ n
    (l , ih) ← decodeAt→Modulus (ℕ→Code (fromJust _ (fst (z x)))) t (snd (z x))
    ∣ n ∷ l , (λ χ' →
      λ { (checkList .n p .l q) → (λ w → (genIsJust x l ih p q w) ,
                     genDecodeAtDom x l ih p q w) ,
                     (cong (erase χ separatedℕ) (spoke n ((λ w → decodeAt χ (ℕ→Code (fromJust (φ₀ e (fst w) k) (fst (z w)))) t
          (snd (z w)))) x) ∙∙ snd (ih χ' q) ∙∙
            cong (erase χ' separatedℕ) ((λ i → decodeAt χ' (ℕ→Code (fromJust (φ₀ e (r x l ih p q (subst _↓ p x) i) k)
                                                           (genIsJustFiller x l ih p q (subst _↓ p x) i))) t (genDecodeAtDomFiller x l ih p q (subst _↓ p x) i)) ∙
            sym (spoke n ((λ w → decodeAt χ' (ℕ→Code (fromJust (φ₀ e (fst w) k) (genIsJust x l ih p q w))) t (genDecodeAtDom x l ih p q w))) (subst _↓ p x))))}) ∣
    where
      module _ (x : χ n ↓) where
        e' = ℕ→Code (fromJust (φ₀ e (fst x) k) (fst (z x)))

        module _ (l : List ℕ)
          (ih : (χ' : Oracle ℕ ℕ) → (allList (λ n → χ n ≡ χ' n) l) →
            Σ[ w ∈ decodeAtDom χ' e' t ] erase χ separatedℕ (decodeAt χ e' t (snd (z x))) ≡ erase χ' separatedℕ (decodeAt χ' e' t w)) (p : χ n ≡ χ' n) (q : allList (λ n → χ n ≡ χ' n) l) where

          module _ (w : χ' n ↓) where
            r : fst x ≡ fst w
            r i = fst (isProp→PathP (λ i → ∇defd-prop separatedℕ (p i)) x w i)
            
            genIsJust : isJust (φ₀ e (fst w) k)
            genIsJust = subst (λ u → isJust (φ₀ e u k)) r (fst (z x))

            genIsJustFiller = subst-filler (λ u → isJust (φ₀ e u k)) r (fst (z x))

            genDecodeAtDom : decodeAtDom χ' (ℕ→Code (fromJust (φ₀ e (fst w) k) genIsJust)) t
            genDecodeAtDom = transport (λ i → decodeAtDom χ' (ℕ→Code (fromJust (φ₀ e (r i) k) (genIsJustFiller i))) t) (fst (ih χ' q))

            genDecodeAtDomFiller : PathP (λ i → decodeAtDom χ' (ℕ→Code (fromJust (φ₀ e (r i) k) (genIsJustFiller i))) t) (fst (ih χ' q)) genDecodeAtDom
            genDecodeAtDomFiller = transport-filler ((λ i → decodeAtDom χ' (ℕ→Code (fromJust (φ₀ e (r i) k) (genIsJustFiller i))) t)) ((fst (ih χ' q)))

  localContinuity : (z : ◯[ χ ] ℕ) → ∥ Σ[ c ∈ Code ] ◯[ χ ] (Σ[ l ∈ List ℕ ] ((χ' : Oracle ℕ ℕ) → (allList (λ n → χ n ≡ χ' n) l) → Σ[ u ∈ decode χ' c ↓ ] erase χ separatedℕ z ≡ erase χ' separatedℕ (∂.value (decode χ' c) u))) ∥₁
  localContinuity z = do
    (e , w) ← decodeSurj χ z
    let mod' = do
      (t , v) ← computeHaltingTime χ e (¬¬resize-out (fst w))
      (l , defd) ← decodeAt→Modulus e t v
      ∣ l , (λ χ' p → ¬¬resize-in (t , (fst (defd χ' p))) , sym (cong (erase χ separatedℕ) (sym (snd (decodeWithPath χ e (fst w)) t v) ∙ snd w)) ∙∙ snd (defd χ' p) ∙∙ sym (cong (erase χ' separatedℕ) (snd (decodeWithPath χ' e (¬¬resize-in (t , (fst (defd χ' p))))) t (fst (defd χ' p))))) ∣
    ∣ e , mod' ∣₁
