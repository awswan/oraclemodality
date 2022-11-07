open import Includes

module Util.Transpositions (decA : Discrete A) (a b : A) where

transpose : A → A
transpose c with (decA c a)
transpose c | yes _ = b
transpose c | no _ with (decA c b)
transpose c | no _ | yes _ = a
transpose c | no _ | no _ = c

transposeL : transpose a ≡ b
transposeL with (decA a a)
... | yes _ = refl
... | no ¬p = ⊥rec (¬p refl)

transposeR : transpose b ≡ a
transposeR with (decA b a)
transposeR | yes p = p
transposeR | no ¬p with (decA b b)
transposeR | no ¬p | yes q = refl
transposeR | no ¬p | no ¬q = ⊥rec (¬q refl)

transposeId : (c : A) → (¬ c ≡ a) → (¬ c ≡ b) → (transpose c ≡ c)
transposeId c ¬p ¬q with (decA c a)
transposeId c ¬p ¬q | yes p = ⊥rec (¬p p)
transposeId c ¬p ¬q | no _ with (decA c b)
transposeId c ¬p ¬q | no _ | yes q = ⊥rec (¬q q)
transposeId c ¬p ¬q | no _ | no _ = refl

transposeInv : (c : A) → (transpose (transpose c) ≡ c)
transposeInv c with (decA c a)
transposeInv c | (yes p) = transposeR ∙ sym p
transposeInv c | (no ¬p) with (decA c b)
transposeInv c | (no ¬p) | yes q = transposeL ∙ sym q
transposeInv c | (no ¬p) | no ¬q = transposeId c ¬p ¬q

transposeIso : Iso A A
Iso.fun transposeIso = transpose
Iso.inv transposeIso = transpose
Iso.rightInv transposeIso = transposeInv
Iso.leftInv transposeIso = transposeInv
