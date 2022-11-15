open import Includes
open import Cubical.Foundations.GroupoidLaws

module Util.Sigma {A : Type ℓ} (B : A → Type ℓ') where

private variable
  a a' : A
  b b' : B a

ΣPathFst : {a a' : A} {b : B a} (p : a ≡ a') →
  (a , b) ≡ (a' , subst B p b)
ΣPathFst {b = b} p i = (p i) , (subst-filler B p b i)

ΣPathSnd : {b b' : B a} → (b ≡ b') → (a , b) ≡ (a , b')
ΣPathSnd {a = a} p = ΣPathP {B = λ _ → B} (refl , p)

ΣPathSndRefl : ΣPathSnd {b = b} {b' = b} refl ≡ refl
ΣPathSndRefl = refl

conjugatePath : {a a' : A} (p : a ≡ a') {b b' : B a} (q : b ≡ b') →
  ΣPathSnd (cong (subst B p) q) ≡ (sym (ΣPathFst p) ∙∙ ΣPathSnd q ∙∙ ΣPathFst p)

conjugatePath {a} {a'} p {b} {b'} q i j = 
  hcomp (λ k → λ {(j = i0) → ΣPathFst {b = b} p k
                 ; (j = i1) → ΣPathFst {b = b'} p k
                 ; (i = i0) → (p k) , subst-filler B p (q j) k})
        (a , q j)

conjugatePathSquare : {a a' : A} (p : a ≡ a') {b b' : B a} (q : b ≡ b') →
  PathP (λ i → ΣPathFst {b = b} p i ≡ ΣPathFst {b = b'} p i)
           (ΣPathSnd q) (ΣPathSnd (cong (subst B p) q))
conjugatePathSquare p q i j = (p i) , subst-filler B p (q j) i


conjugateLoop : {a : A} (p : a ≡ a) {b : B a} (q : b ≡ b) →
  ΣPathSnd (cong (subst B p) q) ≡ (sym (ΣPathFst p) ∙∙ ΣPathSnd q ∙∙ ΣPathFst p)
conjugateLoop p q = conjugatePath p q

includeFibre : {a : A} → (B a) → Σ A B
includeFibre {a} b = (a , b)

includeFibreIso : {a : A} → (ab' : Σ A B) → Iso (fiber (includeFibre {a = a}) ab') (a ≡ fst ab')
Iso.fun (includeFibreIso (a' , b')) (b , p) = cong fst p
Iso.inv (includeFibreIso (a' , b')) p =
  (subst B (sym p) b')
  ,  ΣPathP (p , λ i → subst-filler B (sym p) b' (~ i))
Iso.leftInv (includeFibreIso (a' , b')) (b , p) i = (α i0 i) , λ j → (fst (p j)) , α j i
  where
    α : (i : I) → subst-filler B (λ j → fst (p (~ j))) b' (~ i) ≡ snd (p i)
    α i j = fill (λ i' → B (fst (p (~ i'))))
                 (λ i' → λ {(j = i1) → snd (p (~ i'))
                           ; (j = i0) → subst-filler B ((λ j → fst (p (~ j)))) b' i'})
                 (inS b') (~ i)
Iso.rightInv (includeFibreIso (a' , b')) p = refl

fst-path : (a , b) ≡ _,_ {B = B} a' b' → a ≡ a'
fst-path p = cong fst p

snd-path : (p : (a , b) ≡ _,_ {B = B} a' b') → (subst B (fst-path p) b) ≡ b'
snd-path {b = b} p i = -- fromPathP (λ i → snd (p i))
  comp (λ j → B (fst-path p j))
       (λ j → λ {(i = i0) → subst-filler B (fst-path p) b j ; (i = i1) → snd (p j)})
       b

snd-path-filler : (p : (a , b) ≡ _,_ {B = B} a' b') → (i : I) → I → B (fst-path p i)
snd-path-filler {b = b} p i j = fill (λ j' → B (fst-path p j')) (λ j' → λ {(i = i0) → subst-filler B (fst-path p) b j' ; (i = i1) → snd (p j')}) (inS b) i


