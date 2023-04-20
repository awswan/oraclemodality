open import Includes

open import OracleModality
open import DoubleNegationSheaves
open import RelativisedCT

open import Cubical.Functions.Embedding

open import Axioms.ChurchsThesis
open import Axioms.NegativeResizing

open import Util.DoubleNegation
open import Util.Encodings
open import Util.StablePartial
open import Util.PartialElements
open import Util.ModalOperatorSugar
open import Util.Nullification
open import Util.PropTruncationModalInstance

open import Cubical.Data.List hiding ([_])
open import Util.Misc2

module WeakTT where

{- A synthetic definition of weak truth reducibility -}
_≤wtt'_ : {A : Type ℓa} {B : Type ℓb} {A' : Type ℓa'} {B' : Type ℓb'} (χ : Oracle A B) (χ' : Oracle A' B') → Type (ℓ-max (ℓ-max ℓa ℓb) (ℓ-max ℓa' ℓb'))
_≤wtt'_ {A = A} {A' = A'} χ χ' = (a : A) → Σ[ l ∈ (List A') ] (allList (λ a' → χ' a' ↓) l → χ a ↓ )

computeHead : {A : Type ℓ} (χ : ℕ → ∇ A) → (n : ℕ) → ◯⟨ χ ⟩ ((m : Fin n) → χ (fst m) ↓)
computeHead χ zero = ∣ (λ z → ⊥rec (¬-<-zero (snd z))) ∣
computeHead χ (suc n) = do
  ih ← computeHead χ n
  next ← query χ n
  ∣ (λ z → ⊎rec (λ p → ih ((fst z) , p)) (λ p → subst (λ m → χ m ↓)  (sym p) next) (<-split (snd z))) ∣

_≤wtt_ : (χ : Oracle ℕ Bool) (χ' : Oracle ℕ Bool) → Type
_≤wtt_ χ χ' = (n : ℕ) → Σ[ m ∈ ℕ ] (((k : Fin m) → χ' (fst k) ↓) → χ n ↓)


{- Weak truth reducibility implies Turing -}
wtt→T' : {A : Type ℓa} {B : Type ℓb} {A' : Type ℓa'} {B' : Type ℓb'} (sepB : Separated B)
  (χ : Oracle A B) (χ' : Oracle A' B') → χ ≤wtt' χ' → χ ≤T χ'
_≤T_.red (wtt→T' sepB χ χ' wtt) n = do
  z ← nullList (oDefd χ') (λ m → χ' m ↓) (fst (wtt n)) (all→allList (λ m → ◯⟨ χ' ⟩ (χ' m ↓)) (λ m → query χ' m) (fst (wtt n)))
  ∣ snd (wtt n) z ∣

wtt→T : (χ χ' : Oracle ℕ Bool) → χ ≤wtt χ' → χ ≤T χ'
_≤T_.red (wtt→T χ χ' wtt) n = do
  m ← computeHead χ' (fst (wtt n))
  ∣ snd (wtt n) m ∣

range : (n : ℕ) → List ℕ
range zero = []
range (suc n) = n ∷ range n

allRange→allFin : (X : ℕ → Type ℓ) (n : ℕ) → (allList X (range n)) → (k : Fin n) → X (fst k)
allRange→allFin X zero z k = ⊥rec (¬-<-zero (snd k))
allRange→allFin X (suc n) (checkList .n p .(range n) z) k =
  ⊎rec (λ q → allRange→allFin X n z ((fst k) , q)) (λ q → subst X (sym q) p) (<-split (snd k))

wtt→wtt' : (χ χ' : Oracle ℕ Bool) → χ ≤wtt χ' → χ ≤wtt' χ'
wtt→wtt' χ χ' wtt n = range N , λ z → f (allRange→allFin _ N z)
  where
    N = fst (wtt n)
    f = snd (wtt n)

Lmax : List ℕ → ℕ
Lmax [] = 0
Lmax (x ∷ l) = max x (Lmax l)

LmaxAllFin→allList : (X : ℕ → Type ℓ) (l : List ℕ) (g : (k : Fin (suc (Lmax l))) → X (fst k)) →
  allList X l
LmaxAllFin→allList X [] g = allNil
LmaxAllFin→allList X (x ∷ l) g =
  checkList x (g (x , ≤<-trans left-≤-max ≤-refl)) l
    (LmaxAllFin→allList X l (λ k → g ((fst k) , <≤-trans (snd k) (suc-≤-suc right-≤-max))))

wtt'→wtt : (χ χ' : Oracle ℕ Bool) → χ ≤wtt' χ' → χ ≤wtt χ'
wtt'→wtt χ χ' wtt' n = suc (Lmax l) , λ g → f (LmaxAllFin→allList _ l g)
  where
    l = fst (wtt' n)
    f = snd (wtt' n)

ℕ→Bool : ℕ → Bool
ℕ→Bool zero = false
ℕ→Bool (suc n) = true

Bool→ℕ : Bool → ℕ
Bool→ℕ false = 0
Bool→ℕ true = 1

Bool→ℕ→Bool : (b : Bool) → ℕ→Bool (Bool→ℕ b) ≡ b
Bool→ℕ→Bool false = refl
Bool→ℕ→Bool true = refl

ℕ→FB : (n : ℕ) → ℕ → ((Fin n) → Bool)
ℕ→FB zero m k = ⊥rec (¬-<-zero (snd k))
ℕ→FB (suc n) m = ℕ→Bool ∘ FN
  where
    FN = invEq (ℕTupleEquiv n) m

FB→ℕ : (n : ℕ) → ((Fin n) → Bool) → ℕ
FB→ℕ zero f = zero
FB→ℕ (suc n) f = (fst (ℕTupleEquiv n) (Bool→ℕ ∘ f))

FBℕSec : (n : ℕ) → (f : (Fin n) → Bool) → ℕ→FB n (FB→ℕ n f) ≡ f
FBℕSec zero f = funExt (λ k → ⊥rec (¬-<-zero (snd k)))
FBℕSec (suc n) f = funExt (λ k → cong ℕ→Bool (funExt⁻ (retEq (ℕTupleEquiv n) (Bool→ℕ ∘ f)) k) ∙ Bool→ℕ→Bool (f k))

codesHead : (χ : Oracle ℕ Bool) (n m : ℕ) → Type
codesHead χ n m = (k : Fin n) → χ (fst k) ↓= ℕ→FB n m k

decodeHead : (χ : Oracle ℕ Bool) (n m : ℕ) (ch : codesHead χ n m) → (k : Fin n) → χ (fst k) ↓
decodeHead χ n m ch k = (ℕ→FB n m k) , (ch k)

codesHeadStable : (χ : Oracle ℕ Bool) (n m : ℕ) → Stable (codesHead χ n m)
codesHeadStable χ n m p k = Ω¬¬-stab _ (¬¬-map (λ p' → p' k) p)

⟨_,_⟩ : ℕ → ℕ → ℕ
⟨ n , m ⟩ = fst ℕPairEquiv (n , m)

p₀ : ℕ → ℕ
p₀ nm = fst (invEq ℕPairEquiv nm)

p₁ : ℕ → ℕ
p₁ nm = snd (invEq ℕPairEquiv nm)

pβ₀ : (n m : ℕ) → (p₀ ⟨ n , m ⟩ ≡ n)
pβ₀ n m = cong fst (retEq ℕPairEquiv (n , m))

pβ₁ : (n m : ℕ) → (p₁ ⟨ n , m ⟩ ≡ m)
pβ₁ n m = cong snd (retEq ℕPairEquiv (n , m))


wttWitness : (χ χ' : Oracle ℕ Bool)  → Type
wttWitness χ χ' =
  Σ[ (e0 , e1) ∈ totalComputable × ℕ ]
    ((n m : ℕ) → codesHead χ' (evalTC e0 n) m →
      Σ[ u ∈ φ e1 ⟨ n , m ⟩ ↓ ] (χ n ↓= ℕ→Bool (∂.value (φ e1 ⟨ n , m ⟩) u)))


wttIsWitnessAt : (χ χ' : Oracle ℕ Bool) (e0 : ℕ) (e1 : ℕ) (n : ℕ) → Type
wttIsWitnessAt χ χ' e0 e1 n =
  Σ[ v ∈ φ e0 n ↓ ] ((m : ℕ) → codesHead χ' (get (φ e0 n) v) m →
    Σ[ u ∈ φ e1 ⟨ n , m ⟩ ↓ ] (χ n ↓= ℕ→Bool (get (φ e1 ⟨ n , m ⟩) u)))


wttWitness→at : (χ χ' : Oracle ℕ Bool) → (wtt : wttWitness χ χ') → (n : ℕ) →
  wttIsWitnessAt χ χ' (fst (fst (fst wtt))) (snd (fst wtt)) n
wttWitness→at χ χ' ((e0 , e1) , u) n = snd e0 n ,
  λ m ch → u n m ch

ECT2' : (dom : ℕ → ℕ → Type ℓ) → ((n₀ n₁ : ℕ) → Stable (dom n₀ n₁)) → ((n₀ n₁ : ℕ) → isProp (dom n₀ n₁)) →
  (X : ℕ → ℕ → ℕ → Type ℓ) →
  ((n₀ n₁ : ℕ) → dom n₀ n₁ → Σ[ m ∈ ℕ ] X n₀ n₁ m) →
  ∥ Σ[ e ∈ ℕ ] ((n₀ n₁ : ℕ) → dom n₀ n₁ → Σ[ u ∈ φ e ⟨ n₀ , n₁ ⟩ ↓ ] X n₀ n₁ (∂.value (φ e ⟨ n₀ , n₁ ⟩) u)) ∥₁
ECT2' dom stabDom propDom X x = do
  (e , p) ← ECT f
  ∣ e , lemma e p ∣₁
  where
    f : ℕ → ∂ ℕ
    ∂.domain (f n) = ¬¬resize (dom (p₀ n) (p₁ n))
    ∂.value (f n) u = fst (x (p₀ n) (p₁ n) (stabDom _ _ (¬¬resize-out u)))

    lemma : (e : ℕ) → ((n : ℕ) → (z : f n ↓) → φ e n ↓= get (f n) z) → (n₀ n₁ : ℕ) →
      dom n₀ n₁ → Σ[ u ∈ φ e ⟨ n₀ , n₁ ⟩ ↓ ] X n₀ n₁ (get (φ e ⟨ n₀ , n₁ ⟩) u)

    lemma e p n₀ n₁ w = φdefd , subst (X n₀ n₁) (sym q) (snd (x n₀ n₁ w))
      where
        fdefd : f ⟨ n₀ , n₁ ⟩ ↓
        fdefd = ¬¬resize-in (subst2 dom (sym (pβ₀ n₀ n₁)) (sym (pβ₁ n₀ n₁)) w)

        fdefdPath = (subst2-filler dom (sym (pβ₀ n₀ n₁)) (sym (pβ₁ n₀ n₁)) w)

        φdefd : φ e ⟨ n₀ , n₁ ⟩ ↓
        φdefd = fst (p ⟨ n₀ , n₁ ⟩ fdefd)

        q : get (φ e ⟨ n₀ , n₁ ⟩) φdefd ≡ fst (x n₀ n₁ w)
        q = snd (p ⟨ n₀ , n₁ ⟩ fdefd) ∙ (λ i → fst (x (pβ₀ n₀ n₁ i) (pβ₁ n₀ n₁ i)
          (isProp→PathP (λ i → propDom (pβ₀ n₀ n₁ i) (pβ₁ n₀ n₁ i)) (stabDom (p₀ ⟨ n₀ , n₁ ⟩) (p₁ ⟨ n₀ , n₁ ⟩) (¬¬resize-out fdefd)) w i)))


wttWitness→wtt' : (χ χ' : Oracle ℕ Bool) → wttWitness χ χ' → χ ≤wtt χ'
wttWitness→wtt' χ χ' wtt n = (evalTC e0 n) , red
  where
    e0 = fst (fst wtt)
    e1 = snd (fst wtt)

    red : (z : (k : Fin (evalTC e0 n)) → χ' (fst k) ↓) → χ n ↓
    red z = ℕ→Bool (∂.value (φ e1 ⟨ n , m ⟩) (fst l)) , snd l
      where
        m = FB→ℕ (evalTC e0 n) λ k → fst (z k)
        p = (FBℕSec (evalTC e0 n) λ k → fst (z k))
        l = snd wtt n m (λ k → subst (λ u → χ' (fst k) ↓= u) (sym (funExt⁻ p k)) (snd (z k)))



wtt→wttWitness : (χ χ' : Oracle ℕ Bool) → χ ≤wtt χ' → ∥ wttWitness χ χ' ∥₁
wtt→wttWitness χ χ' wtt = do
  (e0 , z) ← CT' (λ n m → (((k : Fin m) → χ' (fst k) ↓) → χ n ↓)) wtt
  (e1 , w) ← ECT2' (λ n m → codesHead χ' (evalTC e0 n) m) (λ _ _ → codesHeadStable χ' _ _) (λ _ _ → isPropΠ (λ _ → Ω¬¬-props _))
    (λ n m l → χ n ↓= ℕ→Bool l) λ n m u → (Bool→ℕ (fst (z n (decodeHead χ' (evalTC e0 n) m u)))) ,
    subst (λ v → χ n ↓= v) (sym (Bool→ℕ→Bool _)) (snd (z n (decodeHead χ' (evalTC e0 n) m u)))
  ∣ (e0 , e1) , w ∣₁

κ : ℕ → ∇ Bool
κ en = byCases (φ (p₀ en) (p₁ en) ↓) true false

decodeκ : (e n : ℕ) → (κ ⟨ e , n ⟩ ↓) → Dec (φ e n ↓)
decodeκ e n (false , z) = no (λ w → ∇.well-defd (κ ⟨ e , n ⟩) false true z (byCasesβ⊤ _ _ _ (subst2 (λ e n → φ e n ↓) (sym (pβ₀ e n)) (sym (pβ₁ e n)) w)) false≢true)
decodeκ e n (true , z) = yes (¬¬resize-in-from¬¬
  (λ w → ∇.well-defd (κ ⟨ e , n ⟩) false true
                     (byCasesβ⊥ _ _ _ λ u → ¬¬resize-out u (λ v → w (subst2 φ-domain (pβ₀ e n) (pβ₁ e n) v))) z false≢true))

decideHaltingProb : (e n : ℕ) → ◯⟨ κ ⟩ (Dec (φ e n ↓))
decideHaltingProb e n = do
  z ← query κ ⟨ e , n ⟩
  ∣ decodeκ e n z ∣


diagWTT : (n : ℕ) →
  ◯⟨ κ ⟩ (Σ[ b ∈ Bool ]  ((χ : Oracle ℕ Bool) → (χ n ↓= b) → ¬ wttIsWitnessAt χ κ (p₀ n) (p₁ n) n))
diagWTT n = do
  let e0 = p₀ n
  let e1 = p₁ n
  yes u ← decideHaltingProb e0 n
    where no u → ∣ false , (λ _ _ v → u (fst v)) ∣
  let requests = get (φ e0 n) u
  hd ← computeHead κ requests
  let m = FB→ℕ _ ((λ k → fst (hd k)))
  yes w ← decideHaltingProb e1 ⟨ n , m ⟩
    where no w → ∣ false ,
             (λ _ _ v → w (fst (snd v m (subst ((λ u' →
               codesHead κ (get (φ e0 n) u') m)) (Ω¬¬-props _ u (fst v)) (subst (λ s → (((k : Fin (get (φ (p₀ n) n) u)) →
                                        κ (fst k) ↓= s k))) (sym (FBℕSec (get (φ (p₀ n) n) u) λ k → fst (hd k))) λ k → snd (hd k)))))) ∣
  let nb = ℕ→Bool (get (φ e1 ⟨ n , m ⟩) w)
  ∣ (not nb) ,
    (λ χ p v → ∇.well-defd (χ n) _ _ p
      (snd (snd v m (subst (λ u' → codesHead κ (get (φ e0 n) u') m) (Ω¬¬-props _ u (fst v))
        (subst (λ s → ((((k : Fin (get (φ e0 n) u)) → κ (fst k) ↓= s k)))) (sym (FBℕSec (get (φ e0 n) u) λ k → fst (hd k))) ((λ k → snd (hd k)))))))
        λ q → not≢const nb (q ∙ cong ℕ→Bool (cong (get (φ e1 ⟨ n , m ⟩))
              (Ω¬¬-props _ _ _)))) ∣

private
  convertζ : (n : ℕ) → ◯⟨ κ ⟩ (Σ[ b ∈ Bool ]  ((χ : Oracle ℕ Bool) → (χ n ↓= b) → ¬ wttIsWitnessAt χ κ (p₀ n) (p₁ n) n)) → Σ[ b ∈ ∇ Bool ] ((χ : Oracle ℕ Bool) → (χ n ≡ b) → ¬ wttIsWitnessAt χ κ (p₀ n) (p₁ n) n)
  convertζ n = nullRec (¬¬Sheaf→Null {χ = κ} separatedBool (isNullΣ ∇isSheaf (λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNull⊥ _ (snd ∘ snd)))))))
    (λ (b , u) → (∇-in b) , (λ χ p z → u χ (subst (λ w → [ ∇.is-this w b ]) (sym p) (ιIs b)) z))

ζwithProof : (n : ℕ) → Σ[ b ∈ ∇ Bool ] ((χ : Oracle ℕ Bool) → (χ n ≡ b) → ¬ wttIsWitnessAt χ κ (p₀ n) (p₁ n) n)
ζwithProof n = convertζ n (diagWTT n)

ζ : Oracle ℕ Bool
ζ = fst ∘ ζwithProof

notWTT : ¬ (ζ ≤wtt κ)
notWTT wtt = rec isProp⊥ (λ x → x) do
  ((e0 , e1) , z) ← wtt→wttWitness ζ κ wtt
  let wttat = wttWitness→at ζ κ ((e0 , e1) , z) ⟨ fst e0 , e1 ⟩
  let d = snd (ζwithProof ⟨ fst e0 , e1 ⟩)
  ∣ d ζ refl (subst2 (λ e0' e1' → wttIsWitnessAt ζ κ e0' e1' ⟨ fst e0 , e1 ⟩) (sym (pβ₀ (fst e0) e1)) (sym (pβ₁ (fst e0) e1)) wttat) ∣₁

isTuring : ζ ≤T κ
_≤T_.red isTuring n = do
  ((b , _) , p) ← evalWithPath κ (diagWTT n)
  ∣ b , subst (λ s → fst (convertζ n s) ↓= b) (sym p) (ιIs b) ∣
