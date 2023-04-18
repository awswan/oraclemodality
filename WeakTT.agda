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
_≤wtt'_ {A = A} {A' = A'} χ χ' = (a : A) → ∥ Σ[ l ∈ (List A') ] (allList (λ a' → χ' a' ↓) l → χ a ↓ ) ∥₁

-- take∇ : (ℕ → ∇ A) → ℕ → ∇ (List A)
-- take∇ f zero = ∇-in []
-- take∇ f (suc n) = do
--   ih ← take∇ f n
--   next ← f n
--   ∇-in (next ∷ ih)

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
_≤T_.red (wtt→T' sepB χ χ' wtt) a =
  rec (NullPreservesProp (∇defd-prop sepB (χ a)))
      (λ (l , d) → nullList (oDefd χ') (λ a' → χ' a' ↓) l (all→allList (λ a' → ◯⟨ χ' ⟩ (χ' a' ↓)) (query χ') l) >>= (∣_∣ ∘ d)) (wtt a)

wtt→T : (χ χ' : Oracle ℕ Bool) → χ ≤wtt χ' → χ ≤T χ'
_≤T_.red (wtt→T χ χ' wtt) n = do
  m ← computeHead χ' (fst (wtt n))
  ∣ snd (wtt n) m ∣

postulate
  FinBoolCtbl : ℕ ≃ (Σ[ n ∈ ℕ ] ((Fin n) → Bool))

ℕ→FB = fst FinBoolCtbl
FB→ℕ = invEq FinBoolCtbl

-- codesHead' : (χ : Oracle ℕ Bool) (n : ℕ) (

codesHead : (χ : Oracle ℕ Bool) (n m : ℕ) → Type
codesHead χ n m =
  let
    n' = fst (ℕ→FB m)
    f = snd (ℕ→FB m)
  in
  (n' ≡ n) × ((k : Fin n') → χ (fst k) ↓= f k)

decodeHead : (χ : Oracle ℕ Bool) (n m : ℕ) (ch : codesHead χ n m) → (k : Fin n) → χ (fst k) ↓
decodeHead χ n m ch = subst (λ n → (k : Fin n) → χ (fst k) ↓) (fst ch)
  λ k → (snd (ℕ→FB m) k) , (snd ch k)

headCodeUnique : (χ : Oracle ℕ Bool) (n : ℕ) → isProp (Σ[ m ∈ ℕ ] codesHead χ n m)
headCodeUnique χ n = inh→isContr→isProp λ (m , ch) → defd→ic (decodeHead χ n m ch)
  where
    defd→ic : ((k : Fin n) → χ (fst k) ↓) → isContr (Σ[ m ∈ ℕ ] codesHead χ n m)
    defd→ic f = isOfHLevelRespectEquiv 0
      (invEquiv (Σ-cong-equiv-fst
        {B = λ s → (fst s ≡ n) × ((k : Fin (fst s)) → χ (fst k) ↓= snd s k)} FinBoolCtbl))
      (((n , (λ k → fst (f k))) , (refl , (λ k → snd (f k)))) ,
           λ ((n' , f') , (p , q)) → Σ≡Prop (λ _ → isProp× (isSetℕ _ _) (isPropΠ (λ _ → Ω¬¬-props _))) (ΣPathP ((sym p) ,
             toPathP (funExt (λ k → Discrete→Separated discreteBool _ _ (∇.well-defd (χ (fst k)) _ _ (snd (f (subst Fin p k))) (q k)))))))

codesHeadStable : (χ : Oracle ℕ Bool) (n m : ℕ) → Stable (codesHead χ n m)
codesHeadStable χ n m p = (separatedℕ _ _ (¬¬-map fst p)) ,
  λ k → Ω¬¬-stab _ (¬¬-map (λ p' → snd p' k) p)

ℕ→Bool : ℕ → Bool
ℕ→Bool zero = false
ℕ→Bool (suc n) = true

Bool→ℕ : Bool → ℕ
Bool→ℕ false = 0
Bool→ℕ true = 1

Bool→ℕ→Bool : (b : Bool) → ℕ→Bool (Bool→ℕ b) ≡ b
Bool→ℕ→Bool false = refl
Bool→ℕ→Bool true = refl

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

wttWitness→wtt : (χ χ' : Oracle ℕ Bool) → wttWitness χ χ' → χ ≤wtt χ'
wttWitness→wtt χ χ' wtt n = (evalTC e0 n) , red
  where
    e0 = fst (fst wtt)
    e1 = snd (fst wtt)

    red : (z : (k : Fin (evalTC e0 n)) → χ' (fst k) ↓) → χ n ↓
    red z = ℕ→Bool (∂.value (φ e1 ⟨ n , m ⟩) (fst l)) , snd l
      where
        m = FB→ℕ ((evalTC e0 n) , λ k → fst (z k))
        p = (secEq FinBoolCtbl ((evalTC e0 n) , λ k → fst (z k)))
        l = snd wtt n m (cong fst p , subst (λ u → (k : Fin (fst u)) → χ' (fst k) ↓= snd u k) (sym p)
                      λ k → snd (z k))


wtt→wttWitness : (χ χ' : Oracle ℕ Bool) → χ ≤wtt χ' → ∥ wttWitness χ χ' ∥₁
wtt→wttWitness χ χ' wtt = do
  (e0 , z) ← CT' (λ n m → (((k : Fin m) → χ' (fst k) ↓) → χ n ↓)) wtt
  (e1 , w) ← ECT2' (λ n m → codesHead χ' (evalTC e0 n) m) (λ _ _ → codesHeadStable χ' _ _) (λ _ _ → isPropΣ (isSetℕ _ _) λ _ → isPropΠ (λ _ → Ω¬¬-props _))
    (λ n m l → χ n ↓= ℕ→Bool l) λ n m u → (Bool→ℕ (fst (z n (decodeHead χ' (evalTC e0 n) m u)))) ,
    subst (λ v → χ n ↓= v) (sym (Bool→ℕ→Bool _)) (snd (z n (decodeHead χ' (evalTC e0 n) m u)))
  ∣ (e0 , e1) , w ∣₁

κ : ℕ × ℕ → ∇ Bool
κ (e , n) = byCases (φ e n ↓) true false

κ' : ℕ → ∇ Bool
κ' en = κ ((p₀ en) , (p₁ en))

decodeκ : (e n : ℕ) → (κ (e , n) ↓) → Dec (φ e n ↓)
decodeκ e n (false , z) = no (λ w → ∇.well-defd (κ (e , n)) false true z
  (byCasesβ⊤ (φ e n ↓) true false w) false≢true)
decodeκ e n (true , z) = yes (¬¬resize-in-from¬¬
  (λ w → ∇.well-defd (κ (e , n)) false true
    (byCasesβ⊥ (φ e n ↓) true false λ u → ¬¬-map (λ x → x) (¬¬resize-out u) w) z false≢true))

decideHaltingProb : (e n : ℕ) → ◯⟨ κ' ⟩ (Dec (φ e n ↓))
decideHaltingProb e n = do
  z ← query κ' ⟨ e , n ⟩
  ∣ decodeκ e n (subst (λ x → κ x ↓) (≡-× (pβ₀ e n) (pβ₁ e n)) z) ∣

diagWTT : (n : ℕ) →
  ◯⟨ κ' ⟩ (Σ[ b ∈ Bool ]  ((χ : Oracle ℕ Bool) → (χ n ↓= b) → ¬ wttIsWitnessAt χ κ' (p₀ n) (p₁ n) n))
diagWTT n = do
  let e0 = p₀ n
  let e1 = p₁ n
  yes u ← decideHaltingProb e0 n
    where no u → ∣ false , (λ _ _ v → u (fst v)) ∣
  let requests = get (φ e0 n) u
  hd ← computeHead κ' requests
  let m = FB→ℕ (requests , (λ k → fst (hd k)))
  yes w ← decideHaltingProb e1 ⟨ n , m ⟩
    where no w → ∣ false ,
             (λ _ _ v → w (fst (snd v m (subst (λ u' →
               codesHead κ' (get (φ e0 n) u') m)
                            (Ω¬¬-props _ u (fst v))
                            (subst (λ s → (fst s ≡ requests) × (((k : Fin (fst s)) →
                                        κ' (fst k) ↓= snd s k)))
                                   (sym (secEq FinBoolCtbl (requests , λ k → fst (hd k))))
                                   (refl , λ k → snd (hd k))))))) ∣
  let nb = ℕ→Bool (get (φ e1 ⟨ n , m ⟩) w)
  ∣ (not nb) ,
    (λ χ p v → ∇.well-defd (χ n) _ _ p
      (snd (snd v m (subst (λ u' → codesHead κ' (get (φ e0 n) u') m) (Ω¬¬-props _ u (fst v))
        (subst (λ s → (fst s ≡ requests) × ((((k : Fin (fst s)) → κ' (fst k) ↓= snd s k)))) (sym (secEq FinBoolCtbl (requests , (λ k → fst (hd k))))) (refl , (λ k → snd (hd k)))))))
        λ q → not≢const nb (q ∙ cong ℕ→Bool (cong (get (φ e1 ⟨ n , m ⟩))
              (Ω¬¬-props _ _ _)))) ∣

private
  convertζ : (n : ℕ) → ◯⟨ κ' ⟩ (Σ[ b ∈ Bool ]  ((χ : Oracle ℕ Bool) → (χ n ↓= b) → ¬ wttIsWitnessAt χ κ' (p₀ n) (p₁ n) n)) → Σ[ b ∈ ∇ Bool ] ((χ : Oracle ℕ Bool) → (χ n ≡ b) → ¬ wttIsWitnessAt χ κ' (p₀ n) (p₁ n) n)
  convertζ n = nullRec (¬¬Sheaf→Null {χ = κ'} separatedBool
          (isNullΣ ∇isSheaf λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNullΠ (λ _ → isNull⊥ _ (snd ∘ snd)))))) (λ (b , u) → (∇-in b) , (λ χ p z → u χ (subst (λ w → [ ∇.is-this w b ]) (sym p) (ιIs b)) z))

ζwithProof : (n : ℕ) → Σ[ b ∈ ∇ Bool ] ((χ : Oracle ℕ Bool) → (χ n ≡ b) → ¬ wttIsWitnessAt χ κ' (p₀ n) (p₁ n) n)
ζwithProof n = convertζ n (diagWTT n)

ζ : Oracle ℕ Bool
ζ = fst ∘ ζwithProof

noWTT : ¬ (ζ ≤wtt κ')
noWTT wtt = rec isProp⊥ (λ x → x) do
  ((e0 , e1) , z) ← wtt→wttWitness ζ κ' wtt
  let wttat = wttWitness→at ζ κ' ((e0 , e1) , z) ⟨ fst e0 , e1 ⟩
  let d = snd (ζwithProof ⟨ fst e0 , e1 ⟩)
  ∣ d ζ refl (subst2 (λ e0' e1' → wttIsWitnessAt ζ κ' e0' e1' ⟨ fst e0 , e1 ⟩) (sym (pβ₀ (fst e0) e1)) (sym (pβ₁ (fst e0) e1)) wttat) ∣₁

isTuring : ζ ≤T κ'
_≤T_.red isTuring n = do
  ((b , _) , p) ← evalWithPath κ' (diagWTT n)
  ∣ b , subst (λ s → fst (convertζ n s) ↓= b) (sym p) (ιIs b) ∣
