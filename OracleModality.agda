module OracleModality where


open import Includes

open import Util.Everything


open import Cubical.Relation.Nullary
open import Cubical.Induction.WellFounded


open import Cubical.HITs.Nullification renaming (rec to Null-rec ; elim to Null-elim)

open import Cubical.Modalities.Modality

open import Util.HasUnderlyingType
open import PartialElements
open import Axioms.NegativeResizing
open import Axioms.MarkovInduction
open import DoubleNegationSheaves

variable
  ℓa ℓb ℓa' ℓb' : Level

-- TODO: See if making this a record lets us make more variables implicit
Oracle : (A : Type ℓa) (B : Type ℓb) → Type (ℓ-max ℓa ℓb)
Oracle A B = A → ∇ B

oDefd : (χ : Oracle A B) → A → Type _
oDefd χ a = χ a ↓

module OM (χ : Oracle A B) {ℓ : Level} where
  domain : A → Type _ -- TODO: delete
  domain a = χ a ↓

  open Modality (NullModality {ℓ = ℓ} domain) public

◯⟨_⟩ : {A : Type ℓa} {B : Type ℓb} (χ : Oracle A B) {ℓ : Level} →
       Type ℓ → Type (ℓ-max ℓ (ℓ-max ℓa ℓb))
◯⟨ χ ⟩ {ℓ = ℓ} = Null domain
  where
    open OM χ {ℓ = ℓ}

instance
  open ModalOperator
  Null-bind : ∀ {A : Type ℓa} {S : A → Type ℓb} {ℓc ℓd : Level} →
              ModalOperator (ℓ-max ℓa ℓb) ℓc ℓd (Null S)
  bind (Null-bind {S = S}) a g = Null-rec (isNull-Null S) g a
    -- Nullification.rec is more flexible than ◯-rec in allowing differing universe levels

◯⟨⟩≡-in : (χ : Oracle A B) → {a b : ◯⟨ χ ⟩ X} → (◯⟨ χ ⟩ (a ≡ b)) → a ≡ b
◯⟨⟩≡-in χ = nullRec (isNull≡ (isNull-Null _)) (λ x → x)

module _ (χ : Oracle A B) where
  open OM χ

  private
    _is_ = ∇.is-this {A = ℕ}
    mp-inst : ∇ ℕ → Type _
    mp-inst N = ((n : ℕ) → ◯⟨ χ ⟩ (Dec ⟨ N is n ⟩)) → ◯⟨ χ ⟩ (N ↓)

  rel-markov : (N : ∇ ℕ) → mp-inst N
  rel-markov = markov-ind mp-inst step
    where
      step : (N : ∇ ℕ) →
             ((M : ∇ ℕ) → N is-suc-of M → mp-inst M) → mp-inst N

      step N ih dec = do
        (no ¬p) ← dec 0
          where yes p → ∣ (0 , p) ∣
        n₀ ← ih (Pred.M N ¬p) (Pred.is-suc N ¬p) (convert-dec ¬p)
        ∣ ((suc (fst n₀)) , snd n₀) ∣
        where
          convert-dec : (¬p : ¬ ⟨ N is 0 ⟩) (n : ℕ) → ◯⟨ χ ⟩ (Dec ⟨ (Pred.M N ¬p) is n ⟩)
          convert-dec ¬p n = do
            yes p ← dec (suc n)
              where no ¬p' → ∣ no (λ z → ¬p' (Pred.is-suc N ¬p n z)) ∣
            ∣ yes (invert-suc-of {N = N} {M = Pred.M N ¬p} (Pred.is-suc N ¬p) n p) ∣

  locate-unique : (X : ℕ → Type ℓ) (is-unique : (n m : ℕ) → (X n) → (X m) → n ≡ m)
    (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) → ◯⟨ χ ⟩ (Dec (X n))) → ◯⟨ χ ⟩ (Σ ℕ X)
  locate-unique X is-unique exists dec = do
    (n , z) ← rel-markov N dec'
    yes p ← dec n
      where (no ¬p) → ⊥rec (¬¬resize-out z ¬p)
    ∣ n , p ∣
    where
      N : ∇ ℕ
      ∇.is-this N n = ¬¬resize (X n)
      ∇.well-defd N n m x y = do
        x' ← ¬¬resize-out x
        y' ← ¬¬resize-out y
        ¬¬-in (is-unique n m x' y')
      ∇.almost-inh N = ¬¬-map (λ {(n , x) → (n , ¬¬resize-in x)}) exists

      dec' : (n : ℕ) → ◯⟨ χ ⟩ (Dec ⟨ ∇.is-this N n ⟩)
      dec' n = do
        (no ¬p) ← dec n
          where (yes p) → ∣ yes (¬¬resize-in p) ∣
        ∣ no (λ w → ¬¬resize-out w ¬p) ∣

  locate-first : (X : ℕ → Type ℓ) (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) →
                    ◯⟨ χ ⟩ (Dec (X n))) → ◯⟨ χ ⟩ (Σ ℕ (λ n → X n × ((m : ℕ) → m < n → ¬ (X m))))
  locate-first X exists dec = locate-unique X' unique (λ w → exists (λ (n , v) → convert-ex w n v)) dec'
    where
      X' : ℕ → Type _ -- TODO: Simplify using functions from MarkovInduction
      X' n = X n × ((m : ℕ) → m < n → ¬ (X m)) -- n is the first witness for X

      convert-ex : ¬ (Σ ℕ X') → (n : ℕ) → ¬ (X n)
      convert-ex z = WFI.induction <-wellfounded λ n w v → z (n , (v , w))

      unique : (n m : ℕ) → (X' n) → (X' m) → n ≡ m
      unique m n x y with (m ≟ n)
      ... | lt p = ⊥rec (snd y m p (fst x))
      ... | eq p = p
      ... | gt p = ⊥rec (snd x n p (fst y))

      scan : (n : ℕ) → ◯⟨ χ ⟩(((m : ℕ) → m < n → ¬ (X m)) ⊎ Σ ℕ λ k → (k < n) × (X' k))
      scan zero = ∣ inl (λ m p _ → ¬-<-zero p) ∣
      scan (suc n) = do
        inl z ← scan n -- has the first witness already occured for m < n?
          where inr (m , (p , z)) → ∣ inr (m , (<-trans p ≤-refl) , z) ∣ -- already found the least witness
        no ¬xn ← dec n -- check if n is a witness
          where yes xn → ∣ inr (n , (≤-refl , (xn , z))) ∣ -- first witness appears here
        ∣ inl (λ m p → ⊎rec (z m) (λ q → subst _ (sym q) ¬xn) (<-split p)) ∣ -- otherwise return proof there's no witness so far

      dec' : (n : ℕ) → ◯⟨ χ ⟩ (Dec (X' n))
      dec' n = do
        inr (m , (p , z)) ← scan (suc n)
          where inl z → ∣ no (λ w → z n ≤-refl (fst w) ) ∣
        ⊎rec (λ q → ∣ no (λ {(_ , w) → w m q (fst z)}) ∣)
             (λ q → ∣ yes (subst X' q z) ∣) (<-split p)

  locate : (X : ℕ → Type ℓ) (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) →
                    ◯⟨ χ ⟩ (Dec (X n))) → ◯⟨ χ ⟩ (Σ ℕ X)
  locate X exists dec = do
    (n , (x , _)) ← locate-first X exists dec
    ∣ n , x ∣

  query : (a : A) → ◯⟨ χ ⟩(χ a ↓)
  query a = hub a (λ z → ∣ z ∣)

  evalWithPath : (x : ◯⟨ χ ⟩ X) → ◯⟨ χ ⟩ (Σ[ x' ∈ X ] (x ≡ ∣ x' ∣))
  evalWithPath = nullElim (λ _ → isNull-Null _) λ x → ∣ x , refl ∣

  isNull⊥ : isNull (oDefd χ) ⊥
  isPathSplitEquiv.sec (isNull⊥ a) = (∇.almost-inh (χ a)) , (λ b → funExt (λ _ → isProp⊥ _ _))

  extract⊥ : ◯⟨ χ ⟩ ⊥ → ⊥
  extract⊥ = nullRec isNull⊥ (λ x → x)

search-fibre : (χ : ℕ → ∇ ℕ) (m : ℕ) → ¬ ¬ (Σ ℕ (λ n → ⟨ ∇.is-this (χ n) m ⟩)) →
  ◯⟨ χ ⟩ (Σ ℕ (λ n → ⟨ ∇.is-this (χ n) m ⟩))

search-fibre χ m z = locate χ _ z λ n → do
  z ← query χ n
  ∣ dec' n z ∣
  where
    dec' : (n : ℕ) → ((χ n) ↓) → Dec ⟨ ∇.is-this (χ n) m ⟩
    dec' n (χn , w) with discreteℕ χn m
    ... | yes p = yes (subst _ p w)
    ... | no ¬p = no (λ v → ∇.well-defd (χ n) χn m w v ¬p)


variable
  χ χ' χ'' : Oracle A B

¬¬Sheaf→Null : {A : Type ℓ} {B : Type ℓ'} {X : Type ℓ''} {χ : Oracle A B} → (Separated B) → (¬¬Sheaf X) → isNull (λ a → (χ a) ↓) X
¬¬Sheaf→Null {A = A} {X = X} {χ = χ} Bsep Xsh a = fromIsEquiv const (record { equiv-proof = λ f → isOfHLevelRetractFromIso 0 (fibequiv f) (Xsh (P a) (∇.almost-inh (χ a)) f) })
  where
    P : (a : A) → hProp _
    P a = (χ a ↓) , ∇defd-prop Bsep (χ a)
    
    fibequiv : (f : χ a ↓ → X) → Iso (fiber const f) (Σ[ x ∈ X ] ((z : ⟨ P a ⟩) → f z ≡ x))
    Iso.fun (fibequiv f) (x , u) = x , λ z i → u (~ i) z
    Iso.inv (fibequiv f) (x , p) = x , funExt (λ z → sym (p z))
    Iso.rightInv (fibequiv f) (x , p) = refl
    Iso.leftInv (fibequiv f) (x , u) = refl

strip : (χ : Oracle A B) → (Separated B) → ◯⟨ χ ⟩ X → ∇ X
strip χ Bsep = Null-rec (¬¬Sheaf→Null {χ = χ} Bsep ∇-isSheaf) ∇-in

◯→¬¬ : (χ : Oracle A B) → (Separated B) → ◯⟨ χ ⟩ X → ¬ ¬ X
◯→¬¬ χ Bsep z = ∇→¬¬ (strip χ Bsep z)

recallStrip : (χ : Oracle A B) → (sB : Separated B) → {X : Type ℓ} → (x : ◯⟨ χ ⟩ X) → ◯⟨ χ ⟩(strip χ sB x ↓)
recallStrip χ sB = Null-elim (λ x → isNull-Null (λ a → χ a ↓)) λ x → ∣ x , (¬¬resize-in refl) ∣

variable
  A' B' : Type ℓ'

-- Making this a record type encourages agda to keep hold of χ and χ' when type checking
record _≤T_ {A : Type ℓa} {B : Type ℓb} {A' : Type ℓa'} {B' : Type ℓb'}
            (χ : Oracle A B) (χ' : Oracle A' B') : Type (ℓ-max (ℓ-max ℓa ℓb) (ℓ-max ℓa' ℓb')) where
  constructor Tred
  field
    red : (a : A) → ◯⟨ χ' ⟩(χ a ↓)

TReducible→isNull : {B : Type ℓ} {χ : Oracle A B} {χ' : Oracle A' B'} (sB : Separated B)
  → χ ≤T χ' → (isNull (λ a → χ a ↓) (◯⟨ χ' ⟩ X))
TReducible→isNull {X = X} {χ = χ} {χ' = χ'} sB (Tred e) a  = fromIsEquiv _ (snd equiv)
  where
    ic : isContr (◯⟨ χ' ⟩ (χ a ↓))
    ic = inhProp→isContr (e a) (NullPreservesProp (∇defd-prop sB (χ a)))
  
    equiv : ◯⟨ χ' ⟩ X ≃ (χ a ↓ → ◯⟨ χ' ⟩ X)
    equiv =
      ◯⟨ χ' ⟩ X
        ≃⟨ invEquiv (UnitToType≃ _) ⟩
      (Unit → ◯⟨ χ' ⟩ X)
        ≃⟨ preCompEquiv (isContr→≃Unit ic) ⟩
      (◯⟨ χ' ⟩( χ a ↓) → ◯⟨ χ' ⟩ X)
        ≃⟨ NullRecEquiv (isNull-Null _) ⟩
      (χ a ↓ → ◯⟨ χ' ⟩ X)
        ■

_≡T_ : (χ : Oracle A B) (χ' : Oracle A' B') → Type _
χ ≡T χ' = (χ ≤T χ') × (χ' ≤T χ)

Trefl : (χ : Oracle A B) → χ ≤T χ
Trefl χ = Tred (query χ)

simulate : {χ : Oracle A B} (sB : Separated B) → χ ≤T χ' → ◯⟨ χ ⟩ X → ◯⟨ χ' ⟩ X
simulate sB e = Null-rec (TReducible→isNull sB e) ∣_∣

≤TTrans : {χ' : Oracle A' B'} (sB : Separated B') →
          χ ≤T χ' → χ' ≤T χ'' → χ ≤T χ''
≤TTrans sB (Tred e) f = Tred (λ a → simulate sB f (e a))

module _ (χ : ℕ × ℕ → ∇ Bool) (uniq : (a : ℕ) → (b b' : ℕ) → ⟨ χ (a , b) ⟩ → ⟨ χ (a , b') ⟩ → ¬ ¬ b ≡ b')
  (defd : (a : ℕ) → ¬ ¬ (Σ[ b ∈ ℕ ] ⟨ χ (a , b) ⟩)) where

  graphToFn : ℕ → ∇ ℕ
  
  ∇.is-this (graphToFn a) b = ∇.is-this (χ (a , b)) true
  ∇.well-defd (graphToFn a) b b' u v = uniq a b b' u v
  ∇.almost-inh (graphToFn a) = defd a


  graphToFn≤T : graphToFn ≤T χ
  graphToFn≤T = Tred λ a → locate χ (λ b → ⟨ χ (a , b) ⟩) (defd a) (dec a)
    where
      dec : (a : ℕ) → (b : ℕ) → ◯⟨ χ ⟩ (Dec ⟨ χ (a , b) ⟩)
      dec a b = do
        (false , z) ← query χ (a , b)
          where (true , z) → ∣ yes z ∣
        ∣ no (λ w → ∇.well-defd (χ (a , b)) false true z w false≢true) ∣

module invert (χ : ℕ → ∇ ℕ) (inj : (n m : ℕ) → χ n ≡ χ m → n ≡ m) (surj : (m : ℕ) → ¬ ¬ (Σ[ n ∈ ℕ ] ⟨ ∇.is-this (χ n) m ⟩)) where
  compute-inverse : (n : ℕ) → ◯⟨ χ ⟩ (Σ[ m ∈ ℕ ] ⟨ ∇.is-this (χ m) n ⟩)
  compute-inverse n = locate χ (λ m → ⟨ ∇.is-this (χ m) n ⟩) (surj n) (dec n)
    where
      dec : (m n : ℕ) → ◯⟨ χ ⟩ (Dec ⟨ ∇.is-this (χ n) m ⟩)
      dec m n = do
        (k , z) ← query χ n
        ∣ decRec (λ p → yes (subst _ p z))
                 (λ np → no (λ w → np (separatedℕ _ _
                            (∇.well-defd (χ n) k m z w)))) (discreteℕ k m) ∣
  inverse : ℕ → ∇ ℕ
  inverse n = strip χ separatedℕ (OM.◯-map χ fst (compute-inverse n))

  inverse≤T : inverse ≤T χ
  _≤T_.red (inverse≤T) n = recallStrip χ separatedℕ (OM.◯-map χ fst (compute-inverse n))

manyOne→≤T : {C : Type ℓ} (χ : Oracle A B) → (f : C → A) → ((χ ∘ f) ≤T χ)
manyOne→≤T χ f = Tred λ c → query χ (f c)
