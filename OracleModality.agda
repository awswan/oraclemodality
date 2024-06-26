module OracleModality where

open import Includes

open import Util.Everything
open import Util.LexNull
open import Util.Nullification

open import Cubical.Modalities.Modality

open import Util.HasUnderlyingType
open import Util.PartialElements
open import Axioms.NegativeResizing
open import Axioms.MarkovInduction
open import DoubleNegationSheaves

Oracle : (A : Type ℓa) (B : Type ℓb) → Type (ℓ-max ℓa ℓb)
Oracle A B = A → ∇ B

oDefd : (χ : Oracle A B) → A → Type _ -- NB: χ is the Greek letter \chi
oDefd χ a = χ a ↓

module OM (χ : Oracle A B) {ℓ : Level} where
  {- Nullification is in particular a modality -}
  open Modality (NullModality {ℓ = ℓ} (oDefd χ)) public

{- Definition of oracle modality -}
◯[_] : {A : Type ℓa} {B : Type ℓb} (χ : Oracle A B) {ℓ : Level} →
       Type ℓ → Type (ℓ-max ℓ (ℓ-max ℓa ℓb))
◯[ χ ] {ℓ = ℓ} = Null (oDefd χ)
  where
    open OM χ {ℓ = ℓ}


module _ (χ : Oracle A B) where
  open OM χ

  private
    _is_ = ∇.is-this {A = ℕ}
    mp-inst : ∇ ℕ → Type _
    mp-inst N = ((n : ℕ) → ◯[ χ ] (Dec ⟨ N is n ⟩)) → ◯[ χ ] (N ↓)

  -- Key lemma for relativised Markov's principle. See first part of proof of Theorem 5.5
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
          convert-dec : (¬p : ¬ ⟨ N is 0 ⟩) (n : ℕ) → ◯[ χ ] (Dec ⟨ (Pred.M N ¬p) is n ⟩)
          convert-dec ¬p n = do
            yes p ← dec (suc n)
              where no ¬p' → ∣ no (λ z → ¬p' (Pred.is-suc N ¬p n z)) ∣
            ∣ yes (invert-suc-of {N = N} {M = Pred.M N ¬p} (Pred.is-suc N ¬p) n p) ∣

  -- We first show relativised Markov's principle for the special case where X n is true exactly once
  search-unique : (X : ℕ → Type ℓ) (is-unique : (n m : ℕ) → (X n) → (X m) → n ≡ m)
    (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) → ◯[ χ ] (Dec (X n))) → ◯[ χ ] (Σ ℕ X)
  search-unique X is-unique exists dec = do
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

      dec' : (n : ℕ) → ◯[ χ ] (Dec ⟨ ∇.is-this N n ⟩)
      dec' n = do
        (no ¬p) ← dec n
          where (yes p) → ∣ yes (¬¬resize-in p) ∣
        ∣ no (λ w → ¬¬resize-out w ¬p) ∣

  {- We derive the full version of relativised Markov's principle by finding the first n such that
     X(n), which is unique. -}
  search-first : (X : ℕ → Type ℓ) (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) →
                    ◯[ χ ] (Dec (X n))) → ◯[ χ ] (Σ ℕ (λ n → X n × ((m : ℕ) → m < n → ¬ (X m))))
  search-first X exists dec = search-unique X' unique (λ w → exists (λ (n , v) → convert-ex w n v)) dec'
    where
      X' : ℕ → Type _
      X' n = X n × ((m : ℕ) → m < n → ¬ (X m)) -- n is the first witness for X

      convert-ex : ¬ (Σ ℕ X') → (n : ℕ) → ¬ (X n)
      convert-ex z = WFI.induction <-wellfounded λ n w v → z (n , (v , w))

      unique : (n m : ℕ) → (X' n) → (X' m) → n ≡ m
      unique m n x y with (m ≟ n)
      ... | lt p = ⊥rec (snd y m p (fst x))
      ... | eq p = p
      ... | gt p = ⊥rec (snd x n p (fst y))

      scan : (n : ℕ) → ◯[ χ ](((m : ℕ) → m < n → ¬ (X m)) ⊎ Σ ℕ λ k → (k < n) × (X' k))
      scan zero = ∣ inl (λ m p _ → ¬-<-zero p) ∣
      scan (suc n) = do
        inl z ← scan n -- has the first witness already occured for m < n?
          where inr (m , (p , z)) → ∣ inr (m , (<-trans p ≤-refl) , z) ∣ -- already found the least witness
        no ¬xn ← dec n -- check if n is a witness
          where yes xn → ∣ inr (n , (≤-refl , (xn , z))) ∣ -- first witness appears here
        ∣ inl (λ m p → ⊎rec (z m) (λ q → subst _ (sym q) ¬xn) (<-split p)) ∣ -- otherwise return proof there's no witness so far

      dec' : (n : ℕ) → ◯[ χ ] (Dec (X' n))
      dec' n = do
        inr (m , (p , z)) ← scan (suc n)
          where inl z → ∣ no (λ w → z n ≤-refl (fst w) ) ∣
        ⊎rec (λ q → ∣ no (λ {(_ , w) → w m q (fst z)}) ∣)
             (λ q → ∣ yes (subst X' q z) ∣) (<-split p)

  {- We usually don't need to know that the element selected is the first one, so it's useful
     to have a function that just calls search-first and forgets that the witness is first. -}
  search : (X : ℕ → Type ℓ) (exists : ¬ ¬ (Σ ℕ X)) → (dec : (n : ℕ) →
                    ◯[ χ ] (Dec (X n))) → ◯[ χ ] (Σ ℕ X)
  search X exists dec = do
    (n , (x , _)) ← search-first X exists dec
    ∣ n , x ∣

  query : (a : A) → ◯[ χ ](χ a ↓)
  query a = hub a (λ z → ∣ z ∣)

  evalWithPath : (x : ◯[ χ ] X) → ◯[ χ ] (Σ[ x' ∈ X ] (x ≡ ∣ x' ∣))
  evalWithPath = nullElim (λ _ → isNull-Null _) λ x → ∣ x , refl ∣

  extract⊥ : ◯[ χ ] ⊥ → ⊥
  extract⊥ = nullRec (isNull⊥ (oDefd χ) λ a → ∇.almost-inh (χ a)) (λ x → x)

variable
  χ χ' χ'' : Oracle A B

¬¬Sheaf→Null : {A : Type ℓ} {B : Type ℓ'} {X : Type ℓ''} {χ : Oracle A B} → (Separated B) → (¬¬Sheaf X) → isNull (oDefd χ) X
¬¬Sheaf→Null {A = A} {X = X} {χ = χ} Bsep Xsh a = Xsh ((χ a ↓) , (∇defd-prop Bsep (χ a)) , ∇.almost-inh (χ a))

{- Erase all the computational information to get an element of ∇ X -}
erase : (χ : Oracle A B) → (Separated B) → ◯[ χ ] X → ∇ X
erase χ Bsep = nullRec (¬¬Sheaf→Null {χ = χ} Bsep ∇isSheaf) ∇-in

◯→¬¬ : (χ : Oracle A B) → (Separated B) → ◯[ χ ] X → ¬ ¬ X
◯→¬¬ χ Bsep z = ∇→¬¬ (erase χ Bsep z)

recallErase : (χ : Oracle A B) → (sB : Separated B) → {X : Type ℓ} → (x : ◯[ χ ] X) → ◯[ χ ](erase χ sB x ↓)
recallErase χ sB = nullElim (λ x → isNull-Null (λ a → χ a ↓)) λ x → ∣ x , (¬¬resize-in refl) ∣

eraseInj : (χ : Oracle A B) → (sB : Separated B) (sX : Separated X) → {w z : ◯[ χ ] X} → (erase χ sB w ≡ erase χ sB z) → (w ≡ z)
eraseInj {X = X} χ sB sX {w} {z} =
  nullElim {Y = λ w → (z : ◯[ χ ] X) → erase χ sB w ≡ erase χ sB z → w ≡ z}
    (λ w → isNullΠ (λ _ → isNullΠ (λ p → isNull≡ (isNull-Null (oDefd χ)))))
    (λ w₀ → nullElim (λ z → isNullΠ (λ _ → isNull≡ (isNull-Null (oDefd χ)))) (λ z₀ p → cong ∣_∣ (sX _ _ (∇-in-inj p)))) w z

variable
  A' B' : Type ℓ'

-- Definition of Turing reducibility
-- Making this a record type encourages agda to keep hold of χ and χ' when type checking
record _≤T_ {A : Type ℓa} {B : Type ℓb} {A' : Type ℓa'} {B' : Type ℓb'}
            (χ : Oracle A B) (χ' : Oracle A' B') : Type (ℓ-max (ℓ-max ℓa ℓb) (ℓ-max ℓa' ℓb')) where
  constructor Tred
  field
    red : (a : A) → ◯[ χ' ](χ a ↓)

TReducible→isNull : {B : Type ℓ} {χ : Oracle A B} {χ' : Oracle A' B'} (sB : Separated B)
  → χ ≤T χ' → (isNull (λ a → χ a ↓) (◯[ χ' ] X))
TReducible→isNull {X = X} {χ = χ} {χ' = χ'} sB (Tred e) a  = fromIsEquiv _ (snd equiv)
  where
    ic : isContr (◯[ χ' ] (χ a ↓))
    ic = inhProp→isContr (e a) (NullPreservesProp (∇defd-prop sB (χ a)))
  
    equiv : ◯[ χ' ] X ≃ (χ a ↓ → ◯[ χ' ] X)
    equiv =
      ◯[ χ' ] X
        ≃⟨ invEquiv (UnitToType≃ _) ⟩
      (Unit → ◯[ χ' ] X)
        ≃⟨ preCompEquiv (isContr→≃Unit ic) ⟩
      (◯[ χ' ]( χ a ↓) → ◯[ χ' ] X)
        ≃⟨ NullRecEquiv (isNull-Null _) ⟩
      (χ a ↓ → ◯[ χ' ] X)
        ■

{- Turing equivalence -}
_≡T_ : (χ : Oracle A B) (χ' : Oracle A' B') → Type _
χ ≡T χ' = (χ ≤T χ') × (χ' ≤T χ)

{- Reflexivity of Turing degrees -}
Trefl : (χ : Oracle A B) → χ ≤T χ
Trefl χ = Tred (query χ)

simulate : {χ : Oracle A B} (sB : Separated B) → χ ≤T χ' → ◯[ χ ] X → ◯[ χ' ] X
simulate sB e = nullRec (TReducible→isNull sB e) ∣_∣

{- Transitivity of Turing degrees -}
≤TTrans : {χ' : Oracle A' B'} (sB : Separated B') →
          χ ≤T χ' → χ' ≤T χ'' → χ ≤T χ''
≤TTrans sB (Tred e) f = Tred (λ a → simulate sB f (e a))

{- Compute a function from its graph. Theorem 5.13 in paper. -}
module _ (χ : ℕ × ℕ → ∇ Bool) (uniq : (a : ℕ) → (b b' : ℕ) → ⟨ χ (a , b) ⟩ → ⟨ χ (a , b') ⟩ → ¬ ¬ b ≡ b')
  (defd : (a : ℕ) → ¬ ¬ (Σ[ b ∈ ℕ ] ⟨ χ (a , b) ⟩)) where

  graphToFn : ℕ → ∇ ℕ
  
  ∇.is-this (graphToFn a) b = ∇.is-this (χ (a , b)) true
  ∇.well-defd (graphToFn a) b b' u v = uniq a b b' u v
  ∇.almost-inh (graphToFn a) = defd a


  graphToFn≤T : graphToFn ≤T χ
  graphToFn≤T = Tred λ a → search χ (λ b → ⟨ χ (a , b) ⟩) (defd a) (dec a)
    where
      dec : (a : ℕ) → (b : ℕ) → ◯[ χ ] (Dec ⟨ χ (a , b) ⟩)
      dec a b = do
        (false , z) ← query χ (a , b)
          where (true , z) → ∣ yes z ∣
        ∣ no (λ w → ∇.well-defd (χ (a , b)) false true z w false≢true) ∣

{- Compute inverse of a surjective function. Variant of Theorem 5.14 from paper. -}
module invert (χ : ℕ → ∇ ℕ) (surj : (m : ℕ) → ¬ ¬ (Σ[ n ∈ ℕ ] ⟨ ∇.is-this (χ n) m ⟩)) where
  compute-inverse : (n : ℕ) → ◯[ χ ] (Σ[ m ∈ ℕ ] ⟨ ∇.is-this (χ m) n ⟩)
  compute-inverse n = search χ (λ m → ⟨ ∇.is-this (χ m) n ⟩) (surj n) (dec n)
    where
      dec : (m n : ℕ) → ◯[ χ ] (Dec ⟨ ∇.is-this (χ n) m ⟩)
      dec m n = do
        (k , z) ← query χ n
        ∣ decRec (λ p → yes (subst _ p z))
                 (λ np → no (λ w → np (separatedℕ _ _
                            (∇.well-defd (χ n) k m z w)))) (discreteℕ k m) ∣
  inverse : ℕ → ∇ ℕ
  inverse n = erase χ separatedℕ (OM.◯-map χ fst (compute-inverse n))

  inverse≤T : inverse ≤T χ
  _≤T_.red (inverse≤T) n = recallErase χ separatedℕ (OM.◯-map χ fst (compute-inverse n))

{- Many-one reducibility implies Turing reducibility -}
manyOne→≤T : {C : Type ℓ} (χ : Oracle A B) → (f : C → A) → ((χ ∘ f) ≤T χ)
manyOne→≤T χ f = Tred λ c → query χ (f c)

{- ◯[ χ ] X is separated whenever B and X are -}
separated◯[] : (χ : Oracle A B) → (Separated B) → (Separated X) → (Separated (◯[ χ ] X))
separated◯[] χ sepB sepX = separatedNull (λ a → (χ a ↓) , (∇defd-prop sepB (χ a))) (λ a → ◯→¬¬ χ sepB (query χ a)) sepX

map[_] : (χ : Oracle A B) {X : Type ℓ} {Y : Type ℓ'} → (g : X → Y) → ◯[ χ ] X → ◯[ χ ] Y
map[ χ ] g ∣ x ∣ = ∣ g x ∣
map[ χ ] g (hub α f) = hub α λ z → map[ χ ] g (f z)
map[ χ ] g (spoke α f s i) = spoke α (λ z → map[ χ ] g (f z)) s i
map[ χ ] g (≡hub p i) = ≡hub (λ z i → map[ χ ] g (p z i)) i
map[ χ ] g (≡spoke p s i i₁) = ≡spoke (λ z i → map[ χ ] g (p z i)) s i i₁
