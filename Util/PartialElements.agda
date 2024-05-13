module Util.PartialElements where

open import Cubical.Core.Everything
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Util.HasUnderlyingType
open import Util.DoubleNegation
open import Util.ModalOperatorSugar
open import Axioms.NegativeResizing

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

record HasUnderlyingPartial (S : Type ℓ → Type ℓ') : Type (ℓ-max ℓ' (ℓ-suc (ℓ-max ℓ''' (ℓ-max ℓ'' ℓ)))) where
  field
    defined : {A : Type ℓ} → S A → Type ℓ''
    eval : {A : Type ℓ} (α : S A) → (defined α) → A
    is-this : {A : Type ℓ} → S A → A → Type ℓ'''
    isToDefined : {A : Type ℓ} → (α : S A) → (a : A) → (is-this α a) → (defined α)
    includeTotal : {A : Type ℓ} → A → S A
    totalIs : {A : Type ℓ} → (a : A) → is-this (includeTotal a) a
    
record HasUnderlyingPartialDomainFirst (S : Type ℓ → Type ℓ') : Type (ℓ-max ℓ' (ℓ-suc (ℓ-max ℓ'' ℓ))) where
  field
    domain : {A : Type ℓ} → S A → Type ℓ''
    eval : {A : Type ℓ} (α : S A) → (domain α) → A
    total : {A : Type ℓ} (a : A) → Σ[ α ∈ S A ] Σ[ d ∈ domain α ] eval α d ≡ a

record HasUnderlyingPartialValueFirst (S : Type ℓ → Type ℓ') : Type (ℓ-max ℓ' (ℓ-suc (ℓ-max ℓ'' ℓ))) where
  field
    is-this : {A : Type ℓ} → S A → A → Type ℓ''
    includeTotal : {A : Type ℓ} → A → S A
    totalIs : {A : Type ℓ} → (a : A) → is-this (includeTotal a) a


open HasUnderlyingPartial
module df = HasUnderlyingPartialDomainFirst
HasUnderlyingPartialFromDomain : {S : Type ℓ → Type ℓ'} ( hupd : HasUnderlyingPartialDomainFirst {ℓ'' = ℓ''} S) → HasUnderlyingPartial {ℓ = ℓ} {ℓ' = ℓ'} {ℓ''' = ℓ-max ℓ ℓ''} {ℓ'' = ℓ''} S 
defined (HasUnderlyingPartialFromDomain hupd) = df.domain hupd
is-this (HasUnderlyingPartialFromDomain hupd) α a = Σ[ d ∈ df.domain hupd α ] df.eval hupd α d ≡ a
eval (HasUnderlyingPartialFromDomain hupd) = df.eval hupd
isToDefined (HasUnderlyingPartialFromDomain hupd) α a = fst
includeTotal (HasUnderlyingPartialFromDomain hupd) a = fst (df.total hupd a)
totalIs (HasUnderlyingPartialFromDomain hupd) a = snd (df.total hupd a)


module vf = HasUnderlyingPartialValueFirst
HasUnderlyingPartialFromValue : {S : Type ℓ → Type ℓ'} ( hupv : HasUnderlyingPartialValueFirst {ℓ'' = ℓ''} S ) → HasUnderlyingPartial S
defined (HasUnderlyingPartialFromValue hupv) {A = A} α = Σ[ a ∈ A ] vf.is-this hupv α a
is-this (HasUnderlyingPartialFromValue hupv) = vf.is-this hupv
eval (HasUnderlyingPartialFromValue hupv) _ = fst
isToDefined (HasUnderlyingPartialFromValue hupv) α a u = a , u
includeTotal (HasUnderlyingPartialFromValue hupv) = vf.includeTotal hupv
totalIs (HasUnderlyingPartialFromValue hupv) = vf.totalIs hupv
                                                                
module _ {S : Type ℓ → Type ℓ'} ⦃ hup : HasUnderlyingPartial {ℓ''' = ℓ'''} {ℓ'' = ℓ''} S ⦄ {A : Type ℓ} where
  open HasUnderlyingPartial hup

  get : (α : S A) (d : HasUnderlyingPartial.defined hup α) → A
  get = HasUnderlyingPartial.eval hup

  _↓=_ : S A → A → Type ℓ'''
  _↓=_ α a = HasUnderlyingPartial.is-this hup α a

  {- We say x is defined, or that it denotes an element of A. -}
  _↓ : S A → Type _
  _↓ α = HasUnderlyingPartial.defined hup α

  _↓=↓_ : S A → S A → Type _
  α ↓=↓ β = Σ[ a ∈ A ] (α ↓= a × β ↓= a)

  ι : A → S A
  ι = HasUnderlyingPartial.includeTotal hup

  ιIs : (a : A) → (ι a ↓= a)
  ιIs = HasUnderlyingPartial.totalIs hup

  ιdefd : (a : A) → (ι a ↓)
  ιdefd a = HasUnderlyingPartial.isToDefined hup (ι a) a (ιIs a)
