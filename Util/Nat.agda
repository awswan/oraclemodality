module Util.Nat where

open import Includes

trichotomyRec : {A : Type ℓ} → (m n : ℕ) → (m < n → A) → (m ≡ n → A) → (m > n → A) → A
trichotomyRec m n iflt ifeq ifgt with m ≟ n
... | lt p = iflt p
... | eq p = ifeq p
... | gt p = ifgt p
