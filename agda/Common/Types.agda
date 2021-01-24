{-# OPTIONS --safe #-}

module Common.Types where

open import Data.Nat using (ℕ)

record ℕₐ : Set where
  constructor Mkℕₐ
  field
    get-length : ℕ

variable
  nₐ : ℕₐ
