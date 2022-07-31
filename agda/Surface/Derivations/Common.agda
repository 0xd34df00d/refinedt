{-# OPTIONS --safe #-}

module Surface.Derivations.Common where

open import Surface.Oracle

-- Minimal and enriched type system flavours
data TSFlavour : Set where
  M E : TSFlavour

variable
  φ : TSFlavour
  θ : Oracle

infix 0 _?if_

data _?if_ (A : Set) : TSFlavour → Set where
  omitted   : A ?if M
  enriched  : (δ : A)
            → A ?if E

instance
  omitted-?if : {A : Set} → A ?if M
  omitted-?if = omitted
