{-# OPTIONS --safe #-}

module Surface.Derivations.Common where

data TSFlavour : Set where
  M E : TSFlavour

variable
  φ : TSFlavour

data Enrich (A : Set) : TSFlavour → Set where
  omitted   : Enrich A M
  enriched  : (δ : A)
            → Enrich A E

as-enrichment : ∀ {A}
              → A
              → Enrich A φ
as-enrichment {φ = M} δ = omitted
as-enrichment {φ = E} δ = enriched δ
