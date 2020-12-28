{-# OPTIONS --safe #-}

module Surface.Operational.Lemmas where

open import Surface.WellScoped
open import Surface.WellScoped.Renaming as R
open import Surface.Operational

renaming-preserves-values : {ρ : Fin ℓ → Fin ℓ'}
                          → IsValue ϖ
                          → IsValue (R.act-ε ρ ϖ)
renaming-preserves-values IV-Abs = IV-Abs
renaming-preserves-values IV-Unit = IV-Unit
renaming-preserves-values (IV-ADT is-value) = IV-ADT (renaming-preserves-values is-value)
