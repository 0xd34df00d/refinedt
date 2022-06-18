{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases where

open import Surface.Syntax as S renaming (Γ to Γˢ;
                                          b to bˢ; ρ to ρˢ;
                                          τ to τˢ; τ' to τ'ˢ; σ to σˢ;
                                          τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ;
                                          τ₂ to τ₂ˢ; τ₂' to τ₂'ˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ) using () public
open import Surface.Derivations.Algorithmic as S renaming (θ to θˢ)
                                                 hiding (BranchesHaveType; Oracle; PositiveDecision)
                                                 public

open import Intermediate.Syntax as I renaming (Γ to Γⁱ;
                                               τ to τⁱ; τ' to τ'ⁱ; σ to σⁱ;
                                               τ₁ to τ₁ⁱ; τ₁' to τ₁'ⁱ;
                                               τ₂ to τ₂ⁱ; τ₂' to τ₂'ⁱ;
                                               ε to εⁱ; ε' to ε'ⁱ; ε₁ to ε₁ⁱ; ε₂ to ε₂ⁱ) public
open import Intermediate.Derivations.Algorithmic as I renaming (θ to θⁱ)
                                                 hiding (BranchesHaveType; Oracle; PositiveDecision)
                                                 public
