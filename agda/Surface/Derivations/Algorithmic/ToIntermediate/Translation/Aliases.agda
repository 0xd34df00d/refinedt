{-# OPTIONS --safe #-}

module Surface.Derivations.Algorithmic.ToIntermediate.Translation.Aliases where

open import Surface.Syntax as S public
                                using ()
                                renaming (Γ to Γˢ; _,_ to _,ˢ_;
                                          b to bˢ; ρ to ρˢ;
                                          τ to τˢ; τ' to τ'ˢ; σ to σˢ; σ' to σ'ˢ;
                                          τ₁ to τ₁ˢ; τ₁' to τ₁'ˢ;
                                          τ₂ to τ₂ˢ; τ₂' to τ₂'ˢ;
                                          ε to εˢ; ε' to ε'ˢ; ε₁ to ε₁ˢ; ε₂ to ε₂ˢ)
open import Surface.Derivations.Algorithmic as S public
                                                 renaming (θ to θˢ)
                                                 hiding (BranchesHaveType; Oracle; PositiveDecision)
open import Surface.Syntax.Substitution public
                                        using ()
                                        renaming ([_↦τ_]_ to [_↦τˢ_]_;
                                                  [_↦ε_]_ to [_↦εˢ_]_;
                                                  [_↦τ<_]_ to [_↦τ<ˢ_]_;
                                                  [_↦ε<_]_ to [_↦ε<ˢ_]_
                                                 )

open import Intermediate.Syntax as I public
                                     renaming (Γ to Γⁱ; _,_ to _,ⁱ_;
                                               τ to τⁱ; τ' to τ'ⁱ; σ to σⁱ; σ' to σ'ⁱ;
                                               τ₁ to τ₁ⁱ; τ₁' to τ₁'ⁱ;
                                               τ₂ to τ₂ⁱ; τ₂' to τ₂'ⁱ;
                                               ε to εⁱ; ε' to ε'ⁱ; ε₁ to ε₁ⁱ; ε₂ to ε₂ⁱ)
open import Intermediate.Derivations.Algorithmic as I public
                                                      renaming (θ to θⁱ)
                                                      hiding (BranchesHaveType; Oracle; PositiveDecision)
open import Intermediate.Syntax.Substitution public
                                             renaming ([_↦τ_]_ to [_↦τⁱ_]_;
                                                       [_↦ε_]_ to [_↦εⁱ_]_;
                                                       [_↦τ<_]_ to [_↦τ<ⁱ_]_;
                                                       [_↦ε<_]_ to [_↦ε<ⁱ_]_
                                                      )
                                             using ()
