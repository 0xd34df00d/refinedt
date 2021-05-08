{-# OPTIONS --safe #-}

module Core.Syntax.Injectivity where

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Common.Types
open import Core.Syntax

CVar-injective : Injective (CVar {ℓ})
CVar-injective refl = refl

CΠ-injective : Injective₂ (CΠ {ℓ})
CΠ-injective refl = ⟨ refl , refl ⟩

CLam-injective : Injective₂ (CLam {ℓ})
CLam-injective refl = ⟨ refl , refl ⟩

CApp-injective : Injective₂ (CApp {ℓ})
CApp-injective refl = ⟨ refl , refl ⟩

CADT-injective-len : {cons  : ADTCons (Mkℕₐ (suc n))  ℓ}
                   → {cons' : ADTCons (Mkℕₐ (suc n')) ℓ}
                   → CADT cons ≡ CADT cons'
                   → n ≡ n'
CADT-injective-len refl = refl

CADT-injective : Injective (CADT {n} {ℓ})
CADT-injective refl = refl

CCon-injective-len : {cons  : ADTCons (Mkℕₐ n)  ℓ}
                   → {cons' : ADTCons (Mkℕₐ n') ℓ}
                   → CCon ι ε cons ≡ CCon ι' ε' cons'
                   → n ≡ n'
CCon-injective-len refl = refl

CCon-injective : Injective₃ (CCon {n} {ℓ})
CCon-injective refl = ⟨ refl , ⟨ refl , refl ⟩ ⟩


CCase-injective-len : {bs  : CaseBranches nₐ  ℓ}
                    → {bs' : CaseBranches nₐ' ℓ}
                    → CCase ε bs ≡ CCase ε' bs'
                    → nₐ ≡ nₐ'
CCase-injective-len refl = refl

CCase-injective : Injective₂ (CCase {ℓ} {nₐ})
CCase-injective refl = ⟨ refl , refl ⟩
