{-# OPTIONS --safe #-}

module Core.Syntax.Renaming.Injectivity where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Product using (proj₁; proj₂; _×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Syntax
open import Core.Syntax.Injectivity
open import Core.Syntax.Renaming
open import Common.Types

variable
  f : Fin ℓ → Fin ℓ'

ext-injective : Injective f
              → Injective (ext f)
ext-injective f-inj {zero} {zero} ≡ = refl
ext-injective f-inj {suc x₁} {suc x₂} ≡ rewrite f-inj (suc-injective ≡) = refl

∷-injective : {A : Set}
            → Injective₂ {A} {Vec A n} (_∷_)
∷-injective refl = ⟨ refl , refl ⟩

mutual
  act-cons-injective : Injective f
                     → Injective (act-cons {nₐ} f)
  act-cons-injective f-inj {[]} {[]} _ = refl
  act-cons-injective f-inj {x ∷ _} {y ∷ _} ≡ with ∷-injective ≡
  ... | ⟨ head , tail ⟩ rewrite act-ε-injective f-inj {x} {y} head
                              | act-cons-injective f-inj tail
                              = refl

  act-bs-injective : Injective f
                   → Injective (act-branches {nₐ} f)
  act-bs-injective f-inj {[]} {[]} _ = refl
  act-bs-injective f-inj {x ∷ _} {y ∷ _} ≡ with ∷-injective ≡
  ... | ⟨ head , tail ⟩ rewrite act-ε-injective (ext-injective (ext-injective f-inj)) {x} {y} head
                              | act-bs-injective f-inj tail
                              = refl

  act-ε-injective : Injective f
                  → Injective (act-ε f)
  act-ε-injective f-inj {CVar _} {CVar _} ≡
    rewrite f-inj (CVar-injective ≡) = refl
  act-ε-injective f-inj {CSort _} {CSort _} refl = refl
  act-ε-injective f-inj {CΠ ε₁ ε₂} {CΠ ε₁' ε₂'} ≡
    rewrite act-ε-injective f-inj                 {ε₁} {ε₁'} (proj₁ (CΠ-injective ≡))
          | act-ε-injective (ext-injective f-inj) {ε₂} {ε₂'} (proj₂ (CΠ-injective ≡))
          = refl
  act-ε-injective f-inj {CLam ε₁ ε₂} {CLam ε₁' ε₂'} ≡
    rewrite act-ε-injective f-inj                 {ε₁} {ε₁'} (proj₁ (CLam-injective ≡))
          | act-ε-injective (ext-injective f-inj) {ε₂} {ε₂'} (proj₂ (CLam-injective ≡))
          = refl
  act-ε-injective f-inj {CApp ε₁ ε₂} {CApp ε₁' ε₂'} ≡
    rewrite act-ε-injective f-inj {ε₁} {ε₁'} (proj₁ (CApp-injective ≡))
          | act-ε-injective f-inj {ε₂} {ε₂'} (proj₂ (CApp-injective ≡))
          = refl
  act-ε-injective f-inj {Cunit} {Cunit} _ = refl
  act-ε-injective f-inj {CUnit} {CUnit} _ = refl
  act-ε-injective f-inj {CADT cons} {CADT cons₁} ≡ with CADT-injective-len ≡
  ... | refl rewrite act-cons-injective f-inj (CADT-injective ≡) = refl
  act-ε-injective f-inj {CCon ι ε cons} {CCon ι' ε' cons'} ≡ with CCon-injective-len ≡
  ... | refl with CCon-injective ≡
  ...   | ⟨ refl , ⟨ p₁ , p₂ ⟩ ⟩
            rewrite act-ε-injective f-inj {ε} {ε'} p₁
                  | act-cons-injective f-inj p₂
                  = refl
  act-ε-injective f-inj {CCase ε bs} {CCase ε' bs'} ≡ with CCase-injective-len ≡
  ... | refl
          rewrite act-ε-injective f-inj {ε} {ε'} (proj₁ (CCase-injective ≡))
                | act-bs-injective f-inj (proj₂ (CCase-injective ≡))
                = refl
