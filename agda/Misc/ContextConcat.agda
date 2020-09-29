{-# OPTIONS --safe #-}

module Misc.ContextConcat where

open import Data.List.Base using (_++_)

open import Surface.Syntax

infix 19 _,_
_,_ : Ctx → Ctx → Ctx
_,_ Γ Δ = Δ ++ Γ
