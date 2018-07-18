-- V: letpair (x,y) = (V,W) in E --> E[ V,W / x,y ]
module Properties.StepPair where

open import Data.List
open import Data.List.All

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global
open import Values
open import Session

open import Properties.Base

-- this will require multiple steps to execute
mklhs : ∀ {t₁ t₂} → Expr (t₁ ∷ t₂ ∷ []) TUnit → Expr (t₁ ∷ t₂ ∷ []) TUnit
mklhs E =
  letbind (left (left [])) (pair (left (rght [])) (here []) (here []))
  (letpair (left []) (here []) E)

reduction :  ∀ {t₁ t₂}
  → (E : Expr (t₁ ∷ t₂ ∷ []) TUnit)
  → (v₁ : Val [] t₁)
  → (v₂ : Val [] t₂)
  → let ϱ = vcons ss-[] v₁ (vcons ss-[] v₂ (vnil []-inactive)) in 
    let lhs = (run (left (left [])) ss-[] (mklhs E) ϱ (halt []-inactive UUnit)) in
    let rhs = (run (left (left [])) ss-[] E ϱ (halt []-inactive UUnit)) in
    restart lhs ≡
    rhs 
reduction E v₁ v₂
  with split-env (left (left [])) (vcons ss-[] v₁ (vcons ss-[] v₂ (vnil []-inactive)))
... | spe
  = refl

