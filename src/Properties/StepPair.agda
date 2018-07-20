-- V: letpair (x,y) = (V,W) in E --> E[ V,W / x,y ]
module Properties.StepPair where

open import Data.List
open import Data.List.All
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global
open import Values
open import Session

open import Properties.Base

-- this will require multiple steps to execute
mklhs : ∀ {Φ t₁ t₂} → Expr (t₁ ∷ t₂ ∷ Φ) TUnit → Expr (t₁ ∷ t₂ ∷ Φ) TUnit
mklhs {Φ} E =
  letbind (left (left (split-all-right Φ))) (pair (left (rght [])) (here []) (here []))
  (letpair (left (split-all-right Φ)) (here []) E)

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

reduction-open-type : Set
reduction-open-type = ∀ {Φ t₁ t₂}
  (E : Expr (t₁ ∷ t₂ ∷ Φ) TUnit)
  (ϱ : VEnv [] (t₁ ∷ t₂ ∷ Φ))
  → 
    let lhs = run (left (left (split-all-left Φ))) ss-[] (mklhs E) ϱ (halt []-inactive UUnit) in
    let rhs = run (left (left (split-all-left _))) ss-[] E ϱ (halt []-inactive UUnit) in
    restart lhs ≡ rhs

reduction-open : reduction-open-type
reduction-open {Φ} E (vcons ss-[] v (vcons ss-[] v₁ ϱ))
  rewrite split-rotate-lemma {Φ}
  | split-env-right-lemma0 ϱ
  with ssplit-compose3 ss-[] ss-[]
... | ssc3
    rewrite split-env-right-lemma0 ϱ
     | split-rotate-lemma {Φ}
  = refl

