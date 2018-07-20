-- V: (λx.e)v = e[v/x]
-- let f = λx.e in let r = f v in E --> [let x = v in] let r = e in E
module Properties.StepBeta where

open import Data.List
open import Data.List.All
open import Data.Product

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global
open import Channel
open import Values
open import Session
open import Schedule

open import ProcessSyntax
open import ProcessRun

open import Properties.Base

mklhs : ∀ {Φ tin tout} (e : Expr (tin ∷ []) tout) (E : Expr (tout ∷ Φ) TUnit) → Expr (tin ∷ Φ) TUnit
mklhs {Φ} e E = 
  letbind (rght (split-all-right Φ)) (ulambda [] [] [] e) 
  (letbind (left (left (split-all-right Φ))) (app (left (rght [])) (here []) (here []))
  E)

mkrhs : ∀ {Φ tin tout} (e : Expr (tin ∷ []) tout) (E : Expr (tout ∷ Φ) TUnit) → Expr (tin ∷ Φ) TUnit
mkrhs {Φ} e E =
  letbind (left (split-all-right Φ)) e E

reductionT : Set
reductionT = ∀ {tin tout}
  (e : Expr (tin ∷ []) tout) (E : Expr (tout ∷ []) TUnit)
  (v : Val [] tin)
  → let ϱ = vcons ss-[] v (vnil []-inactive) in
    let lhs = run (left []) ss-[] (mklhs e E) ϱ (halt []-inactive UUnit) in
    let rhs = run (left []) ss-[] (mkrhs e E) ϱ (halt []-inactive UUnit) in
    restart (restart lhs) ≡ rhs

reduction : reductionT
reduction e E v
  with split-env (rght []) (vcons ss-[] v (vnil []-inactive))
... | sperght
  = refl

-- open reduction

reduction-open-type : Set
reduction-open-type = ∀ {Φ tin tout}
  (e : Expr (tin ∷ []) tout) (E : Expr (tout ∷ Φ) TUnit)
  (ϱ : VEnv [] (tin ∷ Φ))
  → let lhs = run (left (split-all-left Φ)) ss-[] (mklhs e E) ϱ (halt []-inactive UUnit) in
    let rhs = run (left (split-all-left Φ)) ss-[] (mkrhs e E) ϱ (halt []-inactive UUnit) in
    restart (restart lhs) ≡ rhs

reduction-open : reduction-open-type
reduction-open {Φ} e E (vcons ss-[] v ϱ)
  rewrite split-rotate-lemma {Φ}
  | split-env-right-lemma0 ϱ
  with ssplit-compose3 ss-[] ss-[]
... | ssc3
  rewrite split-env-right-lemma0 ϱ
  | split-rotate-lemma {Φ}
  = refl
