-- V: (λx.e)v = e[v/x]
-- let f = λx.e in let r = f v in E --> [let x = v in] let r = e in E
module Properties.StepBeta where

open import Data.List
open import Data.List.All

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

mklhs : ∀ {tin tout} (e : Expr (tin ∷ []) tout) (E : Expr (tout ∷ []) TUnit) → Expr (tin ∷ []) TUnit
mklhs e E = 
  letbind (rght []) (ulambda [] [] [] e) 
  (letbind (left (left [])) (app (left (rght [])) (here []) (here []))
  E)

mkrhs : ∀ {tin tout} (e : Expr (tin ∷ []) tout) (E : Expr (tout ∷ []) TUnit) → Expr (tin ∷ []) TUnit
mkrhs e E =
  letbind (left []) e E

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
