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

-- V: (λx.e)v = e[v/x]
-- let f = λx.e in let r = f v in E --> [let x = v in] let r = e in E

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

-- open reduction with split between closure and context

mktype' : Set
mktype' =  ∀ {Φ Φ₁ Φ₂ tin tout}
  (sp : Split Φ Φ₁ Φ₂) (un-Φ₁ : All Unr Φ₁) (e : Expr (tin ∷ Φ₁) tout) (E : Expr (tout ∷ Φ₂) TUnit)
  → Expr (tin ∷ Φ) TUnit

mklhs' : mktype'
mklhs' {Φ} {Φ₁} {Φ₂} sp un-Φ₁ e E = 
  letbind (rght sp) (ulambda (split-all-left Φ₁) un-Φ₁ [] e) 
  (letbind (left (left (split-all-right Φ₂))) (app (left (rght [])) (here []) (here []))
  E)

mkrhs' : mktype'
mkrhs' {Φ} {Φ₁} {Φ₂} sp un-Φ₁ e E =
  letbind (left sp) e E

reduction-open-type' : Set
reduction-open-type' = ∀ {Φ Φ₁ Φ₂ tin tout}
  (sp : Split Φ Φ₁ Φ₂) (un-Φ₁ : All Unr Φ₁)
  (e : Expr (tin ∷ Φ₁) tout) (E : Expr (tout ∷ Φ₂) TUnit)
  (ϱ : VEnv [] (tin ∷ Φ))
  → let lhs = run (left (split-all-left Φ)) ss-[] (mklhs' sp un-Φ₁ e E) ϱ (halt []-inactive UUnit) in
    let rhs = run (left (split-all-left Φ)) ss-[] (mkrhs' sp un-Φ₁ e E) ϱ (halt []-inactive UUnit) in
    restart (restart lhs) ≡ rhs

-- this runs into the split-from-disjoint, which was hacked into function application
-- it's not clear if there's a way round
-- hence the proposition needs to be proved with a more specific assumption
{-
reduction-open' : reduction-open-type'
reduction-open' {Φ} {Φ₁} {Φ₂} sp un-Φ₁ e E (vcons ss-[] v ϱ)
  rewrite split-rotate-lemma' sp
  with split-env sp ϱ
... | ([] , []) , ss-[] , ϱ₁ , ϱ₂
  rewrite split-env-left-lemma0 ϱ₁
  with ssplit-compose3 ss-[] ss-[]
... | ssc3
  rewrite split-env-right-lemma0 ϱ₂
  with ssplit-compose3 ss-[] ss-[]
... | ssc3'
  rewrite split-rotate-lemma {Φ₂}
  = {!!}
-}

-- straightforward generalization of the inspect pattern
record Reveal2_·_·_is_ {A B : Set} {C : A → B → Set}
                    (f : (x : A) (y : B) → C x y) (x : A) (y : B) (z : C x y) :
                    Set₁ where
  constructor [[_]]
  field eq : f x y ≡ z

inspect2 : ∀ {A B : Set} {C : A → B → Set}
          (f : (x : A) (y : B) → C x y) (x : A) (y : B) → Reveal2 f · x · y is f x y
inspect2 f x y = [[ refl ]]


reduction-open-type'' : Set
reduction-open-type'' = ∀ {Φ₁ Φ₂ tin tout} → 
  let Φ,sp = split-from-disjoint Φ₁ Φ₂ in
  let Φ = proj₁ Φ,sp in
  let sp = proj₂ Φ,sp in
  (un-Φ₁ : All Unr Φ₁)
  (e : Expr (tin ∷ Φ₁) tout) (E : Expr (tout ∷ Φ₂) TUnit)
  (ϱ : VEnv [] (tin ∷ Φ))
  → let lhs = run (left (split-all-left Φ)) ss-[] (mklhs' sp un-Φ₁ e E) ϱ (halt []-inactive UUnit) in
    let rhs = run (left (split-all-left Φ)) ss-[] (mkrhs' sp un-Φ₁ e E) ϱ (halt []-inactive UUnit) in
    restart (restart lhs) ≡ rhs

reduction-open'' : reduction-open-type''
reduction-open'' {Φ₁} {Φ₂} un-Φ₁ e E (vcons ss-[] v ϱ)
  with split-from-disjoint Φ₁ Φ₂ | inspect2 split-from-disjoint Φ₁ Φ₂
... | Φ , sp | [[ eq ]]
  rewrite split-rotate-lemma' sp
  with split-env sp ϱ
... | ([] , []) , ss-[] , ϱ₁ , ϱ₂
  rewrite split-env-left-lemma0 ϱ₁
  with ssplit-compose3 ss-[] ss-[]
... | ssc3
  rewrite split-env-right-lemma0 ϱ₂
  with ssplit-compose3 ss-[] ss-[]
... | ssc3'
  rewrite split-rotate-lemma {Φ₂} | eq
  = refl
