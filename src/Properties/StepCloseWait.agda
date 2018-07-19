-- P: (vcd) <E[send c v]> | <F[recv d]>  --> (vcd) <E[c]> | <F[(d,v)]>

-- P: (vcd) <E[close c]> | <F[wait d]>  --> (vcd) <E[()]> | <F[()]>
module Properties.StepCloseWait where

open import Data.Maybe hiding (All)
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Sum

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

mkclose : ∀ {Φ} → Expr (TUnit ∷ Φ) TUnit → Expr (TChan send! ∷ Φ) TUnit
mkclose = λ e → letbind (left (split-all-right _)) (close (here [])) e

mkwait : ∀ {Φ} → Expr (TUnit ∷ Φ) TUnit → Expr (TChan send? ∷ Φ) TUnit
mkwait = λ e → letbind (left (split-all-right _)) (wait (here [])) e

module General where

  mklhs : ∀ {Φ Φ₁ Φ₂}
    → Split Φ Φ₁ Φ₂
    → Expr (TUnit ∷ Φ₁) TUnit
    → Expr (TUnit ∷ Φ₂) TUnit
    → Proc Φ
  mklhs sp e f = 
    res (delay send!)
        (par (left (rght sp))
             (exp (mkclose e)) (exp (mkwait f)))

  mkrhs : ∀ {Φ Φ₁ Φ₂}
    → Split Φ Φ₁ Φ₂
    → Expr (TUnit ∷ Φ₁) TUnit
    → Expr (TUnit ∷ Φ₂) TUnit
    → Proc Φ
  mkrhs sp e f =
    par sp (exp (letbind (split-all-right _) (unit []) e))
           (exp (letbind (split-all-right _) (unit []) f))


  -- obviously true, but requires a nasty inductive proof
  postulate
    weaken2-ident : ∀ {G Φ} (ϱ : VEnv G Φ) → weaken2-venv [] [] ϱ ≡ ϱ

  postulate
    weaken1-ident : ∀ {G Φ} (ϱ : VEnv G Φ) → weaken1-venv [] ϱ ≡ ϱ

  reductionT : Set
  reductionT = 
    ∀ { Φ Φ₁ Φ₂ }
    (sp : Split Φ Φ₁ Φ₂)
    (ϱ : VEnv [] Φ)
    (p : ∃ λ ϱ₁ → ∃ λ ϱ₂ →
           split-env sp (lift-venv ϱ) ≡ (((nothing ∷ []) , (nothing ∷ [])) , (ss-both ss-[]) , ϱ₁ , ϱ₂))
    (e : Expr (TUnit ∷ Φ₁) TUnit)
    (f : Expr (TUnit ∷ Φ₂) TUnit) →
    let lhs = (runProc [] (mklhs sp e f) ϱ) in
    let rhs = (runProc [] (mkrhs sp e f) ϱ) in
    one-step lhs ≡
    (Closed , nothing ∷ proj₁ rhs , lift-threadpool (proj₂ rhs))

  reduction : reductionT
  reduction{Φ}{Φ₁}{Φ₂} sp ϱ p e f
    with ssplit-refl-left-inactive []
  ... | G' , ina-G' , ss-GG'
    with split-env-lemma-2 sp ϱ
  ... | ϱ₁ , ϱ₂ , spe== , sp==
    rewrite spe== | sp==
    with ssplit-compose{just (send! , POSNEG) ∷ []} (ss-posneg ss-[]) (ss-left ss-[])
  ... | ssc
    rewrite split-env-right-lemma ϱ₁
    with ssplit-compose{just (send! , POSNEG) ∷ []} (ss-left ss-[]) (ss-left ss-[])
  ... | ssc-ll
    rewrite split-env-right-lemma ϱ₂
    with ssplit-compose2 (ss-both ss-[]) (ss-both ss-[])
  ... | ssc2
    rewrite weaken2-ident (lift-venv ϱ₁) 
          | split-rotate-lemma {Φ₁}
          | split-rotate-lemma {Φ₂}
          | split-env-right-lemma0 ϱ₁
          | split-env-right-lemma0 ϱ₂
          | weaken2-ident ϱ₁
          | weaken1-ident (lift-venv ϱ₂)
          | weaken1-ident ϱ₂
    = refl

module ClosedWithContext where
  mklhs : Expr (TUnit ∷ []) TUnit
    → Expr (TUnit ∷ []) TUnit
    → Proc []
  mklhs e f = 
    res (delay send!)
        (par (left (rght []))
             (exp (mkclose e)) (exp (mkwait f)))

  mkrhs : Expr (TUnit ∷ []) TUnit
    → Expr (TUnit ∷ []) TUnit
    → Proc []
  mkrhs e f =
    par [] (exp (letbind [] (unit []) e))
           (exp (letbind [] (unit []) f))

  reduction :
    (e f : Expr (TUnit ∷ []) TUnit) →
    let lhs = (runProc [] (mklhs e f) (vnil []-inactive)) in
    let rhs = (runProc [] (mkrhs e f) (vnil []-inactive)) in
    one-step lhs ≡
    (Closed , nothing ∷ proj₁ rhs , lift-threadpool (proj₂ rhs))
  reduction e f
    with ssplit-refl-left-inactive []
  ... | G' , ina-G' , ss-GG'
    = refl
