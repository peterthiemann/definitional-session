-- P: <E[new s]> --> (vcd) <E[(c,d)]>
module Properties.StepNew where


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

tch : SType → Type
tch s = (TPair (TChan (SType.force s)) (TChan (SType.force (dual s))))

mknew : ∀ {Φ} → (s : SType) → Expr (tch s ∷ Φ) TUnit → Expr Φ TUnit
mknew s E = letbind (split-all-right _) (new [] s) E

mklhs : ∀ {Φ} → (s : SType) → Expr (tch s ∷ Φ) TUnit → Proc Φ
mklhs s E = exp (mknew s E)

mkrhs : ∀ {Φ} → (s : SType) → Expr (tch s ∷ Φ) TUnit → Proc Φ
mkrhs s E = res s (exp (letbind (left (left (split-all-right _))) (pair (left (rght [])) (here []) (here [])) E))

reduction : (s : SType) (E : Expr (tch s ∷ []) TUnit)
  →
    let lhs = (runProc [] (mklhs s E) (vnil []-inactive)) in
    let rhs = (runProc [] (mkrhs s E) (vnil []-inactive)) in
    let rhs' = one-step rhs in
    one-step lhs ≡
    (New , proj₁ rhs , proj₂ rhs)
reduction s E
  with ssplit-refl-left-inactive []
... | G' , ina-G' , ss-GG'
  = refl
