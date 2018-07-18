-- P: <E[fork e]> --> <E[()]> | <e>
module Properties.StepFork where

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

mkfork : ∀ {Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → Expr Φ₁ TUnit → Expr (TUnit ∷ Φ₂) TUnit → Expr Φ TUnit
mkfork sp e E = letbind sp (fork e) E

mklhs : ∀ {Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂
  → Expr Φ₁ TUnit → Expr (TUnit ∷ Φ₂) TUnit → Proc Φ
mklhs sp e E =
  exp (mkfork sp e E)

mkrhs : ∀ {Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂
  → Expr Φ₁ TUnit → Expr (TUnit ∷ Φ₂) TUnit → Proc Φ
mkrhs sp e E =
  par sp (exp e) (exp (letbind (split-all-right _) (unit []) E))

-- weaken2-command : ∀ {G} G' G'' → Command (G' ++ G) → Command (G' ++ inactive-clone G'' ++ G)

-- obviously true, but requires a nasty inductive proof
postulate
  weaken2-ident : ∀ {G} → (cmd : Command G) → weaken2-command [] [] cmd ≡ cmd

reduction : (e : Expr [] TUnit) → (E : Expr (TUnit ∷ []) TUnit)
  →
    let lhs = (runProc [] (mklhs [] e E) (vnil []-inactive)) in
    let rhs = (runProc [] (mkrhs [] e E) (vnil []-inactive)) in
    let rhs' = one-step rhs in
    one-step lhs ≡
    (Forked , proj₁ rhs , proj₂ rhs)
reduction e E
  with ssplit-refl-left-inactive []
... | G' , ina-G' , ss-GG'
  rewrite weaken2-ident (run [] ss-[] e (vnil []-inactive) (halt []-inactive UUnit))
  = refl

