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

{-  
  postulate -- a heterogeneous equality
    lift-empty : ∀ {Φ} → (ϱ : VEnv [] Φ) → ϱ ≡ lift-venv ϱ
-}

  lift-unrestricted : 
    ∀ {t G} (unrt : Unr t) (v : Val G t) 
    → unrestricted-val unrt (lift-val v) ≡ ::-inactive (unrestricted-val unrt v)
  lift-unrestricted-venv : 
    ∀ {Φ G} (unrt : All Unr Φ) (ϱ : VEnv G Φ) 
    → unrestricted-venv unrt (lift-venv ϱ) ≡ ::-inactive (unrestricted-venv unrt ϱ)

  lift-unrestricted UUnit (VUnit inaG) = refl
  lift-unrestricted UInt (VInt i inaG) = refl
  lift-unrestricted (UPair unrt unrt₁) (VPair ss-GG₁G₂ v v₁)
    rewrite lift-unrestricted unrt v | lift-unrestricted unrt₁ v₁
    = refl
  lift-unrestricted UFun (VFun (inj₁ ()) ϱ e)
  lift-unrestricted UFun (VFun (inj₂ y) ϱ e) = lift-unrestricted-venv y ϱ

  lift-unrestricted-venv [] (vnil ina) = refl
  lift-unrestricted-venv (px ∷ unrt) (vcons ssp v ϱ)
    rewrite lift-unrestricted px v | lift-unrestricted-venv unrt ϱ
    = refl

  unrestricted-empty : ∀ {t} → (unrt : Unr t) (v : Val [] t) → unrestricted-val unrt v ≡ []-inactive
  unrestricted-empty-venv : ∀ {t} → (unrt : All Unr t) (v : VEnv [] t) → unrestricted-venv unrt v ≡ []-inactive

  unrestricted-empty UUnit (VUnit []-inactive) = refl
  unrestricted-empty UInt (VInt i []-inactive) = refl
  unrestricted-empty (UPair unrt unrt₁) (VPair ss-[] v v₁)
    rewrite unrestricted-empty unrt v | unrestricted-empty unrt₁ v₁
    = refl
  unrestricted-empty UFun (VFun (inj₁ ()) ϱ e)
  unrestricted-empty UFun (VFun (inj₂ y) ϱ e) = unrestricted-empty-venv y ϱ

  unrestricted-empty-venv [] (vnil []-inactive) = refl
  unrestricted-empty-venv (px ∷ unrt) (vcons ss-[] v v₁)
    rewrite unrestricted-empty px v | unrestricted-empty-venv unrt v₁
    = refl

  split-env-lemma :
    ∀ { Φ Φ₁ Φ₂ }
    (sp : Split Φ Φ₁ Φ₂)
    (ϱ : VEnv [] Φ)
    → ∃ λ ϱ₁ → ∃ λ ϱ₂ →
               split-env sp (lift-venv ϱ) ≡
               (((nothing ∷ []) , (nothing ∷ [])) , (ss-both ss-[]) , lift-venv ϱ₁ , lift-venv ϱ₂)

  split-env-lemma [] (vnil []-inactive) =
    (vnil []-inactive) , ((vnil []-inactive) , refl)
  split-env-lemma (dupl unrt sp) (vcons ss-[] v ϱ)
    with split-env-lemma sp ϱ | unrestricted-val unrt v
  ... | ϱ₁ , ϱ₂ , spe==  | unr-v
    rewrite inactive-left-ssplit ss-[] unr-v | lift-unrestricted unrt v | unrestricted-empty unrt v | spe==
    with ssplit-compose3 (ss-both ss-[]) (ss-both ss-[])
  ... | ssc3
    = (vcons ss-[] v ϱ₁)
    , (vcons ss-[] v ϱ₂)
    , refl
  split-env-lemma (Split.drop unrt sp) (vcons ss-[] v ϱ) 
    with split-env-lemma sp ϱ | unrestricted-val unrt v
  ... | ϱ₁ , ϱ₂ , spe== | unr-v
    rewrite lift-unrestricted unrt v | unrestricted-empty unrt v
    = ϱ₁ , ϱ₂ , spe==
  split-env-lemma (left sp) (vcons ss-[] v ϱ) 
    with split-env-lemma sp ϱ
  ... | ϱ₁ , ϱ₂ , spe==
    rewrite spe==
    with ssplit-compose3 (ss-both ss-[]) (ss-both ss-[])
  ... | ssc3
    = (vcons ss-[] v ϱ₁) , (ϱ₂ , refl)
  split-env-lemma (rght sp) (vcons ss-[] v ϱ)
    with split-env-lemma sp ϱ
  ... | ϱ₁ , ϱ₂ , spe==
    rewrite spe==
    with ssplit-compose4 (ss-both ss-[]) (ss-both ss-[])
  ... | ssc4
    = ϱ₁ , (vcons ss-[] v ϱ₂) , refl

  split-env-right-lemma :
    ∀ {Φ} (ϱ : VEnv [] Φ) → 
    split-env (split-all-right Φ) (lift-venv ϱ)
    ≡
    (((nothing ∷ []) , (nothing ∷ [])) , (ss-both ss-[]) , vnil (::-inactive []-inactive) , lift-venv ϱ)
  split-env-right-lemma (vnil []-inactive) = refl
  split-env-right-lemma (vcons ss-[] v ϱ)
    with split-env-right-lemma ϱ
  ... | sperl
    rewrite sperl
    with ssplit-compose4 (ss-both ss-[]) (ss-both ss-[])
  ... | ssc4
    = refl

  -- obviously true, but requires a nasty inductive proof
  postulate
    weaken2-ident : ∀ {G Φ} → (ϱ : VEnv G Φ) → weaken2-venv [] [] ϱ ≡ ϱ

  split-rotate-lemma : ∀ {Φ} →
    split-rotate (split-all-left Φ) (split-all-right Φ)
    ≡
    (Φ , split-all-right Φ , split-all-left Φ)

  split-rotate-lemma {[]} = refl
  split-rotate-lemma {x ∷ Φ}
    rewrite split-rotate-lemma {Φ}
    = refl

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
    with split-env sp ϱ
  ... | _ , ss-[] , ϱ₁' , ϱ₂'
    with split-env-lemma sp ϱ
  ... | ϱ₁ , ϱ₂ , spe==
    rewrite spe==
    with ssplit-compose{just (send! , POSNEG) ∷ []} (ss-posneg ss-[]) (ss-left ss-[])
  ... | ssc
    rewrite split-env-right-lemma ϱ₁
    with ssplit-compose{just _ ∷ []} (ss-left ss-[]) (ss-left ss-[])
  ... | ssc-ll
    rewrite split-env-right-lemma ϱ₂
    with ssplit-compose2 (ss-both ss-[]) (ss-both ss-[])
  ... | ssc2
    rewrite weaken2-ident (lift-venv ϱ₁) 
          | split-rotate-lemma {Φ₁}
          | split-rotate-lemma {Φ₂}
          | split-env-right-lemma ϱ₁'
--          |  split-env-right-lemma ϱ₂'
    = {!!}

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
