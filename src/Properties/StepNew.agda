-- P: <E[new s]> --> (vcd) <E[(c,d)]>
module Properties.StepNew where


open import Data.Maybe hiding (All)
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

reduction : (s : SType) (E : Expr (tch s ∷ []) TUnit) →
    let lhs = (runProc [] (mklhs s E) (vnil []-inactive)) in
    let rhs = (runProc [] (mkrhs s E) (vnil []-inactive)) in
    one-step lhs ≡
    (New , proj₁ rhs , proj₂ rhs)
reduction s E
  with ssplit-refl-left-inactive []
... | G' , ina-G' , ss-GG'
  = refl

-- reduction in open context

open-reduction-type : Set
open-reduction-type = ∀ {Φ} (s : SType) (E : Expr (tch s ∷ Φ) TUnit) (ϱ : VEnv [] Φ) →
    let lhs = (runProc [] (mklhs s E) ϱ) in
    let rhs = (runProc [] (mkrhs s E) ϱ) in
    one-step lhs ≡ (New , proj₁ rhs , proj₂ rhs)

open-reduction : open-reduction-type
open-reduction{Φ} s E ϱ 
  with runProc [] (exp (mknew s E)) ϱ
... | rpse
  rewrite split-env-right-lemma0 ϱ
    | split-rotate-lemma {Φ}
    | split-env-right-lemma ϱ
  with ssplit-compose (ss-left{(SType.force s) , POSNEG} ss-[]) (ss-left ss-[])
... | ssc
  = refl

{-

-- reduction in open context with further resources

pairs : ∀ {A : Set} {B : A → Set} {p1 p2 : Σ A λ x → B x }
  → p1 ≡ p2 → Σ (proj₁ p1 ≡ proj₁ p2) λ { refl → proj₂ p1 ≡ proj₂ p2 }
pairs {A} {B} refl = refl , refl

split-env-right-lemma0' :
  ∀ {Φ G} (ϱ : VEnv G Φ) →
  let gis = ssplit-refl-right-inactive G in
  (split-env (split-all-right Φ) ϱ
  ≡
  ((proj₁ gis , G) , proj₂ (proj₂ gis) , vnil (proj₁ (proj₂ gis)) , ϱ))
split-env-right-lemma0' (vnil []-inactive) = refl
split-env-right-lemma0' (vnil (::-inactive ina))
  with split-env-right-lemma0' (vnil ina)
... | ih
  with pairs ih
... | p1== , p2==
  = {!!}
split-env-right-lemma0'{t ∷ Φ} (vcons ssp v ϱ)
  with split-env-right-lemma0' ϱ
... | ih
  with split-env (split-all-right Φ) ϱ
... | sesar
    = {!!}


full-reduction-type : Set
full-reduction-type = ∀ {Φ G} (s : SType) (E : Expr (tch s ∷ Φ) TUnit) (ϱ : VEnv G Φ) →
    let lhs = runProc G (mklhs s E) ϱ in
    let rhs = runProc G (mkrhs s E) ϱ in
    single-step (proj₁ lhs ++ G , proj₂ lhs) ≡ (New , proj₁ rhs ++ G , proj₂ rhs)

full-reduction : full-reduction-type
full-reduction{Φ}{G} s E ϱ 
  with ssplit-refl-left-inactive G
... | ssrli
  rewrite split-env-right-lemma0' ϱ
    | split-rotate-lemma {Φ}
  = {!!}

-}
