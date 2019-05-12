module Properties.Base where

open import Data.Maybe hiding (All)
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Sum

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Global
open import Values
open import Session
open import Schedule

one-step : ∀ {G} → (∃ λ G' → ThreadPool (G' ++ G)) → Event × (∃ λ G → ThreadPool G)
one-step{G} (G1 , tp)
  with ssplit-refl-left-inactive (G1 ++ G)
... | G' , ina-G' , ss-GG'
  with Alternative.step ss-GG' tp (tnil ina-G')
... | ev , tp' = ev , ( _ , tp')

restart : ∀ {G} → Command G → Command G
restart (Ready ss v κ) = apply-cont ss κ v
restart cmd = cmd

-- auxiliary lemmas

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

split-env-right-lemma0 :
  ∀ {Φ} (ϱ : VEnv [] Φ) → 
  split-env (split-all-right Φ) ϱ
  ≡
  (([] , []) , ss-[] , vnil []-inactive , ϱ)
split-env-right-lemma0 (vnil []-inactive) = refl
split-env-right-lemma0 (vcons ss-[] v ϱ)
  rewrite split-env-right-lemma0 ϱ
  = refl

split-env-left-lemma0 :
  ∀ {Φ} (ϱ : VEnv [] Φ) → 
  split-env (split-all-left Φ) ϱ
  ≡
  (([] , []) , ss-[] , ϱ , vnil []-inactive)
split-env-left-lemma0 (vnil []-inactive) = refl
split-env-left-lemma0 (vcons ss-[] v ϱ)
  rewrite split-env-left-lemma0 ϱ
  = refl


split-env-lemma-2T : Set
split-env-lemma-2T =
  ∀ { Φ Φ₁ Φ₂ }
  (sp : Split Φ Φ₁ Φ₂)
  (ϱ : VEnv [] Φ)
  → ∃ λ ϱ₁ → ∃ λ ϱ₂ →
             split-env sp (lift-venv ϱ) ≡
             (_ , (ss-both ss-[]) , lift-venv ϱ₁ , lift-venv ϱ₂)
             ×
             split-env sp ϱ ≡
             (_ , ss-[] , ϱ₁ , ϱ₂)

split-env-lemma-2 : split-env-lemma-2T
split-env-lemma-2 [] (vnil []-inactive)
  = (vnil []-inactive) , ((vnil []-inactive) , (refl , refl))
split-env-lemma-2 (dupl unrt sp) (vcons ss-[] v ϱ)
  with split-env-lemma-2 sp ϱ
... | ϱ₁ , ϱ₂ , selift-ind , se-ind
  rewrite se-ind | lift-unrestricted unrt v
  with unrestricted-val unrt v
... | []-inactive
  rewrite selift-ind
  with ssplit-compose3 (ss-both ss-[]) (ss-both ss-[])
... | ssc3
  = (vcons ss-[] v ϱ₁) , (vcons ss-[] v ϱ₂) , refl , refl
split-env-lemma-2 (Split.drop unrt sp) (vcons ss-[] v ϱ) 
  with split-env-lemma-2 sp ϱ
... | ϱ₁ , ϱ₂ , selift-ind , se-ind
  rewrite se-ind | lift-unrestricted unrt v
  with unrestricted-val unrt v
... | []-inactive
  = ϱ₁ , ϱ₂ , selift-ind , se-ind
split-env-lemma-2 (left sp) (vcons ss-[] v ϱ)
  with split-env-lemma-2 sp ϱ
... | ϱ₁ , ϱ₂ , selift-ind , se-ind
  rewrite se-ind | selift-ind
  with ssplit-compose3 (ss-both ss-[]) (ss-both ss-[])
... | ssc3
  = (vcons ss-[] v ϱ₁) , ϱ₂ , refl , refl
split-env-lemma-2 (rght sp) (vcons ss-[] v ϱ)
  with split-env-lemma-2 sp ϱ
... | ϱ₁ , ϱ₂ , selift-ind , se-ind
  rewrite se-ind | selift-ind
  with ssplit-compose4 (ss-both ss-[]) (ss-both ss-[])
... | ssc4
  = ϱ₁ , (vcons ss-[] v ϱ₂) , refl , refl

split-rotate-lemma : ∀ {Φ} →
  split-rotate (split-all-left Φ) (split-all-right Φ)
  ≡
  (Φ , split-all-right Φ , split-all-left Φ)

split-rotate-lemma {[]} = refl
split-rotate-lemma {x ∷ Φ}
  rewrite split-rotate-lemma {Φ}
  = refl

split-rotate-lemma' :  ∀ {Φ Φ₁ Φ₂}
  (sp : Split Φ Φ₁ Φ₂) →
  split-rotate (split-all-left Φ) sp
  ≡
  (Φ₂ , sp , split-all-left Φ₂)

split-rotate-lemma' {[]} [] = refl
split-rotate-lemma' {x ∷ Φ} (dupl un-x sp)
  rewrite split-rotate-lemma' {Φ} sp
  = refl
split-rotate-lemma' {x ∷ Φ} {Φ₁} {Φ₂} (Split.drop un-x sp)
  rewrite split-rotate-lemma' {Φ} sp
  = refl
split-rotate-lemma' {x ∷ Φ} (left sp)
  rewrite split-rotate-lemma' {Φ} sp
  = refl
split-rotate-lemma' {x ∷ Φ} (rght sp)
  rewrite split-rotate-lemma' {Φ} sp
  = refl


ssplit-compose-lemma : ∀ ss → 
  ssplit-compose ss-[] ss ≡ ([] , ss-[] , ss-[])
ssplit-compose-lemma ss-[] = refl

