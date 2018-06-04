module ProcessRun where

open import Data.List
open import Data.Maybe
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Typing
open import ProcessSyntax

open import Global
open import Values
open import Session

list-right-zero : ∀ {A : Set} → (xs : List A) → xs ++ [] ≡ xs
list-right-zero [] = refl
list-right-zero (x ∷ xs) = cong (_∷_ x) (list-right-zero xs)

list-assoc : ∀ {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
list-assoc [] ys zs = refl
list-assoc (x ∷ xs) ys zs = cong (_∷_ x) (list-assoc xs ys zs)

inactive-clone : (G : SCtx) → SCtx
inactive-clone [] = []
inactive-clone (x ∷ G) = nothing ∷ inactive-clone G

left-right : (G' G'' : SCtx) → SSplit (G' ++ G'') (G' ++ inactive-clone G'') (inactive-clone G' ++ G'')
left-right [] G'' = {!!}
left-right (x ∷ G') G'' = {!!}

runProc : ∀ {Φ} → Fuel → (G : SCtx) → Proc Φ → VEnv G Φ → ∃ λ G' → ∃ λ G'' → ThreadPool (G' ++ G ++ G'')
runProc {Φ} f G (exp e) ϱ with ssplit-refl-left-inactive ([] ++ G ++ [])
... | G' , ina-G' , sp-GGG' = [] , [] , tcons sp-GGG' (run f (split-all-left _) sp-GGG' e ϱ' (halt-cont ina-G' UUnit)) (tnil ina-G')
  where ϱ' : VEnv (G ++ []) Φ
        ϱ' rewrite list-right-zero G = ϱ
runProc f G (par sp P₁ P₂) ϱ with split-env sp ϱ
... | (G₁ , G₂) , ss-GG1G2 , ϱ₁ , ϱ₂ with runProc f G₁ P₁ ϱ₁ | runProc f G₂ P₂ ϱ₂
... | (G₁' , G₁'' , tp1) | (G₂' , G₂'' , tp2) = G₁' ++ G₂' , G₁'' ++ G₂'' , tappend {!!} tp1 tp2
runProc f G (res s P) ϱ with runProc f (just (SType.force s , POSNEG) ∷ G) P {!!}
... | G' , G'' , tp = G' ++ just  (SType.force s , POSNEG) ∷ [] , G'' , tp'
  where tp' : ThreadPool ((G' ++ just (SType.force s , POSNEG) ∷ []) ++ G ++ G'')
        tp' rewrite (list-assoc G' (just  (SType.force s , POSNEG) ∷ []) (G ++ G'')) = tp

startProc : Fuel → Proc [] → Outcome
startProc f P with runProc f [] P (vnil []-inactive)
... | G' , G'' , tp = schedule f (G' ++ G'') tp
