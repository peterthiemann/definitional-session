module ProcessRun where

open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Typing
open import ProcessSyntax

open import Channel
open import Global
open import Values
open import Session
open import Schedule

-- auxiliary lemmas
list-right-zero : ∀ {A : Set} → (xs : List A) → xs ++ [] ≡ xs
list-right-zero [] = refl
list-right-zero (x ∷ xs) = cong (_∷_ x) (list-right-zero xs)

list-assoc : ∀ {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
list-assoc [] ys zs = refl
list-assoc (x ∷ xs) ys zs = cong (_∷_ x) (list-assoc xs ys zs)

cons-assoc : ∀ {A : Set} → (x : A) (xs ys : List A) → (x ∷ xs) ++ ys ≡ x ∷ (xs ++ ys)
cons-assoc x xs ys = refl

inactive-clone : (G : SCtx) → SCtx
inactive-clone [] = []
inactive-clone (x ∷ G) = nothing ∷ inactive-clone G

inactive-extension : ∀ {G} → Inactive G → (G' : SCtx) → Inactive (inactive-clone G' ++ G)
inactive-extension inaG [] = inaG
inactive-extension inaG (x ∷ G') = ::-inactive (inactive-extension inaG G')

splitting-extension : ∀ {G G₁ G₂} (G' : SCtx)
  → SSplit G G₁ G₂ → SSplit (inactive-clone G' ++ G) (inactive-clone G' ++ G₁) (inactive-clone G' ++ G₂)
splitting-extension [] ss = ss
splitting-extension (x ∷ G') ss = ss-both (splitting-extension G' ss)

left-right : (G' G'' : SCtx) 
  → SSplit (G' ++ G'') (G' ++ inactive-clone G'') (inactive-clone G' ++ G'')
left-right [] [] = ss-[]
left-right [] (just x ∷ G'') = ss-right (left-right [] G'')
left-right [] (nothing ∷ G'') = ss-both (left-right [] G'')
left-right (x ∷ G') G'' with left-right G' G''
... | ss-G'G'' with x
left-right (x ∷ G') G'' | ss-G'G'' | just x₁ = ss-left ss-G'G''
left-right (x ∷ G') G'' | ss-G'G'' | nothing = ss-both ss-G'G''

ssplit-append : { G11 G12  G21 G22 : SCtx} (G1 G2 : SCtx) → SSplit G1 G11 G12 → SSplit G2 G21 G22 → SSplit (G1 ++ G2) (G11 ++ G21) (G12 ++ G22)
ssplit-append _ _ ss-[] ss2 = ss2
ssplit-append _ _ (ss-both ss1) ss2 = ss-both (ssplit-append _ _ ss1 ss2)
ssplit-append _ _ (ss-left ss1) ss2 = ss-left (ssplit-append _ _ ss1 ss2)
ssplit-append _ _ (ss-right ss1) ss2 = ss-right (ssplit-append _ _ ss1 ss2)
ssplit-append _ _ (ss-posneg ss1) ss2 = ss-posneg (ssplit-append _ _ ss1 ss2)
ssplit-append _ _ (ss-negpos ss1) ss2 = ss-negpos (ssplit-append _ _ ss1 ss2)

-- weakening #1
weaken1-cr : ∀ {G b s} G' → ChannelRef G b s → ChannelRef (inactive-clone G' ++ G) b s
weaken1-cr [] cr = cr
weaken1-cr (x ∷ G') cr = there (weaken1-cr G' cr)

weaken1-val : ∀ {G t} G' → Val G t → Val (inactive-clone G' ++ G) t
weaken1-venv : ∀ {G Φ} G' → VEnv G Φ → VEnv (inactive-clone G' ++ G) Φ

weaken1-val G' (VUnit inaG) = VUnit (inactive-extension inaG G')
weaken1-val G' (VInt i inaG) = VInt i (inactive-extension inaG G')
weaken1-val G' (VPair ss-GG₁G₂ v v₁) = VPair (splitting-extension G' ss-GG₁G₂) (weaken1-val G' v) (weaken1-val G' v₁)
weaken1-val G' (VChan b vcr) = VChan b (weaken1-cr G' vcr)
weaken1-val G' (VFun x ϱ e) = VFun x (weaken1-venv G' ϱ) e
weaken1-venv G' (vnil ina) = vnil (inactive-extension ina G')
weaken1-venv G' (vcons ssp v ϱ) = vcons (splitting-extension G' ssp) (weaken1-val G' v) (weaken1-venv G' ϱ)

weaken1-cont : ∀ {G t φ} G' → Cont G φ t → Cont (inactive-clone G' ++ G) φ t
weaken1-cont G' (halt inaG un-t) = halt (inactive-extension inaG G') un-t
weaken1-cont G' (bind ts ss e₂ ϱ₂ κ) = bind ts (splitting-extension G' ss) e₂ (weaken1-venv G' ϱ₂) (weaken1-cont G' κ)
weaken1-cont G' (bind-thunk ts ss e₂ ϱ₂ κ) = bind-thunk ts (splitting-extension G' ss) e₂ (weaken1-venv G' ϱ₂) (weaken1-cont G' κ)
weaken1-cont G' (subsume x κ) = subsume x (weaken1-cont G' κ)

weaken1-command : ∀ {G} G' → Command G → Command (inactive-clone G' ++ G)
weaken1-command G' (Fork ss κ₁ κ₂) = Fork (splitting-extension G' ss) (weaken1-cont G' κ₁) (weaken1-cont G' κ₂)
weaken1-command G' (Ready ss v κ) = Ready (splitting-extension G' ss) (weaken1-val G' v) (weaken1-cont G' κ)
weaken1-command G' (Halt x x₁ x₂) = Halt (inactive-extension x G') x₁ (weaken1-val G' x₂)
weaken1-command G' (New s κ) = New s (weaken1-cont G' κ)
weaken1-command G' (Close ss v κ) = Close (splitting-extension G' ss) (weaken1-val G' v) (weaken1-cont G' κ)
weaken1-command G' (Wait ss v κ) = Wait (splitting-extension G' ss) (weaken1-val G' v) (weaken1-cont G' κ)
weaken1-command G' (Send ss ss-args vch v κ) = Send (splitting-extension G' ss) (splitting-extension G' ss-args) (weaken1-val G' vch) (weaken1-val G' v) (weaken1-cont G' κ)
weaken1-command G' (Recv ss vch κ) = Recv (splitting-extension G' ss) (weaken1-val G' vch) (weaken1-cont G' κ)
weaken1-command G' (Select ss lab vch κ) = Select (splitting-extension G' ss) lab (weaken1-val G' vch) (weaken1-cont G' κ)
weaken1-command G' (Branch ss vch dcont) = Branch (splitting-extension G' ss) (weaken1-val G' vch) λ lab → weaken1-cont G' (dcont lab)
weaken1-command G' (NSelect ss lab vch κ) = NSelect (splitting-extension G' ss) lab (weaken1-val G' vch) (weaken1-cont G' κ)
weaken1-command G' (NBranch ss vch dcont) = NBranch (splitting-extension G' ss) (weaken1-val G' vch) λ lab → weaken1-cont G' (dcont lab)

weaken1-threadpool : ∀ {G} G' → ThreadPool G → ThreadPool (inactive-clone G' ++ G)
weaken1-threadpool G' (tnil ina) = tnil (inactive-extension ina G')
weaken1-threadpool G' (tcons ss cmd tp) = tcons (splitting-extension G' ss) (weaken1-command G' cmd) (weaken1-threadpool G' tp)

-- auxiliary

inactive-insertion : ∀ {G} G' G'' → Inactive (G' ++ G) → Inactive (G' ++ inactive-clone G'' ++ G)
inactive-insertion [] G'' ina-G'G = inactive-extension ina-G'G G''
inactive-insertion (just x ∷ G') G'' ()
inactive-insertion (nothing ∷ G') G'' (::-inactive ina-G'G) = ::-inactive (inactive-insertion G' G'' ina-G'G)

splitting-insertion : ∀ {G G₁ G₂} {G' G₁' G₂'} G''
  → SSplit G' G₁' G₂'
  → SSplit G G₁ G₂
  → SSplit (G' ++ inactive-clone G'' ++ G) (G₁' ++ inactive-clone G'' ++ G₁) (G₂' ++ inactive-clone G'' ++ G₂)
splitting-insertion G'' ss-[] ss = splitting-extension G'' ss
splitting-insertion G'' (ss-both ss') ss = ss-both (splitting-insertion G'' ss' ss)
splitting-insertion G'' (ss-left ss') ss = ss-left (splitting-insertion G'' ss' ss)
splitting-insertion G'' (ss-right ss') ss = ss-right (splitting-insertion G'' ss' ss)
splitting-insertion G'' (ss-posneg ss') ss = ss-posneg (splitting-insertion G'' ss' ss)
splitting-insertion G'' (ss-negpos ss') ss = ss-negpos (splitting-insertion G'' ss' ss)

split-append : ∀ {G G1 G2} G' 
  → SSplit (G' ++ G) G1 G2
  → ∃ λ G₁' → ∃ λ G₂' → ∃ λ G₁ → ∃ λ G₂
  → SSplit G' G₁' G₂' × SSplit G G₁ G₂ × G1 ≡ G₁' ++ G₁ × G2 ≡ G₂' ++ G₂
split-append [] ss = _ , _ , _ , _ , ss-[] , ss , refl , refl
split-append (.nothing ∷ G') (ss-both ss) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = _ , _ , _ , _ , (ss-both ss') , ss0 , refl , refl
split-append (.(just _) ∷ G') (ss-left ss) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = _ , _ , _ , _ , (ss-left ss') , ss0 , refl , refl
split-append (.(just _) ∷ G') (ss-right ss) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = _ , _ , _ , _ , (ss-right ss') , ss0 , refl , refl
split-append (.(just (_ , POSNEG)) ∷ G') (ss-posneg ss) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = _ , _ , _ , _ , (ss-posneg ss') , ss0 , refl , refl
split-append (.(just (_ , POSNEG)) ∷ G') (ss-negpos ss) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = _ , _ , _ , _ , (ss-negpos ss') , ss0 , refl , refl

-- weakening #2

weaken2-cr : ∀ {G b s} G' G'' → ChannelRef (G' ++ G) b s → ChannelRef (G' ++ inactive-clone G'' ++ G) b s
weaken2-cr [] G'' cr = weaken1-cr G'' cr
weaken2-cr (.(just (_ , POS)) ∷ G') G'' (here-pos ina-G x) = here-pos (inactive-insertion G' G'' ina-G) x
weaken2-cr (.(just (_ , NEG)) ∷ G') G'' (here-neg ina-G x) = here-neg (inactive-insertion G' G'' ina-G) x
weaken2-cr (.nothing ∷ G') G'' (there cr) = there (weaken2-cr G' G'' cr)

weaken2-val : ∀ {G t} G' G'' → Val (G' ++ G) t → Val (G' ++ inactive-clone G'' ++ G) t
weaken2-venv : ∀ {G Φ} G' G'' → VEnv (G' ++ G) Φ → VEnv (G' ++ inactive-clone G'' ++ G) Φ

weaken2-val G' G'' (VUnit inaG) = VUnit (inactive-insertion G' G'' inaG)
weaken2-val G' G'' (VInt i inaG) = VInt i (inactive-insertion G' G'' inaG)
weaken2-val G' G'' (VPair ss-GG₁G₂ v₁ v₂) with split-append G' ss-GG₁G₂
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = VPair (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' v₁) (weaken2-val G₂' G'' v₂)
weaken2-val G' G'' (VChan b vcr) = VChan b (weaken2-cr G' G'' vcr)
weaken2-val G' G'' (VFun x ϱ e) = VFun x (weaken2-venv G' G'' ϱ) e

weaken2-venv G' G'' (vnil ina) = vnil (inactive-insertion G' G'' ina)
weaken2-venv G' G'' (vcons{G₁ = Gv}{G₂ = Gϱ} ssp v ϱ) with split-append G' ssp
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = vcons (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' v) (weaken2-venv G₂' G'' ϱ)

weaken2-cont : ∀ {G t φ} G' G'' → Cont (G' ++ G) φ t → Cont (G' ++ inactive-clone G'' ++ G) φ t
weaken2-cont G' G'' (halt x un-t) = halt (inactive-insertion G' G'' x) un-t
weaken2-cont G' G'' (bind ts ss e₂ ϱ₂ κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = bind ts (splitting-insertion G'' ss' ss0) e₂ (weaken2-venv G₁' G'' ϱ₂) (weaken2-cont G₂' G'' κ)
weaken2-cont G' G'' (bind-thunk ts ss e₂ ϱ₂ κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = bind-thunk ts (splitting-insertion G'' ss' ss0) e₂ (weaken2-venv G₁' G'' ϱ₂) (weaken2-cont G₂' G'' κ)
weaken2-cont G' G'' (subsume x κ) = subsume x (weaken2-cont G' G'' κ)

weaken2-command : ∀ {G} G' G'' → Command (G' ++ G) → Command (G' ++ inactive-clone G'' ++ G)
weaken2-command G' G'' (Fork ss κ₁ κ₂) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = Fork (splitting-insertion G'' ss' ss0) (weaken2-cont G₁' G'' κ₁) (weaken2-cont G₂' G'' κ₂)
weaken2-command G' G'' (Ready ss v κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = Ready (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' v) (weaken2-cont G₂' G'' κ)
weaken2-command G' G'' (Halt x x₁ x₂) = Halt (inactive-insertion G' G'' x) x₁ (weaken2-val G' G'' x₂)
weaken2-command G' G'' (New s κ) = New s (weaken2-cont G' G'' κ)
weaken2-command G' G'' (Close ss v κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = Close (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' v) (weaken2-cont G₂' G'' κ)
weaken2-command G' G'' (Wait ss v κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = Wait (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' v) (weaken2-cont G₂' G'' κ)
weaken2-command G' G'' (Send ss ss-args vch v κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl with split-append G₁' ss-args
... | G₁₁' , G₁₂' , G₁₁ , G₁₂ , ss-args' , ss0-args , refl , refl = Send (splitting-insertion G'' ss' ss0) (splitting-insertion G'' ss-args' ss0-args) (weaken2-val G₁₁' G'' vch) (weaken2-val G₁₂' G'' v) (weaken2-cont G₂' G'' κ)
weaken2-command G' G'' (Recv ss vch κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = Recv (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' vch) (weaken2-cont G₂' G'' κ)
weaken2-command G' G'' (Select ss lab vch κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = Select (splitting-insertion G'' ss' ss0) lab (weaken2-val G₁' G'' vch) (weaken2-cont G₂' G'' κ)
weaken2-command G' G'' (Branch ss vch dcont) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = Branch (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' vch) λ lab → weaken2-cont G₂' G'' (dcont lab)
weaken2-command G' G'' (NSelect ss lab vch κ) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = NSelect (splitting-insertion G'' ss' ss0) lab (weaken2-val G₁' G'' vch) (weaken2-cont G₂' G'' κ)
weaken2-command G' G'' (NBranch ss vch dcont) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = NBranch (splitting-insertion G'' ss' ss0) (weaken2-val G₁' G'' vch) λ lab → weaken2-cont G₂' G'' (dcont lab)

weaken2-threadpool : ∀ {G} G' G'' → ThreadPool (G' ++ G) → ThreadPool (G' ++ inactive-clone G'' ++ G)
weaken2-threadpool G' G'' (tnil ina) = tnil (inactive-insertion G' G'' ina)
weaken2-threadpool G' G'' (tcons ss cmd tp) with split-append G' ss
... | G₁' , G₂' , G₁ , G₂ , ss' , ss0 , refl , refl = tcons (splitting-insertion G'' ss' ss0) (weaken2-command G₁' G'' cmd) (weaken2-threadpool G₂' G'' tp)


-- translate a process term to semantics (i.e., a list of commands)
runProc : ∀ {Φ} → (G : SCtx) → Proc Φ → VEnv G Φ → ∃ λ G' → ThreadPool (G' ++ G)

runProc G (exp e) ϱ with ssplit-refl-left-inactive G
... | G' , ina-G' , sp-GGG' = [] , (tcons sp-GGG' (run (split-all-left _) sp-GGG' e ϱ (halt ina-G' UUnit)) (tnil ina-G'))

runProc G (par sp P₁ P₂) ϱ with split-env sp ϱ
... | (G₁ , G₂) , ss-GG1G2 , ϱ₁ , ϱ₂ with runProc G₁ P₁ ϱ₁ | runProc G₂ P₂ ϱ₂
... | (G₁' , tp1) | (G₂' , tp2) with weaken1-threadpool G₁' tp2
... | tp2' with weaken2-threadpool G₁' G₂' tp1
... | tp1' with left-right G₁' G₂'
... | ss-G1'G2' rewrite sym (list-assoc G₁' (inactive-clone G₂') G₁) | sym (list-assoc (inactive-clone G₁') G₂' G₂) = (G₁' ++ G₂') , tappend ssfinal tp1' tp2'
  where
    ssfinal : SSplit ((G₁' ++ G₂') ++ G) ((G₁' ++ inactive-clone G₂') ++ G₁) ((inactive-clone G₁' ++ G₂') ++ G₂)
    ssfinal = ssplit-append (G₁' ++ G₂') G ss-G1'G2' ss-GG1G2

runProc G (res s P) ϱ with ssplit-refl-right-inactive G
... | G1 , ina-G1 , ss-GG1G with runProc (just (SType.force s , POSNEG) ∷ G) P (vcons (ss-posneg ss-GG1G) (VChan POS (here-pos ina-G1 (subF-refl _))) (vcons (ss-left ss-GG1G) (VChan NEG (here-neg ina-G1 (subF-refl _))) (lift-venv ϱ)))
... | G' , tp = G' ++ just (SType.force s , POSNEG) ∷ [] , tp'
  where
    tp' : ThreadPool ((G' ++ just (SType.force s , POSNEG) ∷ []) ++ G)
    tp' rewrite list-assoc G' (just (SType.force s , POSNEG) ∷ []) G = tp


startProc : Gas → Proc [] → Outcome
startProc f P with runProc [] P (vnil []-inactive)
... | G , tp = schedule f tp

