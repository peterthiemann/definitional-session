module Progress where

open import Data.Bool
open import Data.Empty
open import Data.Maybe hiding (Any ; All)
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Product
open import Data.Unit

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

-- resources appear in pairs
data Paired : SEntry → Set where
  aon-nothing : Paired nothing
  aon-all : ∀ {s} → Paired (just (s , POSNEG))

-- need lemmas for matchXAndGo ...
-- matchXandGo-preserves-paired


matchWaitAndGo-preserves-paired : 
  ∀ {G G₁ G₂  G₁₁ G₁₂ φ G₂₁ G₂₂ Gnext tpnext} 
    {ss : SSplit G G₁ G₂}
    {ss-cl : SSplit G₁ G₁₁ G₁₂}
    {v : Val G₁₁ (TChan send!)}
    {cl-κ : Cont G₁₂ φ TUnit}
    {ss-GG' : SSplit G₂ G₂₁ G₂₂}
  → All Paired G
  → (tp' : ThreadPool G₂₁) 
  → (tp'' : ThreadPool G₂₂)
  → matchWaitAndGo ss (ss-cl , v , cl-κ) ss-GG' tp' tp'' ≡ just (Gnext , tpnext)
  → All Paired Gnext
matchWaitAndGo-preserves-paired all-paired (tnil ina) tp'' ()
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Fork ss₁ κ₁ κ₂) tp') tp'' match-≡
  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Ready ss₁ v κ) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Halt x x₁ x₂) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(New s κ) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Close ss₁ v κ) tp') tp'' match-≡ with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Send ss₁ ss-args vch v κ) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Recv ss₁ vch κ) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Select ss₁ lab vch κ) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Branch ss₁ vch dcont) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(NSelect ss₁ lab vch κ) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(NBranch ss₁ vch dcont) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp' (tcons ss' cmd tp'') match-≡
matchWaitAndGo-preserves-paired {ss = ss-top} {ss-cl = ss-cl} {v = VChan cl-b cl-vcr} {ss-GG' =  ss-tp}
  all-paired (tcons ss cmd@(Wait ss₁ (VChan w-b w-vcr) κ) tp-wl) tp-acc match-≡
  with ssplit-compose6 ss ss₁
... | Gi , ss-g3gi , ss-g4g2
  with ssplit-compose6 ss-tp ss-g3gi
... | Gi' , ss-g3gi' , ss-gtpacc
  with ssplit-join ss-top ss-cl ss-g3gi'
... | Gchannels , Gother , ss-top' , ss-channels , ss-others
   with vcr-match ss-channels cl-vcr w-vcr
matchWaitAndGo-preserves-paired {ss = ss-top} {ss-cl} {VChan cl-b cl-vcr} {ss-GG' = ss-tp} all-paired (tcons ss cmd@(Wait ss₁ (VChan w-b w-vcr) κ) tp-wl) tp-acc match-≡ | Gi , ss-g3gi , ss-g4g2 | Gi' , ss-g3gi' , ss-gtpacc | Gchannels , Gother , ss-top' , ss-channels , ss-others | nothing with ssplit-compose5 ss-tp ss
... | _ , ss-tp' , ss' =
  matchWaitAndGo-preserves-paired all-paired tp-wl (tcons ss' cmd tp-acc) match-≡
matchWaitAndGo-preserves-paired {ss = ss-top} {ss-cl} {VChan cl-b cl-vcr} {ss-GG' = ss-tp} all-paired (tcons ss cmd@(Wait ss₁ (VChan w-b w-vcr) κ) tp-wl) tp-acc refl | Gi , ss-g3gi , ss-g4g2 | Gi' , ss-g3gi' , ss-gtpacc | Gchannels , Gother , ss-top' , ss-channels , ss-others | just x = {!!}
-- remains to prove All Paired Gother

step-preserves-paired : ∀ {G G' ev tp'} → All Paired G → (tp : ThreadPool G) → Original.step tp ≡ (_,_ {G'} ev tp') → All Paired G'
step-preserves-paired all-paired tp step-≡ with tp
step-preserves-paired all-paired tp refl | tnil ina = all-paired
step-preserves-paired all-paired tp refl | tcons ss (Fork ss₁ κ₁ κ₂) tp' = all-paired
step-preserves-paired all-paired tp refl | tcons ss (Ready ss₁ v κ) tp' = all-paired
step-preserves-paired all-paired tp step-≡ | tcons ss (Halt x x₁ x₂) tp' with inactive-left-ssplit ss x
step-preserves-paired all-paired tp refl | tcons ss (Halt x x₁ x₂) tp' | refl = all-paired
step-preserves-paired all-paired tp refl | tcons ss (New s κ) tp' = aon-all ∷ all-paired
step-preserves-paired all-paired tp step-≡ | tcons{G₁}{G₂} ss (Close ss-vκ v κ) tp'
  with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG'
  with matchWaitAndGo ss (ss-vκ , v , κ) ss-GG' tp' (tnil ina-G')
step-preserves-paired all-paired tp refl | tcons {G₁} {G₂} ss (Close ss-vκ v κ) tp' | G' , ina-G' , ss-GG' | just (Gnext , tpnext) = matchWaitAndGo-preserves-paired {ss = ss}{ss-cl = ss-vκ}{v = v}{cl-κ = κ}{ss-GG'} all-paired tp' (tnil ina-G') p
  where
    p : matchWaitAndGo ss (ss-vκ , v , κ) ss-GG' tp' (tnil ina-G') ≡ just (Gnext , tpnext)
    p = sym {!refl!}
step-preserves-paired all-paired tp refl | tcons {G₁} {G₂} ss (Close ss-vκ v κ) tp' | G' , ina-G' , ss-GG' | nothing = all-paired
step-preserves-paired all-paired tp refl | tcons ss (Wait ss₁ v κ) tp' = all-paired
step-preserves-paired all-paired tp refl | tcons ss (Send ss₁ ss-args vch v κ) tp' = all-paired
step-preserves-paired all-paired tp step-≡ | tcons{G₁}{G₂} ss (Recv ss-vκ vch κ) tp' with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' with matchSendAndGo ss (ss-vκ , vch , κ) ss-GG' tp' (tnil ina-G')
... | just (G-next , tp-next) = {!!}
step-preserves-paired all-paired tp refl | tcons {G₁} {G₂} ss (Recv ss-vκ vch κ) tp' | G' , ina-G' , ss-GG' | nothing = all-paired
step-preserves-paired all-paired tp step-≡ | tcons{G₁}{G₂} ss (Select ss-vκ lab vch κ) tp' with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' with matchBranchAndGo ss (ss-vκ , lab , vch , κ) ss-GG' tp' (tnil ina-G')
... | just (G-next , tp-next) = {!!}
step-preserves-paired all-paired tp refl | tcons {G₁} {G₂} ss (Select ss-vκ lab vch κ) tp' | G' , ina-G' , ss-GG' | nothing = all-paired
step-preserves-paired all-paired tp refl | tcons ss (Branch ss₁ vch dcont) tp' = all-paired
step-preserves-paired all-paired tp step-≡ | tcons{G₁}{G₂} ss (NSelect ss-vκ lab vch κ) tp' with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' with matchNBranchAndGo ss (ss-vκ , lab , vch , κ) ss-GG' tp' (tnil ina-G')
... | just (G-next , tp-next) = {!!}
step-preserves-paired all-paired tp refl | tcons {G₁} {G₂} ss (NSelect ss-vκ lab vch κ) tp' | G' , ina-G' , ss-GG' | nothing = all-paired
step-preserves-paired all-paired tp refl | tcons ss (NBranch ss₁ vch dcont) tp' = all-paired


-- check if the first thread can make a step
topCanStep : ∀ {G} → ThreadPool G → Set
topCanStep (tnil ina) = ⊥
topCanStep (tcons ss (Fork ss₁ κ₁ κ₂) tp) = ⊤
topCanStep (tcons ss (Ready ss₁ v κ) tp) = ⊤
topCanStep (tcons ss (Halt x x₁ x₂) tp) = ⊤
topCanStep (tcons ss (New s κ) tp) = ⊤
topCanStep (tcons{G₁}{G₂} ss (Close ss-vκ v κ) tp) with ssplit-refl-left-inactive G₂
... |  G' , ina-G' , ss-GG' = Is-just (matchWaitAndGo ss (ss-vκ , v , κ) ss-GG' tp (tnil ina-G'))
topCanStep (tcons ss (Wait ss₁ v κ) tp) = ⊥
topCanStep (tcons ss (Send ss₁ ss-args vch v κ) tp) = ⊥
topCanStep (tcons{G₁}{G₂} ss (Recv ss-vκ vch κ) tp) with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' = Is-just (matchSendAndGo ss (ss-vκ , vch , κ) ss-GG' tp (tnil ina-G'))
topCanStep (tcons{G₁}{G₂} ss (Select ss-vκ lab vch κ) tp) with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' = Is-just (matchBranchAndGo ss (ss-vκ , lab , vch , κ) ss-GG' tp (tnil ina-G'))
topCanStep (tcons ss (Branch ss₁ vch dcont) tp) = ⊥
topCanStep (tcons{G₁}{G₂} ss (NSelect ss-vκ lab vch κ) tp) with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' = Is-just (matchNBranchAndGo ss (ss-vκ , lab , vch , κ) ss-GG' tp (tnil ina-G'))
topCanStep (tcons ss (NBranch ss₁ vch dcont) tp) = ⊥


tpLength : ∀ {G} → ThreadPool G → ℕ
tpLength (tnil ina) = 0
tpLength (tcons ss cmd tp) = suc (tpLength tp)

allRotations : ∀ {G} → ThreadPool G → List (ThreadPool G)
allRotations tp = nRotations (tpLength tp) tp
  where
    rotate : ∀ {G} → ThreadPool G → ThreadPool G
    rotate (tnil ina) = tnil ina
    rotate (tcons ss cmd tp) = tsnoc ss tp cmd
    nRotations : ∀ {G} ℕ → ThreadPool G → List (ThreadPool G)
    nRotations zero tp = []
    nRotations (suc n) tp = tp ∷ nRotations n (rotate tp)

-- the thread pool can step if any command in the pool can make a step
canStep : ∀ {G} → ThreadPool G → Set
canStep tp = Any topCanStep (allRotations tp)

deadlocked : ∀ {G} → ThreadPool G → Set
deadlocked (tnil ina) = ⊥
deadlocked tp@(tcons _ _ _) = ¬ canStep tp

-- progress
