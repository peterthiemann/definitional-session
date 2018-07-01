module Properties where

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
matchWaitAndGo-preserves-paired {ss-GG' =  ss-GG'} all-paired (tcons ss cmd@(Stopped ss₁ v κ) tp') tp'' match-≡  with ssplit-compose5 ss-GG' ss
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
step-preserves-paired all-paired tp refl | tcons ss (Stopped ss₁ v κ) tp' = all-paired
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
topCanStep (tcons ss (Stopped ss₁ v κ) tp) = ⊤
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

-- adequacy

one-step : ∀ {G} → (∃ λ G' → ThreadPool (G' ++ G)) → Event × (∃ λ G → ThreadPool G)
one-step{G} (G1 , tp)
  with ssplit-refl-left-inactive (G1 ++ G)
... | G' , ina-G' , ss-GG'
  with Alternative.step ss-GG' tp (tnil ina-G')
... | ev , tp' = ev , ( , tp')



-- V: letpair (x,y) = (V,W) in E --> E[ V,W / x,y ]

-- P: <E[fork e]> --> <E[()]> | <e>
module StepFork where

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
    = {!!}

-- P: <E[new s]> --> (vcd) <E[(c,d)]>
module StepNew where
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

-- P: (vcd) <E[send c v]> | <F[rec d]>  --> (vcd) <E[c]> | <F[(d,v)]>

-- P: (vcd) <E[close c]> | <F[wait d]>  --> (vcd) <E[()]> | <F[()]>
module StepCloseWait where

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