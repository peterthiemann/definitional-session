module Schedule where

open import Data.Bool
open import Data.Fin
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (_$_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global
open import Channel
open import Values
open import Session

-- outcomes of step
data Event : Set where
  Terminated Forked Restarted Halted New Closed NotClosed WaitSkipped : Event
  SendSkipped Received NotReceived : Event
  Stuck : Event
  Selected NotSelected : Event
  NSelected NotNSelected BranchSkipped NBranchSkipped : Event

data NextPool : Set where
  _,_ : ∀ {G} → Event → ThreadPool G → NextPool

module Alternative where
  step : ∀ {Gtop G1 G2} → SSplit Gtop G1 G2 → ThreadPool G1 → ThreadPool G2 → NextPool
  step ss-top (tnil ina) tp2@(tnil _) = Terminated , tp2

  step ss-top (tnil ina) tp2 = Stuck , tp2

  step ss-top (tcons ss (Fork{G₁ = G₁}{G₂ = G₂} ss₁ κ₁ κ₂) tp) tp2
    with ssplit-compose ss ss₁
  ... | Gi , ss₁₃ , ss₂₄ with ssplit-refl-right G₁ | ssplit-refl-right G₂
  ... | Gunit , ss-G1GunitG1 | G2unit , ss-G2GuG2 =
    Forked , (tappend ss-top ((tcons ss₁₃ (apply-cont ss-G1GunitG1 κ₁ (VUnit (ssplit-inactive-right ss-G1GunitG1)))
                             (tcons ss₂₄ (Ready ss-G2GuG2 (VUnit (ssplit-inactive-right ss-G2GuG2)) κ₂) tp))) tp2)

  step ss-top (tcons ss (Ready ss₁ v κ) tp) tp2 =
    Restarted , (tappend ss-top (tsnoc ss tp (apply-cont ss₁ κ v)) tp2)

  step ss-top (tcons ss (Halt inaG x₁ x₂) tp) tp2
    rewrite inactive-left-ssplit ss inaG = Halted , (tappend ss-top tp tp2)

  step ss-top (tcons{G₁} ss (New s κ) tp) tp2
    with ssplit-refl-right G₁
  ... | Gi , ss-GiG1
    with ssplit-inactive-right ss-GiG1
  ... | ina-Gi = New , (tappend (ss-left ss-top) ((tcons (ss-left ss)
           (Ready (ss-left ss-GiG1) (VPair (ss-posneg (inactive-ssplit-trivial ina-Gi)) (VChan POS (here-pos ina-Gi (subF-refl _))) (VChan NEG (here-neg ina-Gi (subF-refl _)))) (lift-cont κ))
           (lift-threadpool tp))) (lift-threadpool tp2))

  step ss-top (tcons{G₁}{G₂} ss cmd@(Close ss-vκ v κ) tp) tp2
    with ssplit-compose ss-top ss
  ... | Gi , ss-top1 , ss-top2
    with ssplit-refl-left-inactive Gi
  ... | G' , ina-G' , ss-GG'
    with matchWaitAndGo ss-top1 (ss-vκ , v , κ) ss-GG' (tappend ss-top2 tp tp2) (tnil ina-G')
  ... | just (Gnext , tpnext) = Closed , tpnext
  ... | nothing
    with ssplit-compose5 ss-top ss
  ... | Gi' , ss-top1' , ss-top2' = step ss-top1' tp (tsnoc ss-top2' tp2 cmd)

  step ss-top (tcons ss cmd@(Wait ss₁ v κ) tp) tp2
    with ssplit-compose5 ss-top ss
  ... | Gi , ss-top1 , ss-top2 =
    step ss-top1 tp (tsnoc ss-top2 tp2 cmd)

  step ss-top (tcons ss cmd@(Send ss₁ ss-args vch v κ) tp) tp2
    with ssplit-compose5 ss-top ss
  ... | Gi , ss-top1 , ss-top2 =
    step ss-top1 tp (tsnoc ss-top2 tp2 cmd)

  step ss-top (tcons{G₁}{G₂} ss cmd@(Recv ss-vκ vch κ) tp) tp2
    with ssplit-compose ss-top ss
  ... | Gi , ss-top1 , ss-top2 
    with ssplit-refl-left-inactive Gi
  ... | G' , ina-G' , ss-GG'
    with matchSendAndGo ss-top1 (ss-vκ , vch , κ) ss-GG' (tappend ss-top2 tp tp2) (tnil ina-G')
  ... | just (G-next , tp-next) = 
    Received , tp-next
  ... | nothing
    with ssplit-compose5 ss-top ss
  ... | Gi' , ss-top1' , ss-top2' =
    step ss-top1' tp (tsnoc ss-top2' tp2 cmd)

  step ss-top (tcons{G₁}{G₂} ss cmd@(Select ss-vκ lab vch κ) tp) tp2
    with ssplit-compose ss-top ss
  ... | Gi , ss-top1 , ss-top2
    with ssplit-refl-left-inactive Gi
  ... | G' , ina-G' , ss-GG' 
    with matchBranchAndGo ss-top1 (ss-vκ , lab , vch , κ) ss-GG' (tappend ss-top2 tp tp2) (tnil ina-G')
  ... | just (G-next , tp-next) = 
    Selected , tp-next
  ... | nothing
    with ssplit-compose5 ss-top ss
  ... | Gi' , ss-top1' , ss-top2' =
    step ss-top1' tp (tsnoc ss-top2' tp2 cmd)

  step ss-top (tcons ss cmd@(Branch ss₁ vch dcont) tp) tp2
    with ssplit-compose5 ss-top ss
  ... | Gi , ss-top1 , ss-top2 =
    step ss-top1 tp (tsnoc ss-top2 tp2 cmd)

  step ss-top (tcons{G₁}{G₂} ss cmd@(NSelect ss-vκ lab vch κ) tp) tp2
    with ssplit-compose ss-top ss
  ... | Gi , ss-top1 , ss-top2 
    with ssplit-refl-left-inactive Gi
  ... | G' , ina-G' , ss-GG' 
    with matchNBranchAndGo ss-top1 (ss-vκ , lab , vch , κ) ss-GG' (tappend ss-top2 tp tp2) (tnil ina-G')
  ... | just (G-next , tp-next) = NSelected , tp-next
  ... | nothing
    with ssplit-compose5 ss-top ss
  ... | Gi' , ss-top1' , ss-top2' = 
    step ss-top1' tp (tsnoc ss-top2' tp2 cmd)

  step ss-top (tcons ss cmd@(NBranch ss₁ vch dcont) tp) tp2
    with ssplit-compose5 ss-top ss
  ... | Gi , ss-top1 , ss-top2 =
    step ss-top1 tp (tsnoc ss-top2 tp2 cmd)

module Original where
  step : ∀ {G} → ThreadPool G → NextPool
  step (tnil ina) =
    Terminated , tnil ina
  step (tcons ss (Fork{G₁ = G₁}{G₂ = G₂} ss₁ κ₁ κ₂) tp) with ssplit-compose ss ss₁
  ... | Gi , ss₁₃ , ss₂₄ with ssplit-refl-right G₁ | ssplit-refl-right G₂
  ... | Gunit , ss-G1GunitG1 | G2unit , ss-G2GuG2 =
    Forked , (tcons ss₁₃ (apply-cont ss-G1GunitG1 κ₁ (VUnit (ssplit-inactive-right ss-G1GunitG1)))
                    (tcons ss₂₄ (apply-cont ss-G2GuG2 κ₂ (VUnit (ssplit-inactive-right ss-G2GuG2))) tp))
  step (tcons ss (Ready ss₁ v κ) tp) =
    Restarted , (tsnoc ss tp (apply-cont ss₁ κ v))
  step (tcons ss (Halt inaG x₁ x₂) tp) rewrite inactive-left-ssplit ss inaG =
    Halted , tp
  step (tcons{G₁} ss (New s κ) tp) with ssplit-refl-right G₁
  ... | Gi , ss-GiG1 with ssplit-inactive-right ss-GiG1
  ... | ina-Gi =
    New , (tcons (ss-left ss)
             (apply-cont (ss-left ss-GiG1) (lift-cont κ) (VPair (ss-posneg (inactive-ssplit-trivial ina-Gi)) (VChan POS (here-pos ina-Gi (subF-refl _))) (VChan NEG (here-neg ina-Gi (subF-refl _)))))
             (lift-threadpool tp))
  step (tcons{G₁}{G₂} ss cmd@(Close ss-vκ v κ) tp) with ssplit-refl-left-inactive G₂
  ... | G' , ina-G' , ss-GG' with matchWaitAndGo ss (ss-vκ , v , κ) ss-GG' tp (tnil ina-G')
  ... | just (Gnext , tpnext) = Closed , tpnext
  ... | nothing = NotClosed , (tsnoc ss tp cmd)
  step (tcons ss cmd@(Wait ss₁ v κ) tp) =
    WaitSkipped , (tsnoc ss tp cmd)
  step (tcons ss cmd@(Send ss₁ ss-args vch v κ) tp) =
    SendSkipped , (tsnoc ss tp cmd)
  step (tcons{G₁}{G₂} ss cmd@(Recv ss-vκ vch κ) tp) with ssplit-refl-left-inactive G₂
  ... | G' , ina-G' , ss-GG' with matchSendAndGo ss (ss-vκ , vch , κ) ss-GG' tp (tnil ina-G')
  ... | just (G-next , tp-next) = Received , tp-next
  ... | nothing = NotReceived , (tsnoc ss tp cmd)
  step (tcons{G₁}{G₂} ss cmd@(Select ss-vκ lab vch κ) tp) with ssplit-refl-left-inactive G₂
  ... | G' , ina-G' , ss-GG' with matchBranchAndGo ss (ss-vκ , lab , vch , κ) ss-GG' tp (tnil ina-G')
  ... | just (G-next , tp-next) = Selected , tp-next
  ... | nothing = NotSelected , (tsnoc ss tp cmd)
  step (tcons ss cmd@(Branch ss-vκ vch dcont) tp) =
    BranchSkipped , (tsnoc ss tp cmd)
  step (tcons{G₁}{G₂} ss cmd@(NSelect ss-vκ lab vch κ) tp) with ssplit-refl-left-inactive G₂
  ... | G' , ina-G' , ss-GG' with matchNBranchAndGo ss (ss-vκ , lab , vch , κ) ss-GG' tp (tnil ina-G')
  ... | just (G-next , tp-next) = NSelected , tp-next
  ... | nothing = NotNSelected , (tsnoc ss tp cmd)
  step (tcons ss cmd@(NBranch ss-vκ vch dcont) tp) =
    NBranchSkipped , (tsnoc ss tp cmd)

open Alternative

single-step : (∃ λ G → ThreadPool G) → Event × (∃ λ G → ThreadPool G)
single-step (G , tp)
  with ssplit-refl-left-inactive G
... | G' , ina-G' , ss-GG'
  with step ss-GG' tp (tnil ina-G')
... | ev , tp' = ev , ( _ , tp')

-- stuff to run ...
data Gas : Set where
  Empty : Gas
  More  : Gas → Gas

-- outcomes of scheduling
data Outcome : Set where
  Terminated : Outcome
  _,_ : Event → Outcome → Outcome
  OutOfGas : ∀ {G} → ThreadPool G → Outcome

-- thread scheduling
schedule : {G : SCtx} → Gas → ThreadPool G → Outcome
schedule Empty tp = OutOfGas tp
schedule{G} (More gas) tp
  with single-step (_ , tp)
... | Terminated , _ , tp' = Terminated
... | ev , _ , tp' = ev , (schedule gas tp')

-- start main thread
start : Gas → Expr [] TUnit → Outcome
start f e =
  schedule f (tcons ss-[] (run [] ss-[] e (vnil []-inactive) (halt []-inactive UUnit)) (tnil []-inactive))
