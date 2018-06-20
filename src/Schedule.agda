module Schedule where

open import Data.Bool
open import Data.Fin
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.Maybe hiding (All)
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
  SendSkipped Received NotReceived Selected NotSelected : Event
  NSelected NotNSelected BranchSkipped NBranchSkipped : Event

data NextPool : Set where
  _,_ : ∀ {G} → Event → ThreadPool G → NextPool

step : ∀ {G} → ThreadPool G → NextPool
step (tnil ina) =
  Terminated , tnil ina
step (tcons ss (Fork{G₁ = G₁}{G₂ = G₂} ss₁ κ₁ κ₂) tp) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ with ssplit-refl-right G₁ | ssplit-refl-right G₂
... | Gunit , ss-G1GunitG1 | G2unit , ss-G2GuG2 =
  Forked , (tcons ss₁₃ (apply-cont ss-G1GunitG1 κ₁ (VUnit (ssplit-inactive-right ss-G1GunitG1)))
                  (tcons ss₂₄ (apply-cont ss-G2GuG2 κ₂ (VUnit (ssplit-inactive-right ss-G2GuG2))) tp))
step (tcons ss (Stopped ss₁ v κ) tp) =
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

-- outcomes of scheduling
data Outcome : Set where
  Terminated : Outcome
  Action : Event → Outcome → Outcome
  OutOfGas : ∀ {G} → ThreadPool G → Outcome

-- thread scheduling
schedule : {G : SCtx} → Gas → ThreadPool G → Outcome
schedule Empty tp = OutOfGas tp
schedule (More gas) tp with step tp
... | Terminated , tp' = Terminated
... | ev , tp' = Action ev (schedule gas tp')

-- start main thread
start : Gas → Expr [] TUnit → Outcome
start f e =
  schedule f (tcons ss-[] (run [] ss-[] e (vnil []-inactive) (halt []-inactive UUnit)) (tnil []-inactive))
