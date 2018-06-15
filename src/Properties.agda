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

-- resources appear in pairs
data Paired : SEntry → Set where
  aon-nothing : Paired nothing
  aon-all : ∀ {s} → Paired (just (s , POSNEG))

-- need lemmas for matchXAndGo ...
-- matchXandGo-preserves-paired

step-preserves-paired : ∀ {G G' ev tp'} → All Paired G → (tp : ThreadPool G) → step tp ≡ (_,_ {G'} ev tp') → All Paired G'
step-preserves-paired all-paired tp step-≡ with tp
step-preserves-paired all-paired tp refl | tnil ina = all-paired
step-preserves-paired all-paired tp refl | tcons ss (Fork ss₁ κ₁ κ₂) tp' = all-paired
step-preserves-paired all-paired tp refl | tcons ss (Stopped ss₁ v κ) tp' = all-paired
step-preserves-paired all-paired tp step-≡ | tcons ss (Halt x x₁ x₂) tp' with inactive-left-ssplit ss x
step-preserves-paired all-paired tp refl | tcons ss (Halt x x₁ x₂) tp' | refl = all-paired
step-preserves-paired all-paired tp refl | tcons ss (New s κ) tp' = aon-all ∷ all-paired
step-preserves-paired all-paired tp step-≡ | tcons{G₁}{G₂} ss (Close ss-vκ v κ) tp' with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' with matchWaitAndGo ss (ss-vκ , v , κ) ss-GG' tp' (tnil ina-G')
step-preserves-paired all-paired tp refl | tcons {G₁} {G₂} ss (Close ss-vκ v κ) tp' | G' , ina-G' , ss-GG' | just (Gnext , tpnext) = {!!}
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
