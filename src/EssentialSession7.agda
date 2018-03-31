module EssentialSession7 where

open import Data.Bool
open import Data.Empty
-- open import Data.Fin hiding (_+_ ; _≤_)
open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Maybe hiding (All)
open import Data.Nat
open import Data.Product
open import Data.Unit hiding (_≤_)
-- open import Data.Vec hiding ( _∈_ ; _>>=_)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- open import Lemmas

open import Typing

-- expressions
data Expr : (φ : TCtx) → Ty → Set where
  var : ∀ {t φ}
      → (x : t ∈ φ)
      → Expr φ t

  nat : ∀ {φ}
      → All Unr φ
      → (i : ℕ)
      → Expr φ TInt

  letbind : ∀ {φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (e₁ : Expr φ₁ t₁)
    → (e₂ : Expr (t₁ ∷ φ₂) t₂)
    → Expr φ t₂

  pair : ∀ {φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (x₁ : t₁ ∈ φ₁)
    → (x₂ : t₂ ∈ φ₂)
    → Expr φ (TPair t₁ t₂)

  letpair : ∀ {φ φ₁ φ₂ t₁ t₂ t}
    → (sp : Split φ φ₁ φ₂)
    → (p : TPair t₁ t₂ ∈ φ₁)
    → (e : Expr (t₁ ∷ t₂ ∷ φ₂) t)
    → Expr φ t

  fork : ∀ { φ}
    → (e : Expr φ TUnit)
    → Expr φ TUnit

  new : ∀ {φ}
      → All Unr φ
      → (s : STy)
      → Expr φ (TPair (TChan s) (TChan (dual s)))
{-
  -- takes only variables to avoid extraneous effects
  send : ∀ {φ φ₁ φ₂ s t}
      → (sp : Split φ φ₁ φ₂)
      → (ch : (TChan (SSend t s)) ∈ φ₁)
      → (vv : t ∈ φ₂)
      → Expr φ (TChan s)
  -- takes only variables to avoid extraneous effects
  recv : ∀ {φ s t}
      → (ch : (TChan (SRecv t s)) ∈ φ)
      → Expr φ (TPair (TChan s) t)
-}
  close : ∀ { φ}
      → (ch : TChan SEnd! ∈ φ)
      → Expr φ TUnit

  wait : ∀ { φ}
      → (ch : TChan SEnd? ∈ φ)
      → Expr φ TUnit


-- global session context
SCtx = List (Maybe (STy × PosNeg))

-- SSplit G G₁ G₂
-- split G into G₁ and G₂
-- length and position preserving
data SSplit : SCtx → SCtx → SCtx → Set where
  ss-[]    : SSplit [] [] []
  ss-both  : ∀ {  G G₁ G₂ }
           → SSplit G G₁ G₂
           → SSplit (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂)
  ss-left  : ∀ { spn G G₁ G₂ }
           → SSplit G G₁ G₂
           → SSplit (just spn ∷ G) (just spn ∷ G₁) (nothing ∷ G₂)
  ss-right : ∀ { spn G G₁ G₂ }
           → SSplit G G₁ G₂
           → SSplit (just spn ∷ G) (nothing ∷ G₁) (just spn ∷ G₂)
  ss-posneg : ∀ {  s G G₁ G₂ }
          → SSplit G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , POS) ∷ G₁) (just (s , NEG) ∷ G₂)
  ss-negpos : ∀ {  s G G₁ G₂ }
          → SSplit G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , NEG) ∷ G₁) (just (s , POS) ∷ G₂)

-- tedious but easy to prove
ssplit-compose : (G G₁ G₂ G₃ G₄ : SCtx) 
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₁ G₃ G₄)
  → Σ SCtx λ Gi → SSplit G G₃ Gi × SSplit Gi G₄ G₂
ssplit-compose .[] .[] .[] .[] .[] ss-[] ss-[] =  [] , (ss-[] , ss-[])
ssplit-compose (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂) (nothing ∷ G₃) (nothing ∷ G₄) (ss-both ss) (ss-both ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
ssplit-compose (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂) (nothing ∷ G₃) (nothing ∷ G₄) (ss-both ss) (ss-both ss₁) | Gi , ss₁₃ , ss₂₄ = nothing ∷ Gi , ss-both ss₁₃ , ss-both ss₂₄
ssplit-compose (just _ ∷ G) (just _ ∷ G₁) (nothing ∷ G₂) (just _ ∷ G₃) (nothing ∷ G₄) (ss-left ss) (ss-left ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = nothing ∷ Gi , ss-left ss₁₃ , ss-both ss₂₄
ssplit-compose (just x ∷ G) (just _ ∷ G₁) (nothing ∷ G₂) (nothing ∷ G₃) (just _ ∷ G₄) (ss-left ss) (ss-right ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just x ∷ Gi , ss-right ss₁₃ , ss-left ss₂₄
ssplit-compose (just (x , POSNEG) ∷ G) (just _ ∷ G₁) (nothing ∷ G₂) (just (_ , POS) ∷ G₃) (just (_ , NEG) ∷ G₄) (ss-left ss) (ss-posneg ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ =  just (x , NEG) ∷ Gi , ss-posneg ss₁₃ , ss-left ss₂₄
ssplit-compose (just (s , POSNEG) ∷ G) (just _ ∷ G₁) (nothing ∷ G₂) (just (_ , NEG) ∷ G₃) (just (_ , POS) ∷ G₄) (ss-left ss) (ss-negpos ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just (s , POS) ∷ Gi , ss-negpos ss₁₃ , ss-left ss₂₄
ssplit-compose (just x ∷ G) (nothing ∷ G₁) (just _ ∷ G₂) (nothing ∷ G₃) (nothing ∷ G₄) (ss-right ss) (ss-both ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just x ∷ Gi , ss-right ss₁₃ , ss-right ss₂₄
ssplit-compose (just (s , POSNEG) ∷ G) (just (_ , POS) ∷ G₁) (just (_ , NEG) ∷ G₂) (just (_ , POS) ∷ G₃) (nothing ∷ G₄) (ss-posneg ss) (ss-left ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just (s , NEG) ∷ Gi , ss-posneg ss₁₃ , ss-right ss₂₄
ssplit-compose (just (s , POSNEG) ∷ G) (just (_ , POS) ∷ G₁) (just (_ , NEG) ∷ G₂) (nothing ∷ G₃) (just (_ , POS) ∷ G₄) (ss-posneg ss) (ss-right ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just (s , POSNEG) ∷ Gi , ss-right ss₁₃ , ss-posneg ss₂₄
ssplit-compose (just (s , POSNEG) ∷ G) (just (_ , NEG) ∷ G₁) (just (_ , POS) ∷ G₂) (just (_ , NEG) ∷ G₃) (nothing ∷ G₄) (ss-negpos ss) (ss-left ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just (s , POS) ∷ Gi , ss-negpos ss₁₃ , ss-right ss₂₄
ssplit-compose (just (s , POSNEG) ∷ G) (just (_ , NEG) ∷ G₁) (just (_ , POS) ∷ G₂) (nothing ∷ G₃) (just (_ , NEG) ∷ G₄) (ss-negpos ss) (ss-right ss₁) with ssplit-compose G G₁ G₂ G₃ G₄ ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just (s , POSNEG) ∷ Gi , ss-right ss₁₃ , ss-negpos ss₂₄


ssplit-compose3 : (G G₁ G₂ G₃ G₄ : SCtx)
  → SSplit G G₁ G₂
  → SSplit G₂ G₃ G₄
  → Σ SCtx λ Gi → (SSplit G Gi G₄ × SSplit Gi G₁ G₃)
ssplit-compose3 .[] .[] .[] .[] .[] ss-[] ss-[] = [] , ss-[] , ss-[]
ssplit-compose3 (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂) (nothing ∷ G₃) (nothing ∷ G₄) (ss-both ss12) (ss-both ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = nothing ∷ Gi , ss-both ssi4 , ss-both ssi13
ssplit-compose3 (just x ∷ G) (just _ ∷ G₁) (nothing ∷ G₂) (nothing ∷ G₃) (nothing ∷ G₄) (ss-left ss12) (ss-both ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just x ∷ Gi , ss-left ssi4 , ss-left ssi13
ssplit-compose3 (just x ∷ G) (nothing ∷ G₁) (just _ ∷ G₂) (just _ ∷ G₃) (nothing ∷ G₄) (ss-right ss12) (ss-left ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just x ∷ Gi , ss-left ssi4 , ss-right ssi13
ssplit-compose3 (just x ∷ G) (nothing ∷ G₁) (just _ ∷ G₂) (nothing ∷ G₃) (just _ ∷ G₄) (ss-right ss12) (ss-right ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = nothing ∷ Gi , ss-right ssi4 , ss-both ssi13
ssplit-compose3 (just (s , POSNEG) ∷ G) (nothing ∷ G₁) (just (_ , POSNEG) ∷ G₂) (just (_ , POS) ∷ G₃) (just (_ , NEG) ∷ G₄) (ss-right ss12) (ss-posneg ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just (s , POS) ∷ Gi , ss-posneg ssi4 , ss-right ssi13
ssplit-compose3 (just (s , POSNEG) ∷ G) (nothing ∷ G₁) (just (_ , POSNEG) ∷ G₂) (just (_ , NEG) ∷ G₃) (just (_ , POS) ∷ G₄) (ss-right ss12) (ss-negpos ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just (s , NEG) ∷ Gi , ss-negpos ssi4 , ss-right ssi13
ssplit-compose3 (just (s , POSNEG) ∷ G) (just (_ , POS) ∷ G₁) (just (_ , NEG) ∷ G₂) (just (_ , NEG) ∷ G₃) (nothing ∷ G₄) (ss-posneg ss12) (ss-left ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just (s , POSNEG) ∷ Gi , ss-left ssi4 , ss-posneg ssi13
ssplit-compose3 (just (s , POSNEG) ∷ G) (just (_ , POS) ∷ G₁) (just (_ , NEG) ∷ G₂) (nothing ∷ G₃) (just (_ , NEG) ∷ G₄) (ss-posneg ss12) (ss-right ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just (s , POS) ∷ Gi , ss-posneg ssi4 , ss-left ssi13
ssplit-compose3 (just (s , POSNEG) ∷ G) (just (_ , NEG) ∷ G₁) (just (_ , POS) ∷ G₂) (just (_ , POS) ∷ G₃) (nothing ∷ G₄) (ss-negpos ss12) (ss-left ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just (s , POSNEG) ∷ Gi , ss-left ssi4 , ss-negpos ssi13
ssplit-compose3 (just (s , POSNEG) ∷ G) (just (_ , NEG) ∷ G₁) (just (_ , POS) ∷ G₂) (nothing ∷ G₃) (just (_ , POS) ∷ G₄) (ss-negpos ss12) (ss-right ss234) with ssplit-compose3 G G₁ G₂ G₃ G₄ ss12 ss234
... | Gi , ssi4 , ssi13 = just (s , NEG) ∷ Gi , ss-negpos ssi4 , ss-left ssi13


ssplit-compose4
  : (G G₁ G₂ G₂₁ G₂₂ : SCtx) 
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₂ G₂₁ G₂₂)
  → Σ SCtx λ Gi → SSplit G G₂₁ Gi × SSplit Gi G₁ G₂₂
ssplit-compose4 G G₁ G₂ G₃ G₄ ss ss₁ = {!!}

-- a session context is inactive if all its entries are void
data Inactive : (G : SCtx) → Set where
  []-inactive : Inactive []
  ::-inactive :  (G : SCtx) → Inactive G → Inactive (nothing ∷ G)

inactive-ssplit-trivial : ∀ {G} → Inactive G → SSplit G G G
inactive-ssplit-trivial []-inactive = ss-[]
inactive-ssplit-trivial (::-inactive G ina) = ss-both (inactive-ssplit-trivial ina)

ssplit-inactive : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₁ → Inactive G₂ → Inactive G
ssplit-inactive ss-[] []-inactive []-inactive = []-inactive
ssplit-inactive (ss-both ssp) (::-inactive G ina1) (::-inactive G₁ ina2) = ::-inactive _ (ssplit-inactive ssp ina1 ina2)
ssplit-inactive (ss-left ssp) () ina2
ssplit-inactive (ss-right ssp) ina1 ()
ssplit-inactive (ss-posneg ssp) () ina2
ssplit-inactive (ss-negpos ssp) ina1 ()

ssplit-inactive-left : ∀ {G G'} → SSplit G G G' → Inactive G'
ssplit-inactive-left ss-[] = []-inactive
ssplit-inactive-left (ss-both ssp) = ::-inactive _ (ssplit-inactive-left ssp)
ssplit-inactive-left (ss-left ssp) = ::-inactive _ (ssplit-inactive-left ssp)

ssplit-refl-left : (G : SCtx) → Σ SCtx λ G' → SSplit G G G'
ssplit-refl-left [] = [] , ss-[]
ssplit-refl-left (just x ∷ G) with ssplit-refl-left G
... | G' , ssp' = nothing ∷ G' , ss-left ssp'
ssplit-refl-left (nothing ∷ G) with ssplit-refl-left G
... | G' , ssp' = nothing ∷ G' , ss-both ssp'

ssplit-inactive-right : ∀ {G G'} → SSplit G G' G → Inactive G'
ssplit-inactive-right ss-[] = []-inactive
ssplit-inactive-right (ss-both ss) = ::-inactive _ (ssplit-inactive-right ss)
ssplit-inactive-right (ss-right ss) = ::-inactive _ (ssplit-inactive-right ss)

ssplit-refl-right : (G : SCtx) → Σ SCtx λ G' → SSplit G G' G
ssplit-refl-right [] = [] , ss-[]
ssplit-refl-right (just x ∷ G) with ssplit-refl-right G
... | G' , ssp' = nothing ∷ G' , ss-right ssp'
ssplit-refl-right (nothing ∷ G) with ssplit-refl-right G
... | G' , ssp' = nothing ∷ G' , ss-both ssp'

inactive-left-ssplit : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₁ → G ≡ G₂
inactive-left-ssplit ss-[] []-inactive = refl
inactive-left-ssplit (ss-both ss) (::-inactive G inG₁) =
  cong (_∷_ nothing) (inactive-left-ssplit ss inG₁)
inactive-left-ssplit (ss-right ss) (::-inactive G inG₁) =
  cong (_∷_ (just _)) (inactive-left-ssplit ss inG₁)

inactive-right-ssplit : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₂ → G ≡ G₁
inactive-right-ssplit ss-[] []-inactive = refl
inactive-right-ssplit (ss-both ssp) (::-inactive G ina) =
  cong (_∷_ nothing) (inactive-right-ssplit ssp ina)
inactive-right-ssplit (ss-left ssp) (::-inactive G ina) =
  cong (_∷_ (just _)) (inactive-right-ssplit ssp ina)

inactive-right-ssplit-sym : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₂ → G₁ ≡ G
inactive-right-ssplit-sym ssp ina = sym (inactive-right-ssplit ssp ina)


ssplit-function : ∀ {G G' G₁ G₂} → SSplit G G₁ G₂ → SSplit G' G₁ G₂ → G ≡ G'
ssplit-function ss-[] ss-[] = refl
ssplit-function (ss-both ssp-GG1G2) (ss-both ssp-G'G1G2) =
  cong (_∷_ nothing) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-left ssp-GG1G2) (ss-left ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-right ssp-GG1G2) (ss-right ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-posneg ssp-GG1G2) (ss-posneg ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-negpos ssp-GG1G2) (ss-negpos ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)

ssplit-function1 : ∀ {G G₁ G₁' G₂} → SSplit G G₁ G₂ → SSplit G G₁' G₂ → G₁ ≡ G₁'
ssplit-function1 ss-[] ss-[] = refl
ssplit-function1 (ss-both ssp-GG1G2) (ss-both ssp-GG1'G2) =
  cong (_∷_ nothing) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-left ssp-GG1G2) (ss-left ssp-GG1'G2) =
  cong (_∷_ (just _)) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-right ssp-GG1G2) (ss-right ssp-GG1'G2) =
  cong (_∷_ nothing) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-posneg ssp-GG1G2) (ss-posneg ssp-GG1'G2) =
  cong (_∷_ (just _)) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-negpos ssp-GG1G2) (ss-negpos ssp-GG1'G2) =
  cong (_∷_ (just _)) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)

ssplit-function2 : ∀ {G G₁ G₂ G₂'} → SSplit G G₁ G₂ → SSplit G G₁ G₂' → G₂ ≡ G₂'
ssplit-function2 ss-[] ss-[] = refl
ssplit-function2 (ss-both ssp-GG1G2) (ss-both ssp-GG1G2') =
  cong (_∷_ nothing) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-left ssp-GG1G2) (ss-left ssp-GG1G2') =
  cong (_∷_ nothing) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-right ssp-GG1G2) (ss-right ssp-GG1G2') =
  cong (_∷_ (just _)) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-posneg ssp-GG1G2) (ss-posneg ssp-GG1G2') =
  cong (_∷_ (just _)) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-negpos ssp-GG1G2) (ss-negpos ssp-GG1G2') =
  cong (_∷_ (just _)) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')

-- the main part of a channel endpoint value is a valid channel reference
-- the boolean determines whether it's the front end or the back end of the channel
-- enforces that the session context has only one channel
data ValidChannelRef : (G : SCtx) (b : Bool) (s : STy) → Set where
  here-pos : ∀ {s} {G : SCtx}
    → Inactive G
    → ValidChannelRef (just (s , POS) ∷ G) true s
  here-neg : ∀ {s} {G : SCtx}
    → Inactive G
    → ValidChannelRef (just (s , NEG) ∷ G) false (dual s)
  there : ∀ {b s} {G : SCtx}
    → ValidChannelRef G b s
    → ValidChannelRef (nothing ∷ G) b s

-- a value indexed by a *relevant* session context, which is "used up" by the value
data Val (G : SCtx) : Ty → Set where
  VUnit : Inactive G → Val G TUnit
  VInt  : (i : ℕ) → Inactive G → Val G TInt
  VPair : ∀ {t₁ t₂ G₁ G₂} → SSplit G G₁ G₂ → (v₁ : Val G₁ t₁) → (v₂ : Val G₂ t₂) → Val G (TPair t₁ t₂)
  VChan : ∀ {s} → (b : Bool) → (vcr : ValidChannelRef G b s) → Val G (TChan s)

unrestricted-val :  ∀ {t G} → Unr t → Val G t → Inactive G
unrestricted-val UUnit (VUnit x) = x
unrestricted-val UInt (VInt i x) = x
unrestricted-val (UPair unrt unrt₁) (VPair x v v₁) =
  ssplit-inactive x (unrestricted-val unrt v) (unrestricted-val unrt₁ v₁)

-- type environment-indexed value environment
-- session context G describes the entire environment, it splits over all (channel) values
data VEnv (G : SCtx) : TCtx → Set where
  vnil : (ina : Inactive G) → VEnv G []
  vcons : ∀{t φ G₁ G₂} → (ssp : SSplit G G₁ G₂) → (v : Val G₁ t) → (ϱ : VEnv G₂ φ) → VEnv G (t ∷ φ)

unrestricted-venv : ∀ {φ G} → All Unr φ → VEnv G φ → Inactive G
unrestricted-venv unr-φ (vnil ina) = ina
unrestricted-venv (px ∷ unr-φ) (vcons ssp v ϱ) =
  ssplit-inactive ssp (unrestricted-val px v) (unrestricted-venv unr-φ ϱ)

-- access a value in an indexed environment
access : ∀ {φ t} {G : SCtx} → VEnv G φ → t ∈ φ → Σ SCtx λ G₁ → Σ SCtx λ G₂ → Inactive G₂ × SSplit G G₁ G₂ × Val G₁ t
access (vcons ssp v ϱ) (here allUnr) =  _ , _ , unrestricted-venv allUnr ϱ , ssp , v
access (vcons ssp x₀ ϱ) (there unrX₀ x) with access ϱ x
access (vcons ssp x₀ ϱ) (there unrX₀ x) | G₁ , G₂ , inaG₂ , ssp12 , v with ssplit-compose4 _ _ _ _ _ ssp ssp12
... | Gi , ssp1 , ssp2 = G₁ , Gi , ssplit-inactive ssp2 (unrestricted-val unrX₀ x₀) inaG₂ , ssp1 , v

-- non-empty list of value environments for use in a continuation closure
data CLEnv (G : SCtx) : List TCtx → Set where
  clnil : Inactive G → CLEnv G []
  clcons : ∀ {G₁ G₂ φ φ*}
    → (ssp : SSplit G G₁ G₂) (ϱ : VEnv G₁ φ) (ξ : CLEnv G₂ φ*)
    → CLEnv G (φ ∷ φ*)

rewrite-ssplit : ∀ {G G' G₁ G₂} → G ≡ G' → SSplit G G₁ G₂ → SSplit G' G₁ G₂
rewrite-ssplit p ssp rewrite p = ssp

rewrite-ssplit1 : ∀ {G G₁ G₁' G₂} → G₁ ≡ G₁' → SSplit G G₁ G₂ → SSplit G G₁' G₂
rewrite-ssplit1 p ssp rewrite p = ssp

-- split environment according to type context split
split-env : ∀ {Φ Φ₁ Φ₂} {G : SCtx}
  → Split Φ Φ₁ Φ₂
  → VEnv G Φ
  → Σ (SCtx × SCtx) λ { (G₁ , G₂) → SSplit G G₁ G₂ × VEnv G₁ Φ₁ × VEnv G₂ Φ₂ }
split-env{G = G} [] (vnil ina) =  (G , G) , inactive-ssplit-trivial ina , vnil ina , vnil ina
split-env (unr unrt sp) (vcons ssp v ϱ) with split-env sp ϱ | unrestricted-val unrt v
split-env (unr unrt sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' | unr-v rewrite inactive-left-ssplit ssp unr-v with ssplit-compose4 _ _ _ _ _ ssp ssp12 | ssplit-compose3 _ _ _ _ _ ssp ssp12
... | Gi , ssp-GG1Gi , ssp-GiG1G2' | Gi-1 , ssp-GGiG2' , ssp-GiG1G1' =
  let p₁ = (inactive-left-ssplit ssp-GiG1G1' unr-v) in
  let p₂ = (inactive-left-ssplit ssp-GiG1G2' unr-v) in
  (G₁' , G₂') ,  ssp12 , vcons (rewrite-ssplit p₁ ssp-GiG1G1') v ϱ₁' , vcons (rewrite-ssplit p₂ ssp-GiG1G2') v ϱ₂' 
split-env (left sp) (vcons ssp v ϱ) with split-env sp ϱ
split-env{G = G} (left sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' with ssplit-compose3 _ _ _ _ _ ssp ssp12
... | Gi , ssp-GiG2' , ssp-GiG1G1' = (Gi , G₂') , ssp-GiG2' , vcons ssp-GiG1G1' v ϱ₁' , ϱ₂'
split-env (rght sp) (vcons ssp v ϱ) with split-env sp ϱ
split-env (rght sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' with ssplit-compose4 _ _ _ _ _ ssp ssp12
...| Gi , ssp-GG1'Gi , ssp-GiG1G2' = (G₁' , Gi) , ssp-GG1'Gi , ϱ₁' , vcons ssp-GiG1G2' v ϱ₂' 

data Fuel : Set where
  Empty : Fuel
  More  : Fuel → Fuel

mutual
  data Cont (t : Ty) (G : SCtx) (φ : TCtx) : Set where
    cont : 
      (ϱ : VEnv G φ)
      → (c : ∀ {G' Gx} → SSplit G' Gx G → Val Gx t → VEnv G φ →  Command G')
      → Cont t G φ

    bind : ∀ { φ₁ φ₂ G₁ G₂ t₂}
      → (ts : Split φ φ₁ φ₂)
      → (ss : SSplit G G₁ G₂)
      → (e₂ : Expr (t ∷ φ₁) t₂)
      → (ϱ₂ : VEnv G₁ φ₁)
      → (κ₂ : Cont t₂ G₂ φ₂)
      → Cont t G φ

  data Command (G : SCtx) : Set where
{-
    Bind : ∀ {φ φ₁ φ₂ G₁ G₂ t₁ t₂}
      → (ts : Split φ φ₁ φ₂)
      → (ss : SSplit G G₁ G₂)
      → (v : Val G₁ t₁)
      → (e₂ : Expr (t₁ ∷ φ₁) t₂)
      → (ϱ₂ : VEnv G₂ φ₁)
      → (κ₂ : Cont t₂ G₂ φ₂)
      → Command G
-}

    Fork : ∀ {φ₁ φ₂ G₁ G₂}
      → (ss : SSplit G G₁ G₂)
      → (κ₁ : Cont TUnit G₁ φ₁)
      → (κ₂ : Cont TUnit G₂ φ₂)
      → Command G

    Stopped : ∀ {φ t G₁ G₂}
      → (ss : SSplit G G₁ G₂)
      → (v : Val G₁ t)
      → (κ : Cont t G₂ φ)
      → Command G

    Halt :
      Inactive G
      → Command G
    New : ∀ {φ}
      → (s : STy)
      → (κ : Cont (TPair (TChan s) (TChan (dual s))) G φ)
      → Command G
    Close : ∀ {φ}
      → (v : Val G (TChan SEnd!))
      → (κ : Cont TUnit G φ)
      → Command G
    Wait  : ∀ {φ}
      → (v : Val G (TChan SEnd?))
      → (κ : Cont TUnit G φ)
      → Command G

-- 

-- finish a computation
halt-cont : ∀ {G φ} → All Unr φ → VEnv G φ → Cont TUnit G φ
halt-cont unr-φ ϱ = cont ϱ (λ {G'} {Gx} ss-G'GxG vGxt ϱ' → Halt (ssplit-inactive ss-G'GxG (unrestricted-val UUnit vGxt) (unrestricted-venv unr-φ ϱ)))

-- 
rewrite-helper : ∀ {G G1 G2 G'' φ'} → Inactive G2 → SSplit G G1 G2 → SSplit G G G'' → VEnv G2 φ' → VEnv G'' φ'
rewrite-helper ina-G2 ssp-GG1G2 ssp-GGG'' ϱ with inactive-right-ssplit ssp-GG1G2 ina-G2
... | p with rewrite-ssplit1 (sym p) ssp-GG1G2
... | ssp rewrite ssplit-function2 ssp ssp-GGG'' = ϱ

fork-cont : ∀ {φ G' Gx G} → Fuel → Expr φ TUnit → SSplit G' Gx G → Val Gx TUnit → VEnv G φ →  Command G'

-- apply a continuation
apply-cont : ∀ {G G₁ G₂ t φ} → Fuel → (ssp : SSplit G G₁ G₂) (κ : Cont t G₂ φ) → Val G₁ t → Command G

run : ∀ {φ φ₁ φ₂ t G G₁ G₂}
  → Fuel
  → Split φ φ₁ φ₂
  → SSplit G G₁ G₂
  → Expr φ₁ t
  → VEnv G₁ φ₁
  → Cont t G₂ φ₂
  → Command G
run{G = G}{G₁ = G₁}{G₂ = G₂} f tsp ssp (var x) ϱ κ with access ϱ x
... | Gx , Gϱ , ina , ssp12 , v rewrite inactive-right-ssplit ssp12 ina = apply-cont f ssp κ v
run f tsp ssp (nat unr-φ i) ϱ κ =
  apply-cont f ssp κ (VInt i (unrestricted-venv unr-φ ϱ))
run{φ}{φ₁}{φ₂} f tsp ssp (letbind{.φ₁}{φ₁₁}{φ₁₂}{t₁}{t₂} sp e₁ e₂) ϱ κ₂ with split-env sp ϱ | split-rotate tsp sp
... | (G₁ , G₂) , ssp-G1G2 , ϱ₁ , ϱ₂ | φ' , tsp-φ' , φ'-tsp with ssplit-compose _ _ _ _ _ ssp ssp-G1G2
... | Gi , ssp-3i , ssp-42 =
  run f tsp-φ' ssp-3i e₁ ϱ₁
  (bind φ'-tsp ssp-42 e₂ ϱ₂ κ₂)
run f tsp ssp (pair sp x₁ x₂) ϱ κ = {!!}
run f tsp ssp (letpair sp p e) ϱ κ = {!!}
run{φ}{G = G} f tsp ssp (fork e) ϱ κ =
  Fork ssp (cont ϱ (fork-cont f e)) κ
run f tsp ssp (new unr-φ s) ϱ κ with unrestricted-venv unr-φ ϱ
... | ina rewrite inactive-left-ssplit ssp ina = New s κ
run f tsp ssp (close ch) ϱ κ = {!!}
run f tsp ssp (wait ch) ϱ κ = {!!}


apply-cont f ssp (cont ϱ c) v = c ssp v ϱ
apply-cont (More f) ssp (bind ts ss e₂ ϱ₂ κ) v with ssplit-compose3 _ _ _ _ _ ssp ss
... | Gi , ss-GGiG4 , ss-GiG1G3 =
  run f (left ts) ss-GGiG4 e₂ (vcons ss-GiG1G3 v ϱ₂) κ
apply-cont Empty ssp (bind ts ss e₂ ϱ₂ κ) v =
  Stopped {!!} {!!} {!!}


fork-cont {φ}{ G'}{ Gx}{ G} (More f) e ssp_x_ϱ vx ϱ' with unrestricted-val UUnit vx
... | inaGx rewrite inactive-left-ssplit ssp_x_ϱ inaGx with ssplit-refl-left G | split-refl-left φ
... | G'' , sspGG' | φ' , unr-φ' , sp-φφφ' with split-env sp-φφφ' ϱ'
... | (G1 , G2) , ssp-G1G2 , ϱ₁' , ϱ₂' with unrestricted-venv unr-φ' ϱ₂'
... | ina-G2 = run f sp-φφφ' sspGG' e ϱ' (halt-cont unr-φ' (rewrite-helper ina-G2 ssp-G1G2 sspGG' ϱ₂'))
fork-cont {φ}{ G'}{ Gx}{ G} Empty e ssp_x_ϱ vx ϱ' =
  Stopped {!!} {!!} {!!}

lift-cont : ∀ {G t φ} → Cont t G φ → Cont t (nothing ∷ G) φ
lift-cont κ = {!!}

lift-command : ∀ {G} → Command G → Command (nothing ∷ G)
lift-command cmd = {!!}

-- threads
data ThreadPool (G : SCtx) : Set where
  tnil : (ina : Inactive G) → ThreadPool G
  tcons : ∀ {G₁ G₂} → (ss : SSplit G G₁ G₂) → (cmd : Command G₁) → (tp : ThreadPool G₂) → ThreadPool G

lift-threadpool : ∀ {G} → ThreadPool G → ThreadPool (nothing ∷ G)
lift-threadpool (tnil ina) = tnil (::-inactive _ ina)
lift-threadpool (tcons ss cmd tp) = tcons (ss-both ss) (lift-command cmd) (lift-threadpool tp)

-- thread scheduling
schedule : Fuel → (G : SCtx) → ThreadPool G → ⊤
schedule f G (tnil ina) = tt
schedule (More f) G (tcons ss (Fork{G₁ = G₁}{G₂ = G₂} ss₁ κ₁ κ₂) tp) with ssplit-compose _ _ _ _ _ ss ss₁
... | Gi , ss₁₃ , ss₂₄ with ssplit-refl-right G₁ | ssplit-refl-right G₂
... | Gunit , ss-G1GunitG1 | G2unit , ss-G2GuG2 =
  schedule f G
    (tcons ss₁₃ (apply-cont f ss-G1GunitG1 κ₁ (VUnit (ssplit-inactive-right ss-G1GunitG1)))
    (tcons ss₂₄ (apply-cont f ss-G2GuG2 κ₂ (VUnit (ssplit-inactive-right ss-G2GuG2))) tp))
schedule (More f) G (tcons ss (Stopped ss₁ v κ) tp) = {!!}
schedule (More f) G (tcons ss (Halt inaG) tp) with tp | inactive-left-ssplit ss inaG
schedule (More f) G (tcons ss (Halt inaG) tp) | tp' | refl = schedule f G tp'
schedule (More f) G (tcons{G₁} ss (New s κ) tp) with ssplit-refl-right G₁
... | Gi , ss-GiG1 with ssplit-inactive-right ss-GiG1
... | ina-Gi =
  schedule f (just (s , POSNEG) ∷ G)
    (tcons (ss-left ss)
           (apply-cont f (ss-left ss-GiG1) (lift-cont κ) (VPair (ss-posneg (inactive-ssplit-trivial ina-Gi)) (VChan true (here-pos ina-Gi)) (VChan false (here-neg ina-Gi))))
           (lift-threadpool tp))
schedule (More f) G (tcons ss (Close v κ) tp) = {!!}
schedule (More f) G (tcons ss (Wait v κ) tp) = {!!}
schedule Empty G (tcons _ _ _) = {!!}
