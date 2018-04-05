module EssentialSession6 where

open import Data.Bool
open import Data.Empty
open import Data.Fin hiding (_+_ ; _≤_)
open import Data.List hiding (reverse)
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Vec hiding ( _∈_ ; _>>=_)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Lemmas

-- TODO:
-- * incorporate ∈'

-- general
data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)

Pred : Set → Set₁
Pred a = a → Set

data Forall {a : Set} (P : Pred a) : List a → Set where
  [] : Forall P []
  _∷_ : ∀ {x xs} → P x → Forall P xs → Forall P (x ∷ xs)

-- specific
data PosNeg : Set where
  POS NEG POSNEG : PosNeg

-- types and session types
mutual
  -- keep track which ends of a channel a process is allowed to possess
  -- m >= n, but they are equal on the top level
  SCtx = List (Maybe (STy × PosNeg))

  data Ty : Set where
    TUnit TInt : Ty
    TPair : Ty → Ty → Ty
    TChan : STy → Ty

  data STy : Set where
    SSend SRecv : Ty → STy → STy
    SEnd! SEnd? : STy

dual : STy → STy
dual (SSend x s) = SRecv x (dual s)
dual (SRecv x s) = SSend x (dual s)
dual SEnd! = SEnd?
dual SEnd? = SEnd!

dual-involution : (s : STy) → dual (dual s) ≡ s
dual-involution (SSend x s) rewrite dual-involution s = refl
dual-involution (SRecv x s) rewrite dual-involution s = refl
dual-involution SEnd! = refl
dual-involution SEnd? = refl

xdual : Bool → STy → STy
xdual false s = dual s
xdual true s = s


-- liftSTy : {n : ℕ} → STy n → STy (suc n)
-- liftTy  : {n : ℕ} → Ty n → Ty (suc n)

-- liftSTy (SSend x s) = SSend (liftTy x) (liftSTy s)
-- liftSTy (SRecv x s) = SRecv (liftTy x) (liftSTy s)
-- liftSTy SEnd! = SEnd!
-- liftSTy SEnd? = SEnd?

-- liftTy TUnit = TUnit
-- liftTy TInt = TInt
-- liftTy (TPair t₁ t₂) = TPair (liftTy t₁) (liftTy t₂)
-- liftTy (TChan s) = TChan (liftSTy s)

-- liftSTy-dual : ∀ {n} → (s : STy n) → liftSTy (dual s) ≡ dual (liftSTy s)
-- liftSTy-dual (SSend x s) = cong (SRecv (liftTy x)) (liftSTy-dual s)
-- liftSTy-dual (SRecv x s) = cong (SSend (liftTy x)) (liftSTy-dual s)
-- liftSTy-dual SEnd! = refl
-- liftSTy-dual SEnd? = refl

-- liftSTy-xdual : ∀ {n b} → (s : STy n) → liftSTy (xdual b s) ≡ xdual b (liftSTy s)
-- liftSTy-xdual {b = false} s = liftSTy-dual s
-- liftSTy-xdual {b = true} s = refl


-- liftMSPN1 : ∀ {n} → Maybe (STy n × PosNeg) → Maybe (STy (suc n) × PosNeg)
-- liftMSPN1 (just (s , pn)) = just (liftSTy s , pn)
-- liftMSPN1 nothing = nothing

-- liftSCtx : {m n : ℕ} → SCtx m n → SCtx (suc m) n
-- liftSCtx [] = []
-- liftSCtx (x ∷ G) = liftMSPN1 x ∷ liftSCtx G

-- liftNTy : {n : ℕ} → (k : ℕ) → Ty n → Ty (k + n)
-- liftNSTy : {n : ℕ} → (k : ℕ) → STy n → STy (k + n)

-- liftNTy k TUnit = TUnit
-- liftNTy k TInt = TInt
-- liftNTy k (TPair t t₁) = TPair (liftNTy k t) (liftNTy k t₁)
-- liftNTy k (TChan s) = TChan (liftNSTy k s)

-- liftNSTy k (SSend t s) = SSend (liftNTy k t) (liftNSTy k s)
-- liftNSTy k (SRecv t s) = SRecv (liftNTy k t) (liftNSTy k s)
-- liftNSTy k SEnd! = SEnd!
-- liftNSTy k SEnd? = SEnd?

-- liftNSCtx : {m n : ℕ} → (k : ℕ) → SCtx m n → SCtx (k + m) n
-- liftNSCtx zero G = G
-- liftNSCtx (suc k) G = liftSCtx (liftNSCtx k G)

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

-- (ss : SSplit G G₁ G₂) (ss₁ : SSplit G₁ G₃ G₄) → (ss₁₃ : SSplit G G₃ Gi) x (ss₂₄ : Gi G₄ G₂)
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

-- tedious but easy to prove
ssplit-compose4
  : (G G₁ G₂ G₂₁ G₂₂ : SCtx) 
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₂ G₂₁ G₂₂)
  → Σ SCtx λ Gi → SSplit G G₂₁ Gi × SSplit Gi G₁ G₂₂
ssplit-compose4 G G₁ G₂ G₃ G₄ ss ss₁ = {!!}

data ValidChannelRef : (G : SCtx) (b : Bool) (s : STy) → Set where
  here-pos : ∀ { s} {G : SCtx}
    → ValidChannelRef (just (s , POS) ∷ G) true s
  here-neg : ∀ {s} {G : SCtx}
    → ValidChannelRef (just (s , NEG) ∷ G) false (dual s)
  here-posneg : ∀ {s b} {G : SCtx}
    → ValidChannelRef (just (s , POSNEG) ∷ G) b (xdual b s)
  there : ∀ {x b s} {G : SCtx}
    → ValidChannelRef G b s
    → ValidChannelRef (x ∷ G) b s

data Val (G : SCtx) : Ty → Set where
  VInt  : (i : ℕ) → Val G TInt
  VPair : ∀ {t₁ t₂} → (v₁ : Val G t₁) → (v₂ : Val G t₂) → Val G (TPair t₁ t₂)
  VChan : ∀ {s} → (b : Bool) → ValidChannelRef G b s → Val G (TChan s)

-- liftVal1 : ∀ {n : ℕ} {G : SCtx n n} {t : Ty n} {x : Maybe (STy (suc n) × PosNeg)} → Val G t → Val (x ∷ liftSCtx G) (liftTy t)
-- liftVal1 (VInt n) = VInt n
-- liftVal1 (VPair v₁ v₂) = VPair (liftVal1 v₁) (liftVal1 v₂)
-- liftVal1 (VChan m b vcr) = VChan (inject₁ m) b {!liftVCR!}

-- liftValK : ∀ {n : ℕ} {G : SCtx n n} {t : Ty n} (k : ℕ) {H : Vec (Maybe (STy (k + n) × PosNeg)) k} → Val G t → Val (H Data.Vec.++ liftNSCtx k G) (liftNTy k t)
-- liftValK k (VInt n) = VInt n
-- liftValK {G = G} k {H} (VPair v v₁) = VPair (liftValK {G = G} k {H} v) (liftValK {G = G} k {H} v₁)
-- liftValK k (VChan m b x) = let m' = injectk+ k m in VChan m' b {!!}

-- alternative without explicitly mentioning the annoying Fin

data ValidChannelRef' : (G : SCtx) (b : Bool) (s : STy) → Set where
  here-pos : ∀ {s} {G : SCtx}
    → ValidChannelRef' (just (s , POS) ∷ G) true s
  here-neg : ∀ {s} {G : SCtx}
    → ValidChannelRef' (just (s , NEG) ∷ G) false (dual s)
  here-posneg : ∀ {s b} {G : SCtx}
    → ValidChannelRef' (just (s , POSNEG) ∷ G) b (xdual b s)
  there : ∀ {x b s} {G : SCtx}
    → ValidChannelRef' G b s
    → ValidChannelRef' (x ∷ G) b s

-- liftVCR' : ∀ {n k b s}
--   → (x : Maybe (STy (suc n) × PosNeg))
--   → (G : Vec (Maybe (STy n × PosNeg)) k)
--   → ValidChannelRef' G b s
--   → ValidChannelRef' (x ∷ liftSCtx G) b (liftSTy s)

-- liftVCR' x .(just (_ , POS) ∷ _) here-pos = there here-pos
-- liftVCR' x .(just (_ , NEG) ∷ _) (here-neg{n}{s}) rewrite liftSTy-dual s = there here-neg
-- liftVCR' x .(just (_ , POSNEG) ∷ _) (here-posneg{n}{s}{b}) rewrite liftSTy-xdual{b = b} s = there here-posneg
-- liftVCR' x (x' ∷ G') (there vcr) = there (liftVCR' (liftMSPN1 x') G' vcr)

    
data Val' (G : SCtx) : Ty → Set where
  VUnit : Val' G TUnit
  VInt  : (i : ℕ) → Val' G TInt
  VPair : ∀ {t₁ t₂} → (v₁ : Val' G t₁) → (v₂ : Val' G t₂) → Val' G (TPair t₁ t₂)
  VChan : ∀ {s} → (b : Bool) → (vcr : ValidChannelRef' G b s) → Val' G (TChan s)

-- liftVal'1 : ∀ {n : ℕ} {G : SCtx n n} {t : Ty n} {x : Maybe (STy (suc n) × PosNeg)} → Val' G t → Val' (x ∷ liftSCtx G) (liftTy t)
-- liftVal'1 (VInt n) = VInt n
-- liftVal'1 (VPair v v₁) = VPair (liftVal'1 v) (liftVal'1 v₁)
-- liftVal'1 (VChan b vcr) = VChan b (liftVCR' _ _ vcr)

-- typing context
TCtx : Set
TCtx = List Ty

-- lifting for typing contexts
-- liftTCtx : {n : ℕ} → TCtx n → TCtx (suc n)
-- liftTCtx φ = Data.List.map liftTy φ

-- liftNTCtx : {n : ℕ} → (k : ℕ) → TCtx n → TCtx (k + n)
-- liftNTCtx k φ = Data.List.map (liftNTy k) φ

-- linear and unrestricted types
data Lin : Ty → Set where
  LChan : ∀ {s} → Lin (TChan s)
  LPair1 : ∀ {t₁ t₂} → Lin t₁ → Lin (TPair t₁ t₂)
  LPair2 : ∀ {t₁ t₂} → Lin t₂ → Lin (TPair t₁ t₂)

data Unr : Ty → Set where
  UUnit : Unr TUnit
  UInt : Unr TInt
  UPair : ∀ {t₁ t₂} → Unr t₁ → Unr t₂ → Unr (TPair t₁ t₂)

-- lin and unr are mutually exclusive
lemma-lin-unr : ∀ {t} → Lin t → ¬ Unr t
lemma-lin-unr LChan ()
lemma-lin-unr (LPair1 lint) (UPair x x₁) = lemma-lin-unr lint x
lemma-lin-unr (LPair2 lint) (UPair x x₁) = lemma-lin-unr lint x₁

lemma-unr-lin : ∀  {t} → Unr t → ¬ Lin t
lemma-unr-lin UUnit ()
lemma-unr-lin UInt ()
lemma-unr-lin (UPair unr unr₁) (LPair1 lin) = lemma-unr-lin unr lin
lemma-unr-lin (UPair unr unr₁) (LPair2 lin) = lemma-unr-lin unr₁ lin

-- context splitting, respecting linearity
data Split : TCtx → TCtx → TCtx → Set where
  [] : Split [] [] []
  unr : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  linleft : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) Φ₂
  linrght : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ (t ∷ Φ₂)

-- extracting from typing environment, where all other entries must be unrestricted
data _∈'_ (x : Ty) : TCtx → Set where
  here  : ∀ { xs } → Forall Unr xs → x ∈' (x ∷ xs)
  there : ∀ { t₀ xs } → Unr t₀ → x ∈' xs → x ∈' (t₀ ∷ xs)

-- value environments
data VEnv (G : SCtx) : TCtx → Set where
  [] : VEnv G []
  _∷_ : ∀{t φ} → (x : Val G t) → (ϱ : VEnv G φ) → VEnv G (t ∷ φ)

-- split environment according to type context split
split-env : ∀ {Φ Φ₁ Φ₂} {G : SCtx} → Split Φ Φ₁ Φ₂ → VEnv G Φ → VEnv G Φ₁ × VEnv G Φ₂
split-env [] [] = [] , []
split-env (unr x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env (linleft x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env (linrght x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- alternative
data VEnv' (G : SCtx) : TCtx → Set where
  [] : VEnv' G []
  _∷_ : ∀{t φ} → (x : Val' G t) → (ϱ : VEnv' G φ) → VEnv' G (t ∷ φ)

-- split environment according to type context split
split-env' : ∀ {Φ Φ₁ Φ₂} {G : SCtx} → Split Φ Φ₁ Φ₂ → VEnv' G Φ → VEnv' G Φ₁ × VEnv' G Φ₂
split-env' [] [] = [] , []
split-env' (unr x₁ sp) (x ∷ ϱ) with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env' (linleft x₁ sp) (x ∷ ϱ) with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env' (linrght x₁ sp) (x ∷ ϱ) with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)





-- alternative
data Inactive : (G : SCtx) → Set where
  []-inactive : Inactive []
  ::-inactive :  (G : SCtx) → Inactive G → Inactive (nothing ∷ G)

data ValidChannelRef'' : (G : SCtx) (b : Bool) (s : STy) → Set where
  here-pos : ∀ {s} {G : SCtx}
    → Inactive G
    → ValidChannelRef'' (just (s , POS) ∷ G) true s
  here-neg : ∀ {s} {G : SCtx}
    → Inactive G
    → ValidChannelRef'' (just (s , NEG) ∷ G) false (dual s)
  there : ∀ {b s} {G : SCtx}
    → ValidChannelRef'' G b s
    → ValidChannelRef'' (nothing ∷ G) b s


data Val'' (G : SCtx) : Ty → Set where
  VUnit : Inactive G → Val'' G TUnit
  VInt  : (i : ℕ) → Inactive G → Val'' G TInt
  VPair : ∀ {t₁ t₂ G₁ G₂} → SSplit G G₁ G₂ → (v₁ : Val'' G₁ t₁) → (v₂ : Val'' G₂ t₂) → Val'' G (TPair t₁ t₂)
  VChan : ∀ {s} → (b : Bool) → (vcr : ValidChannelRef'' G b s) → Val'' G (TChan s)

data VEnv'' (G : SCtx) : TCtx → Set where
  [] : (ina : Inactive G) → VEnv'' G []
  vcons : ∀{t φ G₁ G₂} → (ssp : SSplit G G₁ G₂) → (v : Val'' G₁ t) → (ϱ : VEnv'' G₂ φ) → VEnv'' G (t ∷ φ)


-- expressions
data Expr : (φ : TCtx) → Ty → Set where
  var : ∀ {t φ}
      → (x : t ∈ φ)
      → Expr φ t

  nat : ∀ {φ}
      → (i : ℕ)
      → Expr φ TInt

  letbind : ∀ {φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (e₁ : Expr φ₁ t₁)
    → (e₂ : Expr (t₁ ∷  φ₂) t₂)
    → Expr φ t₂

  pair : ∀ {φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (x₁ : t₁ ∈ φ₁)
    → (x₂ : t₂ ∈ φ₂)
    → Expr φ (TPair t₁ t₂)

  letpair : ∀ {φ φ₁ φ₂ t₁ t₂ t}
    → (sp : Split φ φ₁ φ₂)
    → (x : TPair t₁ t₂ ∈ φ₁)
    → (e : Expr (t₁ ∷ t₂ ∷ φ₂) t)
    → Expr φ t

  fork : ∀ { φ}
    -- → (ss : SSplit G G₁ G₂)
    -- affine -- → (all-nothing : T (all is-nothing (toList G₃)))
    → (e : Expr φ TUnit)
    → Expr φ TUnit

  new : ∀ {φ}
      → (s : STy)
      → Expr φ (TPair (TChan s) (TChan (dual s)))
{-
  -- takes only variables to avoid extraneous effects
  send : ∀ {φ φ₁ φ₂ s t}
      → (sp : Split φ φ₁ φ₂)
      → (ch : (TChan (SSend t s)) ∈ φ₁)
      -- → (dt : DeltaTransmit n (invert k) b G₁ G₂ t)
      → (vv : t ∈ φ₂)
      → Expr φ (TChan s)
  -- takes only variables to avoid extraneous effects
  recv : ∀ {φ s t}
      → (ch : (TChan (SRecv t s)) ∈ φ)
      -- → (dt : DeltaTransmit n (invert k) (not b) G₁ G₂ t)
      → Expr φ (TPair (TChan s) t)
-}
  close : ∀ { φ}
      → (ch : TChan SEnd! ∈ φ)
      → Expr φ TUnit

  wait : ∀ { φ}
      → (ch : TChan SEnd? ∈ φ)
      → Expr φ TUnit



-- data CEnv {n : ℕ} (G : SCtx n n) : Set where
--   [] : CEnv G
--   _∷_ : ∀ {G} → (spn : STy × PosNeg) → (ψ : CEnv G) → CEnv (spn ∷ G)

access : ∀ {φ t} {G : SCtx} → VEnv G φ → t ∈ φ → Val G t
access (x ∷ ϱ) here = x
access (x ∷ ϱ) (there x₁) = access ϱ x₁

access' : ∀ {φ t} {G : SCtx} → VEnv' G φ → t ∈ φ → Val' G t
access' (x ∷ ϱ) here = x
access' (x ∷ ϱ) (there x₁) = access' ϱ x₁

access'' : ∀ {φ t} {G : SCtx} → VEnv'' G φ → t ∈ φ → Σ SCtx λ G₁ → Σ SCtx λ G₂ → SSplit G G₁ G₂ × Val'' G₁ t
access'' (vcons ssp v ϱ) here =  _ , _ , ssp , v
access'' (vcons ssp _ ϱ) (there x) with access'' ϱ x
access'' (vcons ssp _ ϱ) (there x) | G₁ , G₂ , ssp12 , v with ssplit-compose4 _ _ _ _ _ ssp ssp12
... | Gi , ssp1 , ssp2 = G₁ , Gi , ssp1 , v

data Command (A : Set) : Set where
  Return : (x : A) → Command A

_>>=_ : ∀ {A B : Set} → Command A → (A → Command B) → Command B
Return x >>= fab = fab x


run : ∀ {φ t G}
  → Expr φ t 
  → VEnv' G φ → Command (Val' G t)
run (var x) ϱ = Return (access' ϱ x)
run (nat i) ϱ = Return (VInt i)
run (letbind sp e e₁) ϱ with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = run e ϱ₁ >>= {!!}
run (pair sp x₁ x₂) ϱ with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = Return (VPair (access' ϱ₁ x₁) (access' ϱ₂ x₂))
run (letpair sp x e) ϱ with split-env' sp ϱ
... | ϱ₁ , ϱ₂ with access' ϱ₁ x
run (letpair sp x e) ϱ | ϱ₁ , ϱ₂ | VPair v₁ v₂ = run e (v₁ ∷ v₂ ∷ ϱ₂)
run (fork e) ϱ = {!!}
run (new s) ϱ = {!!}
-- run (send sp ch vv) ϱ = {!!}
-- run (recv ch) ϱ = {!!}
run (close ch) ϱ = {!!}
run (wait ch) ϱ = {!!}

-- data Preserves :  (G G' : SCtx) → Set where
--   ≼-[] : Preserves [] []
--   ≼-∷  : ∀ {G G' x} → Preserves G G' → Preserves (x ∷ G) (x ∷ G')

-- preserves-refl : ∀ {G : SCtx} → Preserves G G
-- preserves-refl {G = []} = ≼-[]
-- preserves-refl {G = x ∷ G} = ≼-∷ preserves-refl

data Extends : (G : SCtx) (G' : SCtx) → Set where
  ≼-preserve : ∀ {G} → Extends G G
  ≼-extend : ∀ {G G'} → Extends G G' → Extends G (nothing ∷ G')

data Augments : (G : SCtx) (G' : SCtx) → Set where
  ≼-augments-ext : ∀ {G G'} → Extends G G' → Augments G G'
  ≼-augments-new : ∀ {G G' s} → Extends G G' → Augments G (just (s , POSNEG) ∷ G')

extends-refl : ∀ {G : SCtx} → Extends G G
extends-refl {G = []} = ≼-preserve
extends-refl {G = x ∷ G} = ≼-preserve

extends-trans : ∀ {G₀ : SCtx}{G₁ : SCtx}{G₂ : SCtx}
  → Extends G₀ G₁ → Extends G₁ G₂ → Extends G₀ G₂
extends-trans ≼-preserve ≼-preserve = ≼-preserve
extends-trans ≼-preserve (≼-extend e02) = ≼-extend e02
extends-trans (≼-extend e01) ≼-preserve = ≼-extend e01
extends-trans (≼-extend e01) (≼-extend e02) = ≼-extend (extends-trans (≼-extend e01) e02)

-- | a global context evolves to another in a later stage of evaluation. almost anything can happen...
data Evolves : (G G' : SCtx) → Set where
  evolve-[] : Evolves [] []
  evolve-∷  : ∀ {G G' x x'} → Evolves G G' → Evolves (x ∷ G) (x' ∷ G')

evolves-refl : {G : SCtx} → Evolves G G
evolves-refl {[]} = evolve-[]
evolves-refl {x ∷ G} = evolve-∷ evolves-refl

data Enhances : (G G' : SCtx) → Set where
  enhance-evolve : ∀ {G G'} → Evolves G G' → Enhances G G'
  enhance-extend : ∀ {G G' x'} → Enhances G G' → Enhances G (x' ∷ G')

enhances-refl : {G : SCtx} → Enhances G G
enhances-refl = enhance-evolve evolves-refl

data EvolveableChannel : {s : STy} (G G' : SCtx) (G↝G' : Evolves G G') (v : Val' G (TChan s)) → Set where
  evolveChan-here-pos : ∀ {G G' G↝G' s} → EvolveableChannel{s} (just (s , POS) ∷ G) (just (s , POS) ∷ G') (evolve-∷ G↝G') (VChan true here-pos)
  evolveChan-here-neg : ∀ {G G' G↝G' s} → EvolveableChannel{dual s} (just (s , NEG) ∷ G) (just (s , NEG) ∷ G') (evolve-∷ G↝G') (VChan false here-neg)
  evolveChan-here-posneg : ∀ {G G' G↝G' b s} → EvolveableChannel{xdual b s} (just (s , POSNEG) ∷ G) (just (s , POSNEG) ∷ G') (evolve-∷ G↝G') (VChan b here-posneg)
  evolveChan-there : ∀ {x x' G G' G↝G' b s vcr} → EvolveableChannel{s} G G' G↝G' (VChan b vcr) → EvolveableChannel{s} (x ∷ G) (x' ∷ G') (evolve-∷ G↝G') (VChan b (there vcr))

evolveable-channel-relf : {s : STy} (G : SCtx) (v : Val' G (TChan s)) → EvolveableChannel G G evolves-refl v
evolveable-channel-relf [] (VChan b ())
evolveable-channel-relf (.(just (_ , POS)) ∷ G) (VChan .true here-pos) = evolveChan-here-pos
evolveable-channel-relf (.(just (_ , NEG)) ∷ G) (VChan .false here-neg) = evolveChan-here-neg
evolveable-channel-relf (.(just (_ , POSNEG)) ∷ G) (VChan b here-posneg) = evolveChan-here-posneg
evolveable-channel-relf (x ∷ G) (VChan b (there vcr)) = evolveChan-there (evolveable-channel-relf G (VChan b vcr))

data EvolveableValue : {t : Ty} (G G' : SCtx) (G↝G' : Evolves G G') (v : Val' G t) → Set where
  evolveUnit : ∀ {G G' G↝G'} → EvolveableValue G G' G↝G' VUnit
  evolveInt : ∀ {G G' G↝G' i} → EvolveableValue G G' G↝G' (VInt i)
  evolvePair : ∀ {G G' G↝G' t₁ t₂ v₁ v₂} → EvolveableValue{t₁} G G' G↝G' v₁ → EvolveableValue{t₂} G G' G↝G' v₂ → EvolveableValue G G' G↝G' (VPair v₁ v₂)
  evolveChan : ∀ {G G' G↝G' s v} → EvolveableChannel{s} G G' G↝G' v → EvolveableValue{TChan s} G G' G↝G' v

evolveable-value-refl : {t : Ty} (G : SCtx) (v : Val' G t) → EvolveableValue G G evolves-refl v
evolveable-value-refl G VUnit = evolveUnit
evolveable-value-refl G (VInt i) = evolveInt
evolveable-value-refl G (VPair v v₁) = evolvePair (evolveable-value-refl G v) (evolveable-value-refl G v₁)
evolveable-value-refl G (VChan b vcr) = evolveChan (evolveable-channel-relf G (VChan b vcr))

data EnhanceableChannel : {s : STy} (G G' : SCtx) (G↝G' : Enhances G G') (v : Val' G (TChan s)) → Set where
  enhanceEvolve : ∀ {G G' G↝G' s v} → EvolveableValue{TChan s} G G' G↝G' v → EnhanceableChannel G G' (enhance-evolve G↝G') v
  enhanceExtend : ∀ {G G' G↝G' s v x} → EnhanceableChannel{s} G G' G↝G' v → EnhanceableChannel G (x ∷ G') (enhance-extend G↝G') v

enhanceable-channel-refl : {s : STy} (G : SCtx) (v : Val' G (TChan s))  → EnhanceableChannel G G enhances-refl v
enhanceable-channel-refl G v = enhanceEvolve (evolveable-value-refl G v)

data EnhanceableValue : {t : Ty} (G G' : SCtx) (G↝G' : Enhances G G') (v : Val' G t) → Set where
  enhanceUnit : ∀ {G G' G↝G' v} → EnhanceableValue{TUnit} G G' G↝G' v
  enhanceInt  : ∀ {G G' G↝G' v} → EnhanceableValue{TInt} G G' G↝G' v
  enhanceChan : ∀ {G G' G↝G' s v} → EnhanceableChannel{s} G G' G↝G' v → EnhanceableValue G G' G↝G' v
  enhancePair : ∀ {G G' G↝G' t₁ t₂ v₁ v₂} → EnhanceableValue{t₁} G G' G↝G' v₁ → EnhanceableValue{t₂} G G' G↝G' v₂ → EnhanceableValue G G' G↝G' (VPair v₁ v₂)

enhanceable-value-refl : {t : Ty} (G : SCtx) (v : Val' G t) → EnhanceableValue G G enhances-refl v
enhanceable-value-refl G VUnit = enhanceUnit
enhanceable-value-refl G (VInt i) = enhanceInt
enhanceable-value-refl G (VPair v v₁) = enhancePair (enhanceable-value-refl G v) (enhanceable-value-refl G v₁)
enhanceable-value-refl G (VChan b vcr) = enhanceChan (enhanceable-channel-refl G (VChan b vcr))

liftEvolvableChannel :  {s : STy} {G G' : SCtx} (G↝G' : Evolves G G') (v : Val' G (TChan s)) (ec : EvolveableChannel{s} G G' G↝G' v) → Val' G' (TChan s)
liftEvolvableChannel .(evolve-∷ _) .(VChan true here-pos) evolveChan-here-pos = VChan true here-pos
liftEvolvableChannel .(evolve-∷ _) .(VChan false here-neg) evolveChan-here-neg = VChan false here-neg
liftEvolvableChannel .(evolve-∷ _) (VChan b here-posneg) evolveChan-here-posneg = VChan b here-posneg
liftEvolvableChannel (evolve-∷ G↝G') (VChan b (there vcr)) (evolveChan-there ec) with liftEvolvableChannel G↝G' (VChan b vcr) ec
liftEvolvableChannel (evolve-∷ G↝G') (VChan b (there vcr)) (evolveChan-there ec) | VChan b₁ vcr₁ = VChan b₁ (there vcr₁)

liftEvolvableValue : {t : Ty} {G G' : SCtx} (G↝G' : Evolves G G') (v : Val' G t) (evv : EvolveableValue G G' G↝G' v) → Val' G' t
liftEvolvableValue G↝G' VUnit evv = VUnit
liftEvolvableValue G↝G' (VInt i) evv = VInt i
liftEvolvableValue G↝G' (VPair v₁ v₂) (evolvePair evv₁ evv₂) = VPair (liftEvolvableValue G↝G' v₁ evv₁) (liftEvolvableValue G↝G' v₂ evv₂)
liftEvolvableValue G↝G' (VChan b vcr) (evolveChan x) = liftEvolvableChannel G↝G' (VChan b vcr) x

liftEnhanceableChannel : {s : STy} {G G' : SCtx} (G↝G' : Enhances G G') (v : Val' G (TChan s)) (ehc : EnhanceableChannel{s} G G' G↝G' v) → Val' G' (TChan s)
liftEnhanceableChannel (enhance-evolve eev) v (enhanceEvolve (evolveChan x)) = liftEvolvableChannel eev v x
liftEnhanceableChannel (enhance-extend ee) (VChan b vcr) (enhanceExtend ehc) with liftEnhanceableChannel ee (VChan b vcr) ehc
liftEnhanceableChannel (enhance-extend ee) (VChan b vcr) (enhanceExtend ehc) | VChan b₁ vcr₁ = VChan b₁ (there vcr₁)

liftEnhanceableValue : {t : Ty} {G G' : SCtx} (G↝G' : Enhances G G') (v : Val' G t) (ev : EnhanceableValue{t} G G' G↝G' v) → Val' G' t
liftEnhanceableValue enhance VUnit ev = VUnit
liftEnhanceableValue enhance (VInt i) ev = VInt i
liftEnhanceableValue enhance (VPair v₁ v₂) (enhancePair ev₁ ev₂) = VPair (liftEnhanceableValue enhance v₁ ev₁) (liftEnhanceableValue enhance v₂ ev₂)
liftEnhanceableValue enhance (VChan b vcr) (enhanceChan esimple) = liftEnhanceableChannel enhance (VChan b vcr) esimple

data EnhanceableVEnv : {φ : TCtx} (G G' : SCtx) (G↝G' : Enhances G G') (ϱ : VEnv' G φ) → Set where
  Enhanceable-[] : ∀ {G G' G↝G'} → EnhanceableVEnv G G' G↝G' []
  Enhanceable-∷  : ∀ {G G' G↝G' t v φ ϱ} → EnhanceableValue{t} G G' G↝G' v → EnhanceableVEnv{φ} G G' G↝G' ϱ → EnhanceableVEnv G G' G↝G' (v ∷ ϱ)

liftEnhanceableVEnv : {φ : TCtx} {G G' : SCtx} (G↝G' : Enhances G G') (ϱ : VEnv' G φ) (evv : EnhanceableVEnv G G' G↝G' ϱ) → VEnv' G' φ
liftEnhanceableVEnv G↝G' [] Enhanceable-[] = []
liftEnhanceableVEnv G↝G' (v ∷ ϱ) (Enhanceable-∷ ev evv) = liftEnhanceableValue G↝G' v ev ∷ liftEnhanceableVEnv G↝G' ϱ evv

enhanceable-venv-refl : {φ : TCtx} (G : SCtx) (ϱ : VEnv' G φ) → EnhanceableVEnv G G enhances-refl ϱ
enhanceable-venv-refl G [] = Enhanceable-[]
enhanceable-venv-refl G (v ∷ ϱ) with enhanceable-venv-refl G ϱ
... | evr = Enhanceable-∷ {!!} evr

-- liftVCR : ∀ {n} {b} {s} → (k : ℕ) (G : SCtx n) (G' : SCtx (k + n)) (vcr : ValidChannelRef' G b s) → ValidChannelRef' G' b s
-- liftVCR zero G G' vcr = {!!}  -- here I need to know that G = G'
-- liftVCR (suc k) G (x ∷ G') vcr = there (liftVCR k G G' vcr)

-- liftVal : ∀ {n} {t} → (k : ℕ) (G : SCtx n) (G' : SCtx (k + n)) (v : Val' G t) → (Val' G' t)
-- liftVal k G G' (VInt i) = VInt i
-- liftVal k G G' (VPair v₁ v₂) = VPair (liftVal k G G' v₁) (liftVal k G G' v₂)
-- liftVal k G G' (VChan b vcr) = VChan b (liftVCR k G G' vcr)

-- liftVEnv : ∀ {n} {φ} → (k : ℕ) (G : SCtx n) (G' : SCtx (k + n)) (ϱ : VEnv' G φ) → (VEnv' G' φ)
-- liftVEnv k G G' [] = []
-- liftVEnv k G G' (x ∷ ϱ) = liftVal k G G' x ∷ liftVEnv k G G' ϱ

liftVCR : ∀ {b s} {G : SCtx} {G' : SCtx}
         → (ex : Extends G G') (vcr : ValidChannelRef' G b s) → (ValidChannelRef' G' b s)
liftVCR ex vcr = {!!}
-- liftVCR {k = zero} ≼-[] ()
-- liftVCR {k = zero} (≼-preserve ex) here-pos = here-pos
-- liftVCR {k = zero} (≼-preserve ex) here-neg = here-neg
-- liftVCR {k = zero} (≼-preserve ex) here-posneg = here-posneg
-- liftVCR {k = zero} (≼-preserve ex) (there vcr) = there (liftVCR ex vcr)
-- liftVCR {k = suc k} (≼-extend ex) vcr = there (liftVCR ex vcr)

liftVal : ∀ {t} {G : SCtx} {G' : SCtx}
         → (ex : Extends G G') (v : Val' G t) → (Val' G' t)
liftVal ex VUnit = VUnit
liftVal ex (VInt i) = VInt i
liftVal ex (VPair v v₁) = VPair (liftVal ex v) (liftVal ex v₁)
liftVal ex (VChan b vcr) = VChan b (liftVCR ex vcr)

liftVEnv : ∀ {φ} {G : SCtx} {G' : SCtx}
         → (ex : Extends G G') (ϱ : VEnv' G φ) → (VEnv' G' φ)
liftVEnv ex [] = []
liftVEnv ex (x ∷ ϱ) = liftVal ex x ∷ liftVEnv ex ϱ

data RelateVCR : ∀ { b s}
  → (G : SCtx) (G' : SCtx)
  → (vcr : ValidChannelRef' G b s) (vcr' : ValidChannelRef' G' b s) → Set where
  vcr-extend : ∀ {b s G G' x' vcr vcr'}
    → RelateVCR{b}{s} G G' vcr vcr'
    → RelateVCR{b}{s} G (x' ∷ G') vcr (there vcr')
  
{-
data RelateVal : ∀ { t} → (G : SCtx) (G' : SCtx) (v : Val' G t) (v' : Val' G' t) → Set where
  val-int : ∀ {G G' i} → RelateVal G G' (VInt i) (VInt i)
  val-pair : ∀ {G G' t₁ t₂  v₁ v₁'  v₂ v₂'}
           → RelateVal{t₁} G G' v₁ v₁'
           → RelateVal{t₂} G G' v₂ v₂'
           → RelateVal G G' (VPair v₁ v₂) (VPair v₁' v₂')
  val-chan : ∀ {G G' b s vcr vcr'}
           → RelateVCR{b} G G' vcr vcr'
           → RelateVal{TChan s} G G' (VChan b vcr) (VChan b vcr')

data RelateVEnv : ∀ {φ} → (G : SCtx) (G' : SCtx) (ϱ : VEnv' G φ) (ϱ' : VEnv' G' φ) → Set where
  [] : ∀ {G G'} → RelateVEnv G G' [] []
  _∷_ : ∀ { G G' t φ v v' ϱ ϱ'} → RelateVal{t} G G' v v' → RelateVEnv{φ} G G' ϱ ϱ' → RelateVEnv G G' (v ∷ ϱ) (v' ∷ ϱ')
-}
  

data Command' (G : SCtx) (t : Ty) : Set where
  Return : Val' G t → Command' G t
  Bind   : ∀ {t'}
         → Command' G t'
         → (Val' G t' →  (G' : SCtx ) (ex : Extends G G') → Command' G' t)
         → Command' G t

run' : ∀ {φ t G}
  → Expr φ t 
  → VEnv' G φ
  → Command' G t
run' (var x) ϱ = Return (access' ϱ x)
run' (nat i) ϱ = {!!}
run' {G = G} (letbind sp e e₁) ϱ  with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = Bind (run' e ϱ₁) λ v G' ex → run' e₁ (liftVEnv ex (v  ∷ ϱ₂))
run' (pair sp x₁ x₂) ϱ = {!!}
run' (letpair sp x e) ϱ = {!!}
run' (fork e) ϱ = {!!}
run' (new s) ϱ = {!!}
-- run' (send sp ch vv) ϱ = {!!}
-- run' (recv ch) ϱ = {!!}
run' (close ch) ϱ = {!!}
run' (wait ch) ϱ = {!!}

--
-- every instant it must be the case that φ covers G, which means that φ has exactly the channels available in G
useChannel : ∀ {s} → (G : SCtx)  (b : Bool) → (vcr : ValidChannelRef' G b s) → SCtx
useChannel (just (_ , POS) ∷ G) .true here-pos = nothing ∷ G
useChannel (just (_ , NEG) ∷ G) .false here-neg = nothing ∷ G
useChannel (just (s , POSNEG) ∷ G) false here-posneg = just (s , POS) ∷ G
useChannel (just (s , POSNEG) ∷ G) true here-posneg = just (s , NEG) ∷ G
useChannel (x ∷ G) b (there vcr) = x ∷ useChannel G b vcr

useValue : ∀ {t} → (G : SCtx) (v : Val' G t) → SCtx
useValue G VUnit = G
useValue G (VInt i) = G
useValue G (VPair v v₁) = {!!} (useValue G v) (useValue G v₁)
useValue G (VChan b vcr) = useChannel G b vcr


-- a continuation closure
Cont : Ty → SCtx → TCtx → Set

inactive-ssplit : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₁ → G ≡ G₂
inactive-ssplit ss-[] []-inactive = refl
inactive-ssplit (ss-both ss) (::-inactive G inG₁) = cong (_∷_ nothing) (inactive-ssplit ss inG₁)
inactive-ssplit (ss-right ss) (::-inactive G inG₁) = cong (_∷_ (just _)) (inactive-ssplit ss inG₁)

ssplit-inactive-left : (G : SCtx) → Σ (SCtx × SCtx) λ{ ( G₁ , G₂ ) → SSplit G G₁ G₂ }
ssplit-inactive-left [] = ( [] , [] ) , ss-[]
ssplit-inactive-left (x ∷ G) with ssplit-inactive-left G
ssplit-inactive-left (just x ∷ G) | (G₁ , G₂) , ss =  (nothing ∷ G₁ , just x ∷ G₂) , ss-right ss 
ssplit-inactive-left (nothing ∷ G) | (G₁ , G₂) , ss = (nothing ∷ G₁ , nothing ∷ G₂) , ss-both ss

join-ssplit : { G₁₁ G₁₂ G₂₁ G₂₂ : SCtx} (G : SCtx) (ss₁ : SSplit G G₁₁ G₁₂) (ss₂ : SSplit G G₂₁ G₂₂) → Σ (SCtx × SCtx) λ{ ( G₁ , G₂ ) → SSplit G G₁ G₂ }
join-ssplit [] ss₁ ss₂ = ([] , []) , ss-[]
join-ssplit (.nothing ∷ G) (ss-both ss₁) (ss-both ss₂) with join-ssplit G ss₁ ss₂
join-ssplit (.nothing ∷ G) (ss-both ss₁) (ss-both ss₂) | (G₁ , G₂) , ss = (nothing ∷ G₁ , nothing ∷ G₂) , ss-both ss
join-ssplit ((just x) ∷ G) (ss-left ss₁) (ss-left ss₂) with join-ssplit G ss₁ ss₂
... | (G₁ , G₂) , ss = (just x ∷ G₁ , nothing ∷ G₂) , ss-left ss
join-ssplit (.(just _) ∷ G) (ss-left ss₁) (ss-right ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-left ss₁) (ss-posneg ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-left ss₁) (ss-negpos ss₂) = {!!}
join-ssplit (.(just _) ∷ G) (ss-right ss₁) (ss-left ss₂) = {!!}
join-ssplit (.(just _) ∷ G) (ss-right ss₁) (ss-right ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-right ss₁) (ss-posneg ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-right ss₁) (ss-negpos ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-posneg ss₁) (ss-left ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-posneg ss₁) (ss-right ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-posneg ss₁) (ss-posneg ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-posneg ss₁) (ss-negpos ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-negpos ss₁) (ss-left ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-negpos ss₁) (ss-right ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-negpos ss₁) (ss-posneg ss₂) = {!!}
join-ssplit (.(just (_ , POSNEG)) ∷ G) (ss-negpos ss₁) (ss-negpos ss₂) = {!!}

fork-context-value : ∀ {t} → (G : SCtx) → Val' G t → Σ (SCtx × SCtx) λ{ ( G₁ , G₂ ) → SSplit G G₁ G₂ }
fork-context-value G (VUnit) = ssplit-inactive-left G
fork-context-value G (VInt i) = ssplit-inactive-left G
fork-context-value G (VPair v₁ v₂) with fork-context-value G v₁ | fork-context-value G v₂
fork-context-value G (VPair v₁ v₂) | (G₁₁ , G₁₂) , ss₁ | (G₂₁ , G₂₂) , ss₂ = ({!!} , {!!}) , {!!}
fork-context-value G (VChan b vcr) = {!!}

fork-context : ∀ {φ} → (G G' : SCtx) → VEnv' G φ → Σ (SCtx × SCtx) λ{ ( G₁ , G₂ ) → SSplit G' G₁ G₂ }
fork-context G [] ϱ =  ( [] , [] ) , ss-[]
fork-context G (just x ∷ G') ϱ = {!!}
fork-context G (nothing ∷ G') ϱ with fork-context G G' ϱ
fork-context G (nothing ∷ G') ϱ | (G₁' , G₂') , proj₃ = ( nothing ∷ G₁' , nothing ∷ G₂' ) , ss-both proj₃

data Command'' (G : SCtx) : Set where
  Fork : ∀ {φ φ' G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → Cont TUnit G₁ φ
    → Cont TUnit G₂ φ'
    → Command'' G
  Halt : Command'' G
  New : ∀ {φ}
    → (s : STy)
    → Cont (TPair (TChan s) (TChan (dual s))) G φ
    → Command'' G
  Close : ∀ {φ} → Val' G (TChan SEnd!) → Cont TUnit G φ → Command'' G
  Wait  : ∀ {φ} → Val' G (TChan SEnd?) → Cont TUnit G φ → Command'' G

-- Cont t G φ = (G' : SCtx) → Augments G G' → (VEnv' G' φ × (Val' G' t → VEnv' G' φ → Command'' G'))
-- this is really a continuation closure
Cont t G φ = Σ (VEnv'' G φ) λ ϱ → (G' : SCtx) (G↝G' : Enhances G G') → EnhanceableVEnv G G' G↝G' ϱ → (Val'' G' t → VEnv'' G' φ → Command'' G')

halt-cont : ∀ { G} → Cont TUnit G []
halt-cont = [] , (λ G' G↝G' _ → (λ x x₁ → Halt))

apply-cont : ∀ {G t φ} → (κ : Cont t G φ) → (G' : SCtx) → (G↝G' : Enhances G G') (evenv : EnhanceableVEnv G G' G↝G' (proj₁ κ)) → Val' G' t → Command'' G'
apply-cont{G} (ϱ , c) G' G↝G' evenv v' = c G' G↝G' evenv v' (liftEnhanceableVEnv{G = G} G↝G' ϱ evenv)


-- everything is valid in the current global channel environment G, but the continuation will be executed in an enhanced environment
run'' : ∀ {φ φ₁ φ₂ t G}
  → Split φ φ₁ φ₂
  → Expr φ₁ t
  → VEnv'' G φ₁
  → Cont t G φ₂
  → Command'' G
run'' sp (var x) ϱ κ = {!!}
run'' sp (nat i) ϱ κ = {!!}
run'' sp (letbind sp₁ e e₁) ϱ κ = {!!}
run'' sp (pair sp₁ x₁ x₂) ϱ κ = {!!}
run'' sp (letpair sp₁ x e) ϱ κ = {!!}
run'' sp (fork e) ϱ κ = {!!}
run'' sp (new s) ϱ κ = {!!}
run'' sp (close ch) ϱ κ = {!!}
run'' sp (wait ch) ϱ κ = {!!}

-- run'' (var x) ϱ κ =
--   apply-cont κ _ (≼-augments-ext extends-refl) (access' ϱ x)
-- run'' (nat i) ϱ κ =
--   apply-cont κ _ (≼-augments-ext extends-refl) (VInt i)
-- run''{G = G} (letbind sp₁ e e₁) ϱ κ with split-env' sp₁ ϱ
-- ... | ϱ₁ , ϱ₂ = run''{G = G} e ϱ₁ λ G' G≼G' →
--     liftVEnv G≼G' ϱ₂ , λ v ϱ₂' → run''{G = G'} e₁ (v ∷ ϱ₂') λ G'' G'≼G'' →
--     liftVEnv G'≼G'' ϱ₂' , λ v ϱ₂'' → apply-cont κ G'' (extends-trans G≼G' G'≼G'') v 
-- run'' (pair sp₁ x₁ x₂) ϱ κ with split-env' sp₁ ϱ
-- ... | ϱ₁ , ϱ₂ = apply-cont κ _ extends-refl (VPair (access' ϱ₁ x₁) (access' ϱ₂ x₂))
-- run'' (letpair sp₁ x e) ϱ κ with split-env' sp₁ ϱ
-- ... | ϱ₁ , ϱ₂ with access' ϱ₁ x
-- run'' (letpair sp₁ x e) ϱ κ | ϱ₁ , ϱ₂ | VPair vp vp₁ = run'' e (vp ∷ vp₁ ∷ ϱ₂) κ
-- run''{G = G} (fork e) ϱ κ = Fork {!!} {!!} {!!}
--   -- Fork {!!} (ϱ , λ _ ϱ → run'' e ϱ (λ G' G≼G' → halt-cont {!!})) {!!}
-- run'' (new s) ϱ κ = New s {!!}
-- run'' (close ch) ϱ κ = Close (access' ϱ ch) {!!}
-- run'' (wait ch) ϱ κ = Wait (access' ϱ ch) {!!}

-- data ThreadPool (G : SCtx) : Set where
--   nil : (ina : Inactive G) → ThreadPool G
--   cons : ∀ {G₁ G₂} → (ss : SSplit G G₁ G₂) → (cmd : Command'' G₁) → (tp : ThreadPool G₂) → ThreadPool G


-- liftVal' : ∀ {G t} → Val' G t → Val' (nothing ∷ G) t
-- liftVal' VUnit = VUnit
-- liftVal' (VInt i) = VInt i
-- liftVal' (VPair v v₁) = VPair (liftVal' v) (liftVal' v₁)
-- liftVal' (VChan b vcr) = VChan b (there vcr)

-- liftCont : ∀ {t G φ} → Cont t G φ → Cont t (nothing ∷ G) φ
-- liftCont κ = (λ G' Gn≼G' → κ G' (extends-trans (≼-extend ≼-preserve) Gn≼G'))

-- liftCMD : ∀ {G} → Command'' G → Command'' (nothing ∷ G)
-- liftCMD (Fork ss κ κ₁) =
--   Fork (ss-both ss) (liftCont κ) (liftCont κ₁)
-- liftCMD Halt = Halt
-- liftCMD (New s κ) =
--   New s (liftCont κ)
-- liftCMD (Close x κ) =
--   Close (liftVal' x) (liftCont κ)
-- liftCMD (Wait x κ) =
--   Wait (liftVal' x) (liftCont κ)

-- liftTP : ∀ {G} → ThreadPool G → ThreadPool (nothing ∷ G)
-- liftTP (nil ina) = nil (::-inactive _ ina)
-- liftTP (cons ss cmd tp) = cons (ss-both ss) (liftCMD cmd) (liftTP tp)

-- ssplit-compose2 : (G G₁ G₂ G₂₁ G₂₂ : SCtx)
--   → SSplit G G₁ G₂
--   → SSplit G₂ G₂₁ G₂₂
--   → Σ SCtx λ Gi → (SSplit G Gi G₂ × SSplit Gi G₁ G₂₂)
-- ssplit-compose2 G G₁ G₂ G₂₁ G₂₂ ss ss₂ = {!!}




-- vcr-match : ∀ {G G₁ G₂ b₁ b₂ s₁ s₂}
--   → SSplit G G₁ G₂
--   → ValidChannelRef' G₁ b₁ s₁
--   → ValidChannelRef' G₂ b₂ s₂
--   → Maybe (b₁ ≡ not b₂ × s₁ ≡ dual s₂)
-- vcr-match ss-[] () vcr₂
-- vcr-match (ss-both ss) (there vcr₁) (there vcr₂) = vcr-match ss vcr₁ vcr₂
-- vcr-match (ss-left ss) here-pos (there vcr₂) = nothing
-- vcr-match (ss-left ss) here-neg (there vcr₂) = nothing
-- vcr-match (ss-left ss) here-posneg (there vcr₂) = nothing
-- vcr-match (ss-left ss) (there vcr₁) (there vcr₂) = vcr-match ss vcr₁ vcr₂
-- vcr-match (ss-right ss) (there vcr₁) here-pos = nothing
-- vcr-match (ss-right ss) (there vcr₁) here-neg = nothing
-- vcr-match (ss-right ss) (there vcr₁) here-posneg = nothing
-- vcr-match (ss-right ss) (there vcr₁) (there vcr₂) = vcr-match ss vcr₁ vcr₂
-- vcr-match (ss-posneg ss) here-pos here-neg = just ( refl , sym (dual-involution _))
-- vcr-match (ss-posneg ss) here-pos (there vcr₂) = nothing
-- vcr-match (ss-posneg ss) (there vcr₁) here-neg = nothing
-- vcr-match (ss-posneg ss) (there vcr₁) (there vcr₂) = vcr-match ss vcr₁ vcr₂
-- vcr-match (ss-negpos ss) here-neg here-pos = just (refl , refl)
-- vcr-match (ss-negpos ss) here-neg (there vcr₂) = nothing
-- vcr-match (ss-negpos ss) (there vcr₁) here-pos = nothing
-- vcr-match (ss-negpos ss) (there vcr₁) (there vcr₂) = vcr-match ss vcr₁ vcr₂


-- findMatchingWait : ∀ {G G₁ G₂}
--   → SSplit G G₁ G₂
--   → Val' G₁ (TChan SEnd!)
--   → ThreadPool G₂
--   → Maybe (Σ SCtx λ G' → Val' G' (TChan SEnd?))
-- findMatchingWait ss v (nil ina) = nothing
-- findMatchingWait ss v (cons ss₁ (Fork ss₂ x x₁) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
-- findMatchingWait ss v (cons ss₁ (Fork ss₂ x x₁) tp) | G' , _ , ss' = findMatchingWait ss' v tp
-- findMatchingWait ss v (cons ss₁ Halt tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
-- ... | G' , _ , ss' = findMatchingWait ss' v tp
-- findMatchingWait ss v (cons ss₁ (New s κ) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
-- ... | G' , _ , ss' = findMatchingWait ss' v tp
-- findMatchingWait ss v (cons ss₁ (Close v' κ) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
-- ... | G' , _ , ss' = findMatchingWait ss' v tp
-- findMatchingWait ss (VChan b vcr) (cons ss₁ (Wait (VChan b₁ vcr₁) κ) tp) with b xor b₁ | ssplit-compose2 _ _ _ _ _ ss ss₁
-- findMatchingWait ss (VChan b vcr) (cons ss₁ (Wait (VChan b₁ vcr₁) κ) tp) | false | G' , _ , ss' = findMatchingWait ss' (VChan b vcr) tp
-- findMatchingWait ss (VChan b vcr) (cons ss₁ (Wait (VChan b₁ vcr₁) κ) tp) | true | G' , ss'' , ss' with ssplit-compose3 _ _ _ _ _ ss ss₁
-- findMatchingWait ss (VChan b vcr) (cons ss₁ (Wait (VChan b₁ vcr₁) κ) tp) | true | G' , ss'' , ss' | Gi , ssi4 , ssi13 with vcr-match ssi13 vcr vcr₁
-- findMatchingWait ss (VChan b vcr) (cons ss₁ (Wait (VChan b₁ vcr₁) κ) tp) | true | G' , ss'' , ss' | Gi , ssi4 , ssi13 | just x = just (_ , VChan b₁ vcr₁)
-- findMatchingWait ss (VChan b vcr) (cons ss₁ (Wait (VChan b₁ vcr₁) κ) tp) | true | G' , ss'' , ss' | Gi , ssi4 , ssi13 | nothing = findMatchingWait ss' (VChan b vcr) tp


-- data Fuel : Set where
--   Empty : Fuel
--   More  : Fuel → Fuel

-- schedule : Fuel → (G : SCtx) → ThreadPool G → ⊤
-- schedule Empty G tp = tt
-- schedule (More f) G (nil ina) = tt
-- schedule (More f) G (cons ss (Fork ss₁ κ κ₁) tp) with ssplit-compose _ _ _ _ _ ss ss₁
-- ... | Gi , ss₁₃ , ss₂₄ = schedule f G (cons ss₁₃ (apply-cont κ _ ≼-preserve VUnit) (cons ss₂₄ (apply-cont κ₁ _ ≼-preserve VUnit) tp))
-- schedule (More f) G (cons ss Halt tp) = schedule f _ tp
-- schedule (More f) G (cons ss (New s κ) tp) = 
--   schedule f (just (s , POSNEG) ∷ G)
--              (cons (ss-left ss)
--                    (apply-cont κ (just (s , POSNEG) ∷ _) {!!}   -- (≼-extend ≼-preserve)
--                      (VPair (VChan true here-posneg) (VChan false here-posneg)))
--                    (liftTP tp))
-- schedule (More f) G (cons ss (Close x κ) tp) =
--   {!!}
-- schedule (More f) G (cons ss (Wait x κ) tp) =
--   {!!}

-- start : Fuel → Expr [] TUnit → ⊤
-- start f e = schedule f [] (cons ss-[] (run'' e [] λ G' []≼G' → [] , λ _ _ → Halt) (nil []-inactive))
