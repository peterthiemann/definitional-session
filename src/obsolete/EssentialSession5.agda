module EssentialSession5 where

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
  SCtx : ℕ → Set
  SCtx n = Vec (Maybe (STy × PosNeg)) n

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
data SSplit : { n : ℕ} → SCtx n → SCtx n → SCtx n → Set where
  ss-[]    : SSplit [] [] []
  ss-both  : ∀ {  n G G₁ G₂ }
           → SSplit{n} G G₁ G₂
           → SSplit (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂)
  ss-left  : ∀ {  n spn G G₁ G₂ }
           → SSplit {n} G G₁ G₂
           → SSplit (just spn ∷ G) (just spn ∷ G₁) (nothing ∷ G₂)
  ss-right : ∀ {  n spn G G₁ G₂ }
           → SSplit {n} G G₁ G₂
           → SSplit (just spn ∷ G) (nothing ∷ G₁) (just spn ∷ G₂)
  ss-posneg : ∀ { n s G G₁ G₂ }
          → SSplit {n} G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , POS) ∷ G₁) (just (s , NEG) ∷ G₂)
  ss-negpos : ∀ { n s G G₁ G₂ }
          → SSplit {n} G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , NEG) ∷ G₁) (just (s , POS) ∷ G₂)

data ValidChannelRef : {n : ℕ} (G : SCtx n) (k : Fin n) (b : Bool) (s : STy) → Set where
  here-pos : ∀ {n s} {G : SCtx n}
    → ValidChannelRef (just (s , POS) ∷ G) zero true s
  here-neg : ∀ {n s} {G : SCtx n}
    → ValidChannelRef (just (s , NEG) ∷ G) zero false (dual s)
  here-posneg : ∀ {n s b} {G : SCtx n}
    → ValidChannelRef (just (s , POSNEG) ∷ G) zero b (xdual b s)
  there : ∀ {n x k b s} {G : SCtx n}
    → ValidChannelRef G k b s
    → ValidChannelRef (x ∷ G) (suc k) b s

data Val {n : ℕ} (G : SCtx n) : Ty → Set where
  VInt  : (i : ℕ) → Val G TInt
  VPair : ∀ {t₁ t₂} → (v₁ : Val G t₁) → (v₂ : Val G t₂) → Val G (TPair t₁ t₂)
  VChan : ∀ {s} → (m : Fin n) (b : Bool) → ValidChannelRef G (invert m) b s → Val G (TChan s)

-- liftVal1 : ∀ {n : ℕ} {G : SCtx n n} {t : Ty n} {x : Maybe (STy (suc n) × PosNeg)} → Val G t → Val (x ∷ liftSCtx G) (liftTy t)
-- liftVal1 (VInt n) = VInt n
-- liftVal1 (VPair v₁ v₂) = VPair (liftVal1 v₁) (liftVal1 v₂)
-- liftVal1 (VChan m b vcr) = VChan (inject₁ m) b {!liftVCR!}

-- liftValK : ∀ {n : ℕ} {G : SCtx n n} {t : Ty n} (k : ℕ) {H : Vec (Maybe (STy (k + n) × PosNeg)) k} → Val G t → Val (H Data.Vec.++ liftNSCtx k G) (liftNTy k t)
-- liftValK k (VInt n) = VInt n
-- liftValK {G = G} k {H} (VPair v v₁) = VPair (liftValK {G = G} k {H} v) (liftValK {G = G} k {H} v₁)
-- liftValK k (VChan m b x) = let m' = injectk+ k m in VChan m' b {!!}

-- alternative without explicitly mentioning the annoying Fin

data ValidChannelRef' : {n : ℕ} (G : SCtx n) (b : Bool) (s : STy) → Set where
  here-pos : ∀ {n s} {G : SCtx n}
    → ValidChannelRef' (just (s , POS) ∷ G) true s
  here-neg : ∀ {n s} {G : SCtx n}
    → ValidChannelRef' (just (s , NEG) ∷ G) false (dual s)
  here-posneg : ∀ {n s b} {G : SCtx n}
    → ValidChannelRef' (just (s , POSNEG) ∷ G) b (xdual b s)
  there : ∀ {n x b s} {G : SCtx n}
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

    
data Val' {n : ℕ} (G : SCtx n) : Ty → Set where
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
data VEnv {n : ℕ} (G : SCtx n) : TCtx → Set where
  [] : VEnv G []
  _∷_ : ∀{t φ} → (x : Val G t) → (ϱ : VEnv G φ) → VEnv G (t ∷ φ)

-- split environment according to type context split
split-env : ∀ {n Φ Φ₁ Φ₂} {G : SCtx n} → Split Φ Φ₁ Φ₂ → VEnv G Φ → VEnv G Φ₁ × VEnv G Φ₂
split-env [] [] = [] , []
split-env (unr x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env (linleft x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env (linrght x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- alternative
data VEnv' {n : ℕ} (G : SCtx n) : TCtx → Set where
  [] : VEnv' G []
  _∷_ : ∀{t φ} → (x : Val' G t) → (ϱ : VEnv' G φ) → VEnv' G (t ∷ φ)

-- split environment according to type context split
split-env' : ∀ {n Φ Φ₁ Φ₂} {G : SCtx n} → Split Φ Φ₁ Φ₂ → VEnv' G Φ → VEnv' G Φ₁ × VEnv' G Φ₂
split-env' [] [] = [] , []
split-env' (unr x₁ sp) (x ∷ ϱ) with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env' (linleft x₁ sp) (x ∷ ϱ) with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env' (linrght x₁ sp) (x ∷ ϱ) with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- replacing a send binding in an environment
data DeltaTransmit : (n : ℕ) (k : Fin n) (b : Bool) (G G' : SCtx n) (t : Ty) → Set where
  here-pos : ∀ {n t s G}
    → DeltaTransmit (suc n) zero true 
                 (just (SSend t s , POS) ∷ G) (just (s , POS) ∷ G) t
  here-neg : ∀ {n t s G}
    → DeltaTransmit (suc n) zero false
                 (just (SRecv t s , NEG) ∷ G) (just (s , NEG) ∷ G) t
  there : ∀ {n k b G G' t x x'}
    → DeltaTransmit n k b G G' t
    → DeltaTransmit (suc n) (suc k) b (x ∷ G) (x' ∷ G') t

data DeltaClose : (n : ℕ) (k : Fin n) (b : Bool) (G G' : SCtx n) → Set where
  here-close-pos : ∀ {n G}
    → DeltaClose (suc n) zero true (just (SEnd! , POS) ∷ G) (nothing ∷ G)
  here-wait-pos : ∀ {n G}
    → DeltaClose (suc n) zero false (just (SEnd? , POS) ∷ G) (nothing ∷ G)
  here-close-neg : ∀ {n G}
    → DeltaClose (suc n) zero true (just (SEnd? , NEG) ∷ G) (nothing ∷ G)
  here-wait-neg : ∀ {n G}
    → DeltaClose (suc n) zero false (just (SEnd! , NEG) ∷ G) (nothing ∷ G)
  there : ∀ {n k b G G' x x'}
    → DeltaClose n k b G G'
    → DeltaClose (suc n) (suc k) b (x ∷ G ) (x' ∷ G')

-- expressions
data Expr : (φ : TCtx) → Ty → Set where
  var : ∀ {t φ}
      → (x : t ∈ φ)
      → Expr φ t

  nat : ∀ {φ}
      → (i : ℕ)
      → Expr φ TInt

  lety : ∀ {φ φ₁ φ₂ t₁ t₂}
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
      → (ch : (TChan SEnd!) ∈ φ)
      → Expr φ TUnit

  wait : ∀ { φ}
      → (ch : (TChan SEnd?) ∈ φ)
      → Expr φ TUnit



-- data CEnv {n : ℕ} (G : SCtx n n) : Set where
--   [] : CEnv G
--   _∷_ : ∀ {G} → (spn : STy × PosNeg) → (ψ : CEnv G) → CEnv (spn ∷ G)

access : ∀ {n φ t} {G : SCtx n} → VEnv G φ → t ∈ φ → Val G t
access (x ∷ ϱ) here = x
access (x ∷ ϱ) (there x₁) = access ϱ x₁

access' : ∀ {n φ t} {G : SCtx n} → VEnv' G φ → t ∈ φ → Val' G t
access' (x ∷ ϱ) here = x
access' (x ∷ ϱ) (there x₁) = access' ϱ x₁

data Command (A : Set) : Set where
  Return : (x : A) → Command A

_>>=_ : ∀ {A B : Set} → Command A → (A → Command B) → Command B
Return x >>= fab = fab x


run : ∀ {φ t n G}
  → Expr φ t 
  → VEnv'{n} G φ → Command (Val' G t)
run (var x) ϱ = Return (access' ϱ x)
run (nat i) ϱ = Return (VInt i)
run (lety sp e e₁) ϱ with split-env' sp ϱ
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

data Extends : {n : ℕ} (G : SCtx n) (k : ℕ) (G' : SCtx (k + n)) → Set where
  ≼-[] : Extends [] zero []
  ≼-preserve : ∀ {n G G' x} → Extends {n} G zero G' → Extends {suc n} (just x ∷ G) zero (just x ∷ G')
  ≼-appear : ∀ {n G G' x} → Extends {n} G zero G' → Extends {suc n} (nothing ∷ G) zero (just x ∷ G')
  ≼-disappear : ∀ {n G G' x} → Extends {n} G zero G' → Extends {suc n} (just x ∷ G) zero (nothing ∷ G')
  ≼-extend : ∀ {n G k G' x} → Extends {n} G  k G' → Extends {n} G (suc k) (x ∷ G')

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

liftVCR : ∀ {n b s} {k} {G : SCtx n} {G' : SCtx (k + n)}
         → (ex : Extends G k G') (vcr : ValidChannelRef' G b s) → (ValidChannelRef' G' b s)
liftVCR {k = zero} ≼-[] ()
liftVCR {k = zero} (≼-preserve ex) here-pos = here-pos
liftVCR {k = zero} (≼-preserve ex) here-neg = here-neg
liftVCR {k = zero} (≼-preserve ex) here-posneg = here-posneg
liftVCR {k = zero} (≼-preserve ex) (there vcr) = there (liftVCR ex vcr)
liftVCR {k = zero} (≼-appear ex) (there vcr) = there (liftVCR ex vcr)
liftVCR {k = zero} (≼-disappear ex) here-pos = {!!}
liftVCR {k = zero} (≼-disappear ex) here-neg = {!!}
liftVCR {k = zero} (≼-disappear ex) here-posneg = {!!}
liftVCR {k = zero} (≼-disappear ex) (there vcr) = there (liftVCR ex vcr)
liftVCR {k = suc k} (≼-extend ex) vcr = there (liftVCR ex vcr)

liftVal : ∀ {n} {t} {k} {G : SCtx n} {G' : SCtx (k + n)}
         → (ex : Extends G k G') (v : Val' G t) → (Val' G' t)
liftVal ex (VInt i) = VInt i
liftVal ex (VPair v v₁) = VPair (liftVal ex v) (liftVal ex v₁)
liftVal ex (VChan b vcr) = VChan b (liftVCR ex vcr)

liftVEnv : ∀ {n} {φ} {k} {G : SCtx n} {G' : SCtx (k + n)}
         → (ex : Extends G k G') (ϱ : VEnv' G φ) → (VEnv' G' φ)
liftVEnv ex [] = []
liftVEnv ex (x ∷ ϱ) = liftVal ex x ∷ liftVEnv ex ϱ

data RelateVCR : ∀ {n k b s}
  → (G : SCtx n) (G' : SCtx (k + n))
  → (vcr : ValidChannelRef' G b s) (vcr' : ValidChannelRef' G' b s) → Set where
  vcr-extend : ∀ {n k b s G G' x' vcr vcr'}
    → RelateVCR{n}{k}{b}{s} G G' vcr vcr'
    → RelateVCR{n}{suc k}{b}{s} G (x' ∷ G') vcr (there vcr')
  

data RelateVal : ∀ {n k t} → (G : SCtx n) (G' : SCtx (k + n)) (v : Val' G t) (v' : Val' G' t) → Set where
  val-int : ∀ {n k G G' i} → RelateVal{n}{k} G G' (VInt i) (VInt i)
  val-pair : ∀ {n k G G' t₁ t₂  v₁ v₁'  v₂ v₂'}
           → RelateVal{n}{k}{t₁} G G' v₁ v₁'
           → RelateVal{n}{k}{t₂} G G' v₂ v₂'
           → RelateVal{n}{k} G G' (VPair v₁ v₂) (VPair v₁' v₂')
  val-chan : ∀ {n k G G' b s vcr vcr'}
           → RelateVCR{n}{k}{b} G G' vcr vcr'
           → RelateVal{n}{k}{TChan s} G G' (VChan b vcr) (VChan b vcr')

data RelateVEnv : ∀ {n k φ} → (G : SCtx n) (G' : SCtx (k + n)) (ϱ : VEnv' G φ) (ϱ' : VEnv' G' φ) → Set where
  [] : ∀ {n k G G'} → RelateVEnv{n}{k} G G' [] []
  _∷_ : ∀ {n k G G' t φ v v' ϱ ϱ'} → RelateVal{n}{k}{t} G G' v v' → RelateVEnv{n}{k}{φ} G G' ϱ ϱ' → RelateVEnv{n}{k} G G' (v ∷ ϱ) (v' ∷ ϱ')
  
  

data Command' {n : ℕ} (G : SCtx n) (t : Ty) : Set where
  Return : Val' G t → Command' G t
  Bind   : ∀ {t'}
         → Command' G t'
         → (Val' G t' → (k : ℕ) (G' : SCtx (k + n)) (ex : Extends G k G') → Command' G' t)
         → Command' G t

run' : ∀ {φ t n G}
  → Expr φ t 
  → VEnv'{n} G φ
  → Command' G t
run' (var x) ϱ = Return (access' ϱ x)
run' (nat i) ϱ = {!!}
run' {G = G} (lety sp e e₁) ϱ  with split-env' sp ϱ
... | ϱ₁ , ϱ₂ = Bind (run' e ϱ₁) λ v k G' ex → run' e₁ (liftVEnv ex (v  ∷ ϱ₂))
run' (pair sp x₁ x₂) ϱ = {!!}
run' (letpair sp x e) ϱ = {!!}
run' (fork e) ϱ = {!!}
run' (new s) ϱ = {!!}
-- run' (send sp ch vv) ϱ = {!!}
-- run' (recv ch) ϱ = {!!}
run' (close ch) ϱ = {!!}
run' (wait ch) ϱ = {!!}

-- a continuation closure
Cont : ∀ {n} → Ty → SCtx n → TCtx → Set

data Inactive : {n : ℕ} (G : SCtx n) → Set where
  []-inactive : Inactive []
  ::-inactive : ∀ {n} → (G : SCtx n) → Inactive G → Inactive (nothing ∷ G)

inactive-ssplit : ∀ {n G G₁ G₂} → SSplit{n} G G₁ G₂ → Inactive G₁ → G ≡ G₂
inactive-ssplit ss-[] []-inactive = refl
inactive-ssplit (ss-both ss) (::-inactive G inG₁) = cong (_∷_ nothing) (inactive-ssplit ss inG₁)
inactive-ssplit (ss-right ss) (::-inactive G inG₁) = cong (_∷_ (just _)) (inactive-ssplit ss inG₁)


data Command'' {n : ℕ} (G : SCtx n) : Set where
  Fork : ∀ {φ φ'} → Cont TUnit G φ → Cont TUnit G φ' → Command'' G
  Halt : Inactive G → Command'' G
  New : ∀ {φ} → (s : STy) → Cont (TPair (TChan s) (TChan (dual s))) G φ → Command'' G
  Close : ∀ {φ} → Val' G (TChan SEnd!) → Cont TUnit G φ → Command'' G
  Wait  : ∀ {φ} → Val' G (TChan SEnd?) → Cont TUnit G φ → Command'' G

Cont t G φ = VEnv' G φ × (Val' G t → VEnv' G φ → Command'' G)

halt-cont : ∀ {n G} → Inactive G → Cont{n} TUnit G []
halt-cont ina = [] , λ _ _ → Halt ina

apply-cont : ∀ {n G t φ} → Cont{n} t G φ → Val' G t → Command'' G
apply-cont (ϱ , c) = λ v → c v ϱ

run'' : ∀ {φ₁ φ₂ t n G}
  → Expr φ₁ t
  → VEnv'{n} G φ₁
  → Cont t G φ₂
  → Command'' G
run'' (var x) ϱ κ = let v = access' ϱ x in apply-cont κ v
run'' (nat i) ϱ κ = apply-cont κ (VInt i)
run'' (lety sp₁ e e₁) ϱ κ with split-env' sp₁ ϱ
... | ϱ₁ , ϱ₂ = run'' e ϱ₁ ( ϱ₂ , λ v ϱ₂' → run'' e₁ (v ∷ ϱ₂') κ)
run'' (pair sp₁ x₁ x₂) ϱ κ with split-env' sp₁ ϱ
... | ϱ₁ , ϱ₂ = apply-cont κ (VPair (access' ϱ₁ x₁) (access' ϱ₂ x₂))
run'' (letpair sp₁ x e) ϱ κ with split-env' sp₁ ϱ
... | ϱ₁ , ϱ₂ with access' ϱ₁ x
run'' (letpair sp₁ x e) ϱ κ | ϱ₁ , ϱ₂ | VPair vp vp₁ = run'' e (vp ∷ vp₁ ∷ ϱ₂) κ
run'' (fork e) ϱ κ = Fork (ϱ , λ _ ϱ → run'' e ϱ (halt-cont {!!})) κ
run'' (new s) ϱ κ = New s κ
run'' (close ch) ϱ κ = Close (access' ϱ ch) κ
run'' (wait ch) ϱ κ = Wait (access' ϱ ch) κ

data ThreadPool {n : ℕ} (G : SCtx n) : Set where
  nil : (ina : Inactive G) → ThreadPool G
  cons : ∀ {G₁ G₂} → (ss : SSplit G G₁ G₂) → (cmd : Command'' G₁) → (tp : ThreadPool G₂) → ThreadPool G

schedule : ∀ {n} → (G : SCtx n) → ThreadPool G → ⊤
schedule G (nil ina) = tt
schedule G (cons ss (Fork κ κ₁) tp) = {!!}
schedule G (cons ss (Halt ina) tp) with inactive-ssplit ss ina
schedule G (cons ss (Halt ina) tp) | refl = schedule G tp
schedule G (cons ss (New s x) tp) = {!!}
schedule G (cons ss (Close x x₁) tp) = {!!}
schedule G (cons ss (Wait x x₁) tp) = {!!}

start : Expr [] TUnit → ⊤
start e = schedule [] (cons ss-[] (run'' e [] ([] , λ _ _ → Halt []-inactive)) (nil []-inactive))
