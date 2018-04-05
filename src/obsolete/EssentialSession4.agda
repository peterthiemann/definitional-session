module EssentialSession4 where

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

data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)


data PosNeg : Set where
  POS NEG POSNEG : PosNeg

-- types and session types
mutual
  -- keep track which ends of a channel a process is allowed to possess
  -- m >= n, but they are equal on the top level
  SCtx : ℕ → ℕ → Set
  SCtx m n = Vec (Maybe (STy m × PosNeg)) n

  data Ty (n : ℕ) : Set where
    TUnit TInt : Ty n
    TPair : Ty n → Ty n → Ty n
    TChan : Fin n → Bool → Ty n

  data STy (n : ℕ) : Set where
    SSend SRecv : Ty n → STy n → STy n
    SEnd! SEnd? : STy n

dual : ∀ {n} → STy n → STy n
dual (SSend x s) = SRecv x (dual s)
dual (SRecv x s) = SSend x (dual s)
dual SEnd! = SEnd?
dual SEnd? = SEnd!


liftSTy : {n : ℕ} → STy n → STy (suc n)
liftTy  : {n : ℕ} → Ty n → Ty (suc n)

liftSTy (SSend x s) = SSend (liftTy x) (liftSTy s)
liftSTy (SRecv x s) = SRecv (liftTy x) (liftSTy s)
liftSTy SEnd! = SEnd!
liftSTy SEnd? = SEnd?

liftTy TUnit = TUnit
liftTy TInt = TInt
liftTy (TPair t₁ t₂) = TPair (liftTy t₁) (liftTy t₂)
liftTy (TChan m b) = TChan (inject₁ m) b

liftMSPN1 : ∀ {n} → Maybe (STy n × PosNeg) → Maybe (STy (suc n) × PosNeg)
liftMSPN1 (just (s , pn)) = just (liftSTy s , pn)
liftMSPN1 nothing = nothing

liftSCtx : {m n : ℕ} → SCtx m n → SCtx (suc m) n
liftSCtx [] = []
liftSCtx (x ∷ G) = liftMSPN1 x ∷ liftSCtx G

liftNTy : {n : ℕ} → (k : ℕ) → Ty n → Ty (k + n)
liftNTy k TUnit = TUnit
liftNTy k TInt = TInt
liftNTy k (TPair t t₁) = TPair (liftNTy k t) (liftNTy k t₁)
liftNTy k (TChan m b) = let m' = injectk+ k m in TChan m' b

liftNSTy : {n : ℕ} → (k : ℕ) → STy n → STy (k + n)
liftNSTy zero s = s
liftNSTy (suc m) s = liftSTy (liftNSTy m s)

liftNSCtx : {m n : ℕ} → (k : ℕ) → SCtx m n → SCtx (k + m) n
liftNSCtx zero G = G
liftNSCtx (suc k) G = liftSCtx (liftNSCtx k G)

-- SSplit G G₁ G₂
-- split G into G₁ and G₂
-- length and position preserving
data SSplit : {m n : ℕ} → SCtx m n → SCtx m n → SCtx m n → Set where
  ss-[]    : ∀ {m} → SSplit {m} [] [] []
  ss-both  : ∀ { m n G G₁ G₂ }
           → SSplit {m}{n} G G₁ G₂
           → SSplit (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂)
  ss-left  : ∀ { m n spn G G₁ G₂ }
           → SSplit {m} {n} G G₁ G₂
           → SSplit (just spn ∷ G) (just spn ∷ G₁) (nothing ∷ G₂)
  ss-right : ∀ { m n spn G G₁ G₂ }
           → SSplit {m} {n} G G₁ G₂
           → SSplit (just spn ∷ G) (nothing ∷ G₁) (just spn ∷ G₂)
  ss-posneg : ∀ { m n s G G₁ G₂ }
          → SSplit {m} {n} G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , POS) ∷ G₁) (just (s , NEG) ∷ G₂)
  ss-negpos : ∀ { m n s G G₁ G₂ }
          → SSplit {m} {n} G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , NEG) ∷ G₁) (just (s , POS) ∷ G₂)

data ValidChannelRef {m : ℕ} : {n : ℕ} (G : SCtx m n) (k : Fin n) (b : Bool) → Set where
  here-pos : ∀ {n s} {G : SCtx m n}
    → ValidChannelRef (just (s , POS) ∷ G) zero true
  here-neg : ∀ {n s} {G : SCtx m n}
    → ValidChannelRef (just (s , NEG) ∷ G) zero false
  here-posneg : ∀ {n s b} {G : SCtx m n}
    → ValidChannelRef (just (s , POSNEG) ∷ G) zero b
  there : ∀ {n x k b} {G : SCtx m n}
    → ValidChannelRef G k b
    → ValidChannelRef (x ∷ G) (suc k) b

liftVCR : ∀ {n k b}
  → (x : Maybe (STy (suc n) × PosNeg))
  → (G : Vec (Maybe (STy n × PosNeg)) k)
  → (m' : Fin k)
  → ValidChannelRef G m' b
  → ValidChannelRef (x ∷ liftSCtx G) (suc m') b

liftVCR x .(just (_ , POS) ∷ _) .zero here-pos = there here-pos
liftVCR x .(just (_ , NEG) ∷ _) .zero here-neg = there here-neg
liftVCR x .(just (_ , POSNEG) ∷ _) .zero here-posneg = there here-posneg
liftVCR {n} x (x' ∷ G') (suc m') (there vcr) = there (liftVCR (liftMSPN1 x') G' m' vcr)
    
data Val {n : ℕ} (G : SCtx n n) : Ty n → Set where
  VInt  : (n : ℕ) → Val G TInt
  VPair : ∀ {t₁ t₂} → Val G t₁ → Val G t₂ → Val G (TPair t₁ t₂)
  VChan : (m : Fin n) (b : Bool) → ValidChannelRef G (invert m) b → Val G (TChan m b)

liftVal1 : ∀ {n : ℕ} {G : SCtx n n} {t : Ty n} {x : Maybe (STy (suc n) × PosNeg)} → Val G t → Val (x ∷ liftSCtx G) (liftTy t)
liftVal1 (VInt n) = VInt n
liftVal1 (VPair v v₁) = VPair (liftVal1 v) (liftVal1 v₁)
liftVal1 (VChan m b x₁) = VChan (inject₁ m) b {!!}

liftValK : ∀ {n : ℕ} {G : SCtx n n} {t : Ty n} (k : ℕ) {H : Vec (Maybe (STy (k + n) × PosNeg)) k} → Val G t → Val (H Data.Vec.++ liftNSCtx k G) (liftNTy k t)
liftValK k (VInt n) = VInt n
liftValK {G = G} k {H} (VPair v v₁) = VPair (liftValK {G = G} k {H} v) (liftValK {G = G} k {H} v₁)
liftValK k (VChan m b x) = let m' = injectk+ k m in VChan m' b {!!}

-- typing context
TCtx : ℕ → Set
TCtx n = List (Ty n)

-- lifting for typing contexts
liftTCtx : {n : ℕ} → TCtx n → TCtx (suc n)
liftTCtx φ = Data.List.map liftTy φ

liftNTCtx : {n : ℕ} → (k : ℕ) → TCtx n → TCtx (k + n)
liftNTCtx k φ = Data.List.map (liftNTy k) φ

-- linear and unrestricted types
data Lin {n : ℕ} : Ty n → Set where
  LChan : ∀ {m b} → Lin (TChan m  b)
  LPair1 : ∀ {t₁ t₂} → Lin t₁ → Lin (TPair t₁ t₂)
  LPair2 : ∀ {t₁ t₂} → Lin t₂ → Lin (TPair t₁ t₂)

data Unr {n : ℕ} : Ty n → Set where
  UUnit : Unr TUnit
  UInt : Unr TInt
  UPair : ∀ {t₁ t₂} → Unr t₁ → Unr t₂ → Unr (TPair t₁ t₂)

-- lin and unr are mutually exclusive
lemma-lin-unr : ∀ {n} {t : Ty n} → Lin t → ¬ Unr t
lemma-lin-unr LChan ()
lemma-lin-unr (LPair1 lint) (UPair x x₁) = lemma-lin-unr lint x
lemma-lin-unr (LPair2 lint) (UPair x x₁) = lemma-lin-unr lint x₁

lemma-unr-lin : ∀ {n} {t : Ty n} → Unr t → ¬ Lin t
lemma-unr-lin UUnit ()
lemma-unr-lin UInt ()
lemma-unr-lin (UPair unr unr₁) (LPair1 lin) = lemma-unr-lin unr lin
lemma-unr-lin (UPair unr unr₁) (LPair2 lin) = lemma-unr-lin unr₁ lin

-- context splitting, respecting linearity
data Split {n : ℕ} : TCtx n → TCtx n → TCtx n → Set where
  [] : Split [] [] []
  unr : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  linleft : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) Φ₂
  linrght : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ (t ∷ Φ₂)

-- value environments
data VEnv {n : ℕ} (G : SCtx n n) : TCtx n → Set where
  [] : VEnv G []
  _∷_ : ∀{t φ} → (x : Val G t) → (ϱ : VEnv G φ) → VEnv G (t ∷ φ)

-- split environment according to type context split
split-env : ∀ {n Φ Φ₁ Φ₂} {G : SCtx n n} → Split Φ Φ₁ Φ₂ → VEnv G Φ → VEnv G Φ₁ × VEnv G Φ₂
split-env [] [] = [] , []
split-env (unr x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env (linleft x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env (linrght x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- replacing a send binding in an environment
data DeltaTransmit {m : ℕ} : (n : ℕ) (k : Fin n) (b : Bool) (G G' : SCtx m n) (t : Ty m) → Set where
  here-pos : ∀ {n t s G}
    → DeltaTransmit (suc n) zero true 
                 (just (SSend t s , POS) ∷ G) (just (s , POS) ∷ G) t
  here-neg : ∀ {n t s G}
    → DeltaTransmit (suc n) zero false
                 (just (SRecv t s , NEG) ∷ G) (just (s , NEG) ∷ G) t
  there : ∀ {n k b G G' t x x'}
    → DeltaTransmit n k b G G' t
    → DeltaTransmit (suc n) (suc k) b (x ∷ G) (x' ∷ G') t

data DeltaClose {m : ℕ} : (n : ℕ) (k : Fin n) (b : Bool) (G G' : SCtx m n) → Set where
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
data Expr : (n n' : ℕ) (G : SCtx n n) (G' : SCtx n' n') (φ : TCtx n) → Ty n' → Set where
  var : ∀ {n G t φ}
      → (x : t ∈ φ)
      → Expr n n G G φ t

  nat : ∀ {n G φ}
      → (i : ℕ)
      → Expr n n G G φ TInt
{- too complicated
  letx : ∀ {n₁ n₂ n₃ G₁ G₂ G₃ φ φ₁ φ₂ t₁ t₂}
    → (n₁≤n₂ : n₁ ≤ n₂)
    → (n₂≤n₃ : n₂ ≤ n₃)
    → Split φ φ₁ φ₂
    → Expr n₁ n₂ G₁ G₂ φ₁ t₁
    → let φ₂' = liftNTCtx (n₂ ∸ n₁) φ₂
          φ₂'' = coerce (convert2{F = TCtx} n₁≤n₂) φ₂'
      in Expr n₂ n₃ G₂ G₃ φ₂'' t₂
    → Expr n₁ n₃ G₁ G₃ φ t₂
-}
  lety : ∀ {n k₁ k₂ G₁ G₂ G₃ φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (e₁ : Expr n (k₁ + n) G₁ G₂ φ₁ t₁)
    → (e₂ : let φ₂' = t₁ ∷ liftNTCtx k₁ φ₂
      in Expr (k₁ + n) (k₂ + (k₁ + n)) G₂ G₃ φ₂' t₂)
    → Expr n (k₂ + (k₁ + n)) G₁ G₃ φ t₂

  pair : ∀ {n φ φ₁ φ₂ t₁ t₂ G}
    → (sp : Split φ φ₁ φ₂)
    → (x₁ : t₁ ∈ φ₁)
    → (x₂ : t₂ ∈ φ₂)
    → Expr n n G G φ (TPair t₁ t₂)

  letpair : ∀ {n k φ φ₁ φ₂ t₁ t₂ G₁ G₂ t}
    → (sp : Split φ φ₁ φ₂)
    → (x : TPair t₁ t₂ ∈ φ₁)
    → (e : Expr n (k + n) G₁ G₂ (t₁ ∷ t₂ ∷ φ₂) t)
    → Expr n (k + n) G₁ G₂ φ t

  fork : ∀ {n k φ G G₁ G₂ G₃}
    → (ss : SSplit G G₁ G₂)
    -- affine -- → (all-nothing : T (all is-nothing (toList G₃)))
    → (e : Expr n (k + n) G₂ G₃ φ TUnit)
    → Expr n n G G₁ φ TUnit

  new : ∀ {n G φ}
      → (s : STy n)
      → Expr n (suc n)
             G (just (liftSTy s , POSNEG) ∷ liftSCtx G)
             φ
             (TPair (TChan (fromℕ n) true) (TChan (fromℕ n) false))
  -- takes only variables to avoid extraneous effects
  send : ∀ {n G₁ G₂ φ φ₁ φ₂ k b t}
      → (sp : Split φ φ₁ φ₂)
      → (ch : (TChan k b) ∈ φ₁)
      → (dt : DeltaTransmit n (invert k) b G₁ G₂ t)
      → (vv : t ∈ φ₂)
      → Expr n n G₁ G₂ φ (TChan k b)
  -- takes only variables to avoid extraneous effects
  recv : ∀ {n G₁ G₂ φ k b t}
      → (ch : (TChan k b) ∈ φ)
      → (dt : DeltaTransmit n (invert k) (not b) G₁ G₂ t)
      → Expr n n G₁ G₂ φ (TPair (TChan k b) t)

  close : ∀ {n k b φ G₁ G₂}
      → (ch : (TChan k b) ∈ φ)
      → (dc : DeltaClose n (invert k) b G₁ G₂)
      → Expr n n G₁ G₂ φ TUnit

  wait : ∀ {n k b φ G₁ G₂}
      → (ch : (TChan k b) ∈ φ)
      → (dc : DeltaClose n (invert k) b G₁ G₂)
      → Expr n n G₁ G₂ φ TUnit


frag1 = 
  wait (there here) here-wait-neg

prog1 =
  lety {0} {1} {1} {G₁ = []} [] (new SEnd!) $
  letpair (linleft (LPair1 LChan) []) here $
  lety {1} {0}  (linleft LChan (linrght LChan []))
    (fork (ss-negpos ss-[]) (close here here-close-pos))
    (wait (there here) here-wait-neg)
{-
    
-}

-- data CEnv {n : ℕ} (G : SCtx n n) : Set where
--   [] : CEnv G
--   _∷_ : ∀ {G} → (spn : STy × PosNeg) → (ψ : CEnv G) → CEnv (spn ∷ G)

access : ∀ {n φ t} {G : SCtx n n} → VEnv G φ → t ∈ φ → Val G t
access (x ∷ ϱ) here = x
access (x ∷ ϱ) (there x₁) = access ϱ x₁

-- (exp) lifted access
kaccess : ∀ {k n φ t} {G : SCtx n n} {G' : SCtx (k + n) (k + n)} → VEnv G φ → t ∈ φ → Val G' (liftNTy k t)
kaccess (x ∷ ϱ) here = {!lift!}
kaccess ϱ (there x) = {!!}

data Command (A : Set) : Set where
  Return : (x : A) → Command A

_>>=_ : ∀ {A B : Set} → Command A → (A → Command B) → Command B
Return x >>= fab = fab x

run : ∀ {n₁ n₂ G₁ G₂ φ t }
  → Expr n₁ n₂ G₁ G₂ φ t 
  → VEnv G₁ φ → Command (Val G₂ t)
run (var x) ϱ = Return $ access ϱ x
run (nat i) ϱ = Return $ VInt i
run (lety sp e e₁) ϱ with split-env sp ϱ
run (lety sp e₁ e₂) ϱ | ϱ₁ , ϱ₂ = run e₁ ϱ₁ >>= λ v₁ → run e₂ {!!}
run (pair sp x₁ x₂) ϱ with split-env sp ϱ
... | ϱ₁ , ϱ₂ = Return (VPair (access ϱ₁ x₁) (access ϱ₂ x₂))
run (letpair sp x e) ϱ with split-env sp ϱ
run (letpair sp x e) ϱ | ϱ₁ , ϱ₂ with access ϱ₁ x
run (letpair sp x e) ϱ | ϱ₁ , ϱ₂ | VPair v v₁ = run e (v ∷ v₁ ∷ ϱ₂)
run (fork ss e) ϱ = {!!}
run (new s) ϱ = {!!}
run (send sp ch dt vv) ϱ = {!!}
run (recv ch dt) ϱ = {!!}
run (close ch dc) ϱ = {!!}
run (wait ch dc) ϱ = {!!}

-- data Eff : SCtx → SCtx → Set where
--   ENone : Eff [] []
--   ESeq  : ∀ {G G₁ G₁' G₂ G₂'}
--         → SSplit G G₁ G₂ 
--         → Eff G₁ G₁'
--         → Eff G₂ G₂'
--         → Eff G G₂
--   ENew  : (s : STy) → Eff [] [ s , POSNEG ]
--   EFork : ∀ {G} → Eff G [] → Eff G []
--   ESend : ∀ {t G G'} → TSend t G G' → Eff G G'
--   ERecv : ∀ {t G G'} → TRecv t G G' → Eff G G'


-- data Expr : (G : SCtx) (G' : SCtx) → CEnv G → Ty → Eff G G' → Set where
--   fork : ∀ {G ψ ε}
--        → Expr G [] ψ TUnit ε
--        → Expr G [] ψ TUnit (EFork ε)
--   new  : ∀ {ψ}
--        → (s : STy)
--        → Expr [] [ s , POSNEG ] ψ (TPair (TChan s) (TChan (dual s))) (ENew s)
--   send : ∀ {G₁ G₁' ψ₁ ε₁ G₂ G₂' ψ₂ ε₂ G G' ψ t s} { ts ss₂}
--        → (ss : SSplit G G₁ G₂)
--        → Expr G₁ G₁' ψ₁ (TChan (SSend t s)) ε₁
--        → Expr G₂ G₂' ψ₂ t ε₂
--        → Expr G G' ψ (TChan s)  (ESeq ss₂ (ESeq ss ε₁ ε₂)  (ESend ts))


-- -- computation for type: Expr G Φ τ ε
-- -- Command ((ψ : CEnv G) → (ϱ : VEnv ψ Φ) → Σ CEnv λ ψ' → (Rel ε ψ ψ' × Val ψ τ))

