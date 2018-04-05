module EssentialSession where

open import Data.Bool
open import Data.List hiding (map)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- types and session types
mutual
  data Ty : Set where
    TUnit : Ty
    TInt : Ty
    TPair : Ty → Ty → Ty
    TChan : STy → Ty

  data STy : Set where
    SSend : Ty → STy → STy
    SRecv : Ty → STy → STy
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

-- linear and unrestricted types (unused so far)
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

lemma-unr-lin : ∀ {t} → Unr t → ¬ Lin t
lemma-unr-lin UUnit ()
lemma-unr-lin UInt ()
lemma-unr-lin (UPair unr unr₁) (LPair1 lin) = lemma-unr-lin unr lin
lemma-unr-lin (UPair unr unr₁) (LPair2 lin) = lemma-unr-lin unr₁ lin

-- contexts for types and session types
TCtx = List Ty
SCtx = List STy

data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)

-- context splitting, respecting linearity
data Split : TCtx → TCtx → TCtx → Set where
  [] : Split [] [] []
  unr : ∀ {t A A₁ A₂} → Unr t → Split A A₁ A₂ → Split (t ∷ A) (t ∷ A₁) (t ∷ A₂)
  linleft : ∀ {t A A₁ A₂} → Lin t → Split A A₁ A₂ → Split (t ∷ A) (t ∷ A₁) A₂
  linrght : ∀ {t A A₁ A₂} → Lin t → Split A A₁ A₂ → Split (t ∷ A) A₁ (t ∷ A₂)

splitting-preserves : ∀ {t A A₁ A₂} → Split A A₁ A₂ → t ∈ A → t ∈ A₁ ⊎ t ∈ A₂
splitting-preserves (unr x split) here = inj₁ here
splitting-preserves (unr x split) (there t∈A) = map there there (splitting-preserves split t∈A)
splitting-preserves (linleft x split) here = inj₁ here
splitting-preserves (linleft x split) (there t∈A) = map there id (splitting-preserves split t∈A)
splitting-preserves (linrght x split) here = inj₂ here
splitting-preserves (linrght x split) (there t∈A) = map id there (splitting-preserves split t∈A)

splitting-reflects-left : ∀ {t A A₁ A₂} → Split A A₁ A₂ → t ∈ A₁ → t ∈ A
splitting-reflects-left (unr x split) here = here
splitting-reflects-left (linleft x split) here = here
splitting-reflects-left (linrght x split) here = there (splitting-reflects-left split here)
splitting-reflects-left (unr x split) (there t∈A₁) = there (splitting-reflects-left split t∈A₁)
splitting-reflects-left (linleft x split) (there t∈A₁) = there (splitting-reflects-left split t∈A₁)
splitting-reflects-left (linrght x split) (there t∈A₁) = there (splitting-reflects-left split (there t∈A₁))

-- syntax of typed expressions
data Expr (A : TCtx) : Ty → Set where
  var : ∀ { t } → t ∈ A → Expr A t
  nat : ℕ → Expr A TInt
  letx : ∀ { t₁ t₂ A₁ A₂ } → Split A A₁ A₂ → Expr A₁ t₁ → Expr (t₁ ∷ A₂) t₂ → Expr A t₂
  pair : ∀ { t₁ t₂ A₁ A₂} → Split A A₁ A₂ → Expr A₁ t₁ → Expr A₂ t₂ → Expr A (TPair t₁ t₂)
  letpair : ∀ { t t₁ t₂ A₁ A₂ } → Split A A₁ A₂ → Expr A₁ (TPair t₁ t₂) → Expr (t₁ ∷ t₂ ∷ A₂) t → Expr A t
  fork : Expr A TUnit → Expr A TUnit
  new : (s : STy) → Expr A (TPair (TChan s) (TChan (dual s)))
  send : ∀ { t s A₁ A₂ } → Split A A₁ A₂ → Expr A₁ (TChan (SSend t s)) → Expr A₂ t → Expr A (TChan s)
  recv : ∀ { t s } → Expr A (TChan (SRecv t s)) → Expr A (TPair (TChan s) t)
  close : Expr A (TChan SEnd!) → Expr A TUnit
  wait  : Expr A (TChan SEnd?) → Expr A TUnit


-- type indexed values
data Val (C : SCtx) : Ty → Set where
  VUnit : Val C TUnit
  VInt  : ℕ → Val C TInt
  VPair : ∀ { t₁ t₂ } → Val C t₁ → Val C t₂ → Val C (TPair t₁ t₂)
  VChan : ∀ { s } → (b : Bool) → (p : (xdual b s) ∈ C) → Val C (TChan s)

-- a channel is represented by a single entry in the session context
-- two channel endpoints belong to each channel, distinguished by a boolean flag
-- dependending on the flag value, the type of the endpoint corresponds either to session type in the context or to its dual
-- the run-time representation of a channel is unit

-- type indexed environments
data VEnv (C : SCtx) : TCtx → Set where
  []  : VEnv C []
  _∷_ : ∀ { t A } (x : Val C t) (xs : VEnv C A) → VEnv C (t ∷ A)

data Chan : STy → Set where
  CToken : (s : STy) → Chan s

-- typed channel environements
data CEnv : SCtx → Set where
  [] : CEnv []
  _∷_ : ∀ { s C } (x : Chan s) (xs : CEnv C) → CEnv (s ∷ C)

-- we need to speak about an "extension" of the current context C
--   designing a suitable relation to capture this notion is not straightforward
--   the following relation is an attempt to do so, but it is not sufficiently precise, I fear

data _≺S_ : STy → STy → Set where
  ≺-send : ∀ {t s} → SSend t s ≺S s
  ≺-recv : ∀ {t s} → SRecv t s ≺S s

data _≼S_ : STy → STy → Set where
  ≼S-refl : ∀ {s} → s ≼S s
  ≼S-step : ∀ {s₁ s₂ s₃} → s₁ ≺S s₂ → s₂ ≼S s₃ → s₁ ≼S s₃

data _≼C0_ : SCtx → SCtx → Set where
  [] : [] ≼C0 []
  _∷_ : ∀ {s₁ s₂ C₁ C₂} → s₁ ≼S s₂ → C₁ ≼C0 C₂ → (s₁ ∷ C₁) ≼C0 (s₂ ∷ C₂)

data _≼C_ : SCtx → SCtx → Set where
  evolve : ∀ {C₁ C₂} → C₁ ≼C0 C₂ → C₁ ≼C C₂
  extend : ∀ {C₁ C₂ s} → C₁ ≼C C₂ → C₁ ≼C (s ∷ C₂)

≼C0-refl :  ∀ (C : SCtx) → C ≼C0 C
≼C0-refl [] = []
≼C0-refl (x ∷ C) = ≼S-refl ∷ ≼C0-refl C

≼C-refl : ∀ (C : SCtx) → C ≼C C
≼C-refl C = evolve (≼C0-refl C)

≼S-trans : ∀ {s₁ s₂ s₃} → s₁ ≼S s₂ → s₂ ≼S s₃ → s₁ ≼S s₃
≼S-trans ≼S-refl ≼S-refl = ≼S-refl
≼S-trans ≼S-refl (≼S-step x p23) = ≼S-step x p23
≼S-trans (≼S-step x p12) ≼S-refl = ≼S-step x p12
≼S-trans (≼S-step x p12) (≼S-step x₁ p23) = ≼S-step x (≼S-trans p12 (≼S-step x₁ p23))

≼C0-trans : ∀ {C₁ C₂ C₃} → C₁ ≼C0 C₂ → C₂ ≼C0 C₃ → C₁ ≼C0 C₃
≼C0-trans [] [] = []
≼C0-trans (x ∷ p12) (x₁ ∷ p23) = ≼S-trans x x₁ ∷ ≼C0-trans p12 p23

≼C-trans : ∀ {C₁ C₂ C₃} → C₁ ≼C C₂ → C₂ ≼C C₃ → C₁ ≼C C₃
≼C-trans (evolve x₁) (evolve x) = evolve (≼C0-trans x₁ x)
≼C-trans (extend p12) (evolve (x ∷ x₁)) = extend (≼C-trans p12 (evolve x₁))
≼C-trans p12 (extend p23) = extend (≼C-trans p12 p23)

-- outcomes of a computation
-- for implementing a state transformers with resumptions and extra actions
-- * Pause is a paused computation with a continuation
-- * Fork requests creation of a new process by offering two continuations
-- * InputFrom waits for input from a designated channel (with continuation)
-- * OutputTo sends output to a designated channel (waits for rendezvous, with continuation)
data Result (C : SCtx) (A : Set) : Set where
  Return    : (x : A) 
            → Result C A
  Pause     : (cont   : (C' : SCtx) (pc' : C ≼C C') (σ' : CEnv C') → Result C' A)
            → Result C A
  Fork      : (forked : (C' : SCtx) (pc' : C ≼C C') (σ' : CEnv C') → Result C' ⊤)
            → (cont   : (C' : SCtx) (pc' : C ≼C C') (σ' : CEnv C') → Result C' A)
            → Result C A
  InputFrom : {t : Ty} {s : STy} 
            → (ch :  Val C (TChan (SRecv t s)))
            → (cont : (C' : SCtx)
                    → (pc' : C ≼C C')
                    → (ch' : Val C' (TChan s))
                    → Val C' t
                    → (σ' : CEnv C')
                    → Result C' A)
            → Result C A
  OutputTo  : {t : Ty} {s : STy}
            → (ch :  Val C (TChan (SSend t s)))
            → Val C t
            → (cont : (C' : SCtx)
                    → (pc' : C ≼C C')
                    → (ch' : Val C' (TChan s))
                    → (σ' : CEnv C') 
                    → Result C' A)
            → Result C A
  New       : {s : STy}
            → (cont : (C' : SCtx)
                    → (pc' : C ≼C C')
                    → (cp' : Val C' (TPair (TChan s) (TChan (dual s))))
                    → (σ'  : CEnv C')
                    → Result C' A)
            → Result C A

liftResult : ∀ {A C₁ C₂} → C₁ ≼C C₂ → Result C₁ A → Result C₂ A
liftResult c12 (Return x) = 
  Return x
liftResult c12 (Pause cont) =
  Pause λ C' pc' σ' → cont C' (≼C-trans c12 pc') σ'
liftResult {C₂ = C₂} c12 (Fork forked cont) =
  Fork (λ C' pc' σ' → forked C' (≼C-trans c12 pc') σ')
       λ C' pc' σ' → cont C' (≼C-trans c12 pc') σ'
liftResult c12 (InputFrom ch cont) = {!!}
liftResult c12 (OutputTo ch x cont) = {!!}
liftResult c12 (New cont) = {!!}

-- need to lift values that are indexed by a channel environment to an evolved channel environment
-- the point is that the type of the value that we want to subject to lifting should not evolve
-- but it is not clear how to express that restriction
liftChan0 : ∀ {C C' s} → C ≼C0 C' → s ∈ C → s ∈ C'
liftChan0 pc ps = {!!}

liftChan : ∀ {C C' s} → C ≼C C' → s ∈ C → s ∈ C'
liftChan (evolve x) ps = liftChan0 x ps
liftChan (extend pc) ps = there (liftChan pc ps)

liftVal : ∀ {C C' A} → C ≼C C' → Val C A → Val C' A
liftVal pc VUnit = VUnit
liftVal pc (VInt x) = VInt x
liftVal pc (VPair v v₁) = VPair (liftVal pc v) (liftVal pc v₁)
liftVal pc (VChan b p) = VChan b (liftChan pc p)

-- the Result data type can be made into a monad
--- * todo: probably requires a generalized monad
return : ∀ {C A} → A → Result C A
return a = Return a

_>>=_ : ∀ {A B C₁ C₂} → (c12 : C₁ ≼C C₂) → Result C₁ A → (A → Result C₂ B) → Result C₂ B
_>>=_ c12 (Return x)   f = f x
_>>=_ c12 (Pause cont) f =
  Pause (λ C' pc' σ' → _>>=_ (≼C-refl C') (cont C' (≼C-trans c12 pc') σ') (λ a → liftResult pc' (f a)))
_>>=_ c12 (Fork forked cont) f =
  Fork (λ C' pc' σ' → forked C' (≼C-trans c12 pc') σ')
       λ C' pc' σ' → _>>=_ (≼C-refl C') (cont C' (≼C-trans c12 pc') σ')  λ a → liftResult pc' (f a)
_>>=_ c12 (InputFrom ch cont) f =
  InputFrom
    (liftVal c12 ch) 
    λ C' pc' ch' v' σ' → _>>=_ (≼C-refl C') (cont C' (≼C-trans c12 pc') ch' v' σ') λ a → liftResult pc' (f a)
_>>=_ c12 (OutputTo ch x₁ cont) f =
  OutputTo
    (liftVal c12 ch)
    (liftVal c12 x₁)
    λ C' pc' ch' σ' → _>>=_ (≼C-refl C') (cont C' (≼C-trans c12 pc') ch' σ') λ a → liftResult pc' (f a)
_>>=_ c12 (New{s} cont) f =
  New
    λ C' pc' cp' σ' → ((≼C-refl C') >>= (cont C' (≼C-trans c12 pc') cp' σ')) λ a → liftResult pc' (f a)

liftEnv : ∀ {C C' A} → C ≼C C' → VEnv C A → VEnv C' A
liftEnv pc [] = []
liftEnv pc (x ∷ ϱ) = liftVal pc x ∷ liftEnv pc ϱ

-- split environment according to type context split
split-env : ∀ {C A A₁ A₂} → Split A A₁ A₂ → VEnv C A → VEnv C A₁ × VEnv C A₂
split-env [] [] = [] , []
split-env (unr x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env (linleft x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env (linrght x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- lookup an entry in a typed environemtn
lookup : ∀ {C A t} → VEnv C A → t ∈ A → Val C t
lookup (x ∷ ϱ) here = x
lookup (x ∷ ϱ) (there x₁) = lookup ϱ x₁

-- auxiliary lemma because "rewrite" does not work ad locum
simp-∈ : {s : STy} {C : SCtx} → s ∈ C → dual (dual s) ∈ C
simp-∈ {s} s∈C rewrite dual-involution s = s∈C

-- monadic interpreter for expressions
runMon : ∀ {t} → {A : TCtx} {C : SCtx} 
       → VEnv C A → CEnv C → Expr A t → Result C (Σ SCtx λ C' → (C ≼C C' × CEnv C' × Val C' t))
runMon ϱ σ (var x) = return (_ , ≼C-refl _ ,  σ , lookup ϱ x)
runMon ϱ σ (nat x) = return (_ , ≼C-refl _ , σ , VInt x)
runMon ϱ σ (letx split e₁ e₂) with split-env split ϱ
... | ϱ₁ , ϱ₂ with runMon ϱ₁ σ e₁
... | out = ((≼C-refl _) >>= out)  λ {(C₁ , cc₁ , σ₁ , v₁) → ({!!} >>= runMon{C = C₁} (v₁ ∷ liftEnv cc₁ ϱ₂) σ₁ e₂) {!!}}
runMon ϱ σ (pair split e e₁) = {!!}
runMon ϱ σ (letpair split e e₁) = {!!}
runMon ϱ σ (fork e) = 
  Fork (λ C' pc' σ' → _>>=_ (≼C-refl C') (runMon (liftEnv pc' ϱ) σ' e)  λ xyz → return tt) 
       (λ C' pc' σ' → Return (C' , pc' , σ' , VUnit))
runMon ϱ σ (new s) = New λ C' pc' cp' σ' → return (C' , pc' , σ' , cp')
runMon ϱ σ (send split e e₁) = {!!}
runMon ϱ σ (recv e) = {!!}
runMon ϱ σ (close e) = {!!}
runMon ϱ σ (wait e) = {!!}

-- another try
runMon1 : ∀ {t} → {A : TCtx} {C : SCtx} 
        → CEnv C
        → VEnv C A
        → Expr A t
        → Σ SCtx λ C' → C ≼C C' × CEnv C' × Result C' ( Val C' t)
runMon1 {C = C} σ ϱ (var x) = C , ≼C-refl C , σ , return (lookup ϱ x)
runMon1 {C = C} σ ϱ (nat x) = C ,  ≼C-refl C , σ , return (VInt x)
runMon1 σ ϱ (letx sp e e₁) = {!!}
runMon1 σ ϱ (pair sp e e₁) = {!!}
runMon1 σ ϱ (letpair sp e e₁) = {!!}
runMon1 {C = C} σ ϱ (fork e) = {!!}
runMon1 {C = C} σ ϱ (new s) rewrite dual-involution s =
  s ∷ C , extend (≼C-refl C) , (CToken s ∷ σ) ,  return (VPair (VChan true here) (VChan false (simp-∈ here)))
runMon1 σ ϱ (send sp e₁ e₂) with runMon1 σ ϱ {!e₁!}
runMon1 σ ϱ (send sp e₁ e₂) | C₁ , pc₁ , σ₁ , r₁ with runMon1 σ₁ (liftEnv pc₁ ϱ) {!e₂!}
runMon1 σ ϱ (send sp e₁ e₂) | C₁ , pc₁ , σ₁ , r₁ | C₂ , pc₂ , σ₂ , r₂ =
  C₂ , ≼C-trans pc₁ pc₂ , σ₂ , {!!}
runMon1 σ ϱ (recv e) = {!!}
runMon1 {C = C} σ ϱ (close e) =
  C , ≼C-refl C , σ , return VUnit
runMon1 {C = C} σ ϱ (wait e) =
  C , ≼C-refl C , σ , return VUnit


-- missing stuff
-- * monadic scheduler for processes
