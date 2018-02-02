module EssentialSession1 where

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
  letx : ∀ { t₁ t₂ A₁ A₂ } → (sp : Split A A₁ A₂) → (e₁ : Expr A₁ t₁) → (e₂ : Expr (t₁ ∷ A₂) t₂) → Expr A t₂
  pair : ∀ { t₁ t₂ A₁ A₂ } → (sp : Split A A₁ A₂) → (e₁ : Expr A₁ t₁) → (e₂ : Expr A₂ t₂) → Expr A (TPair t₁ t₂)
  letpair : ∀ { t t₁ t₂ A₁ A₂ } → (sp : Split A A₁ A₂) → (e₁ : Expr A₁ (TPair t₁ t₂)) → (e₂ : Expr (t₁ ∷ t₂ ∷ A₂) t) → Expr A t
  fork : Expr A TUnit → Expr A TUnit
  new : (s : STy) → Expr A (TPair (TChan s) (TChan (dual s)))
  send : ∀ { t s A₁ A₂ } → (sp : Split A A₁ A₂) → (e₂ : Expr A₁ (TChan (SSend t s))) → (e₂ : Expr A₂ t) → Expr A (TChan s)
  recv : ∀ { t s } → Expr A (TChan (SRecv t s)) → Expr A (TPair (TChan s) t)
  close : Expr A (TChan SEnd!) → Expr A TUnit
  wait  : Expr A (TChan SEnd?) → Expr A TUnit


-- type indexed values
data Val : Ty → Set where
  VUnit : Val TUnit
  VInt  : ℕ → Val TInt
  VPair : ∀ { t₁ t₂ } → Val t₁ → Val t₂ → Val (TPair t₁ t₂)
  VChan : ∀ { s } → Val (TChan s)

-- a channel is represented by a single entry in the session context
-- two channel endpoints belong to each channel, distinguished by a boolean flag
-- dependending on the flag value, the type of the endpoint corresponds either to session type in the context or to its dual
-- the run-time representation of a channel is unit

-- type indexed environments
data VEnv : TCtx → Set where
  []  : VEnv []
  _∷_ : ∀ { t A } (x : Val t) (xs : VEnv A) → VEnv (t ∷ A)

-- outcomes of a computation
-- for implementing a state transformers with resumptions and extra actions
-- * Pause is a paused computation with a continuation
-- * Fork requests creation of a new process by offering two continuations
-- * RecvFrom waits for input from a designated channel (with continuation)
-- * SendTo sends output to a designated channel (waits for rendezvous, with continuation)
data Result (A : Set) : Set where
  Return    : (x : A) 
            → Result A
  Pause     : (cont   : ⊤ → Result A)
            → Result A
  Fork      : (forked : ⊤ → Result (Val TUnit))
            → (cont   : ⊤ → Result A)
            → Result A
  RecvFrom : {t : Ty} {s : STy} 
            → (ch :  Val (TChan (SRecv t s)))
            → (cont : (ch' : Val (TChan s))
                    → Val t
                    → Result A)
            → Result A
  SendTo  : {t : Ty} {s : STy}
            → (ch :  Val (TChan (SSend t s)))
            → Val t
            → (cont : Val (TChan s) → Result A)
            → Result A
  New       : (s : STy)
            → (cont : (cp : Val (TPair (TChan s) (TChan (dual s)))) → Result A)
            → Result A
  Close     : (ch : Val (TChan SEnd!))
            → (cont : Val TUnit → Result A)
            → Result A
  Wait      : (ch : Val (TChan SEnd?))
            → (cont : Val TUnit → Result A)
            → Result A


-- the Result data type can be made into a monad
return : ∀ {A} → A → Result A
return a = Return a

_>>=_ : ∀ {A B} → Result A → (A → Result B) → Result B
Return x >>= f = f x
Pause cont >>= f = Pause λ x → cont x >>= f
Fork forked cont >>= f = Fork forked (λ _ → cont tt >>= f)
RecvFrom ch cont >>= f = RecvFrom ch (λ ch' z → cont ch' z >>= f)
SendTo ch x cont >>= f = SendTo ch x (λ ch' → cont ch' >>= f)
New s cont >>= f = New s λ v → cont v >>= f
Close ch cont >>= f = Close ch (λ z → cont z >>= f)
Wait ch cont >>= f = Wait ch (λ z → cont z >>= f)


-- split environment according to type context split
split-env : ∀ {A A₁ A₂} → Split A A₁ A₂ → VEnv A → VEnv A₁ × VEnv A₂
split-env [] [] = [] , []
split-env (unr x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env (linleft x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env (linrght x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- lookup an entry in a typed environemtn
lookup : ∀ {A t} → VEnv A → t ∈ A → Val t
lookup (x ∷ ϱ) here = x
lookup (x ∷ ϱ) (there x₁) = lookup ϱ x₁

-- -- monadic interpreter for expressions
-- * TODO: make mutually recursive with a function that counts down fuel and changes Return to Pause when fuel runs out
runExpr : ∀ {t A} → VEnv A → Expr A t → Result (Val t)
runExpr ϱ (var x) = return (lookup ϱ x)
runExpr ϱ (nat x) = return (VInt x)
runExpr ϱ (letx sp e₁ e₂) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr ϱ₁ e₁ >>= λ v₁ → runExpr (v₁ ∷ ϱ₂) e₂
runExpr ϱ (pair sp e₁ e₂) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr ϱ₁ e₁ >>= λ v₁ → runExpr ϱ₂ e₂ >>= λ v₂ → return (VPair v₁ v₂)
runExpr ϱ (letpair sp e₁ e₂) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr ϱ₁ e₁ >>= λ{(VPair v₁ v₂) → runExpr (v₁ ∷ v₂ ∷ ϱ₂) e₂}
runExpr ϱ (fork e) = Fork (λ _ → runExpr ϱ e) (λ _ → Return VUnit)
runExpr ϱ (new s) = New s Return
runExpr ϱ (send sp e₁ e₂) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr ϱ₁ e₁ >>= λ v₁ → runExpr ϱ₂ e₂ >>= λ v₂ → SendTo v₁ v₂ Return
runExpr ϱ (recv e) = runExpr ϱ e >>= λ v → RecvFrom v (λ ch' z → Return (VPair ch' z))
runExpr ϱ (close e) = runExpr ϱ e >>= λ v → Close v Return
runExpr ϱ (wait e) = runExpr ϱ e >>= λ v → Wait v Return

-- processes
data Proc (A : TCtx) : Set where
  Pi : (s : STy) → (P : Proc (TChan s ∷ TChan (dual s) ∷ A)) → Proc A
  Par : ∀ {A₁ A₂} → (sp : Split A A₁ A₂) → (P : Proc A₁) → (Q : Proc A₂) → Proc A
  Exp : Expr A TUnit → Proc A

-- -- missing stuff
-- -- * monadic scheduler for processes
