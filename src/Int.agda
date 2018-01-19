module Int where

open import Data.List
open import Data.Nat

mutual
  data Ty : Set where
    TUnit : Ty
    TInt : Ty
    TPair : Ty → Ty → Ty
    TChan : STy → Ty

  data STy : Set where
    SSend : Ty → STy → STy
    SRecv : Ty → STy → STy
    SInternal : STy → STy → STy
    SExternal : STy → STy → STy
    SEnd : STy

dual : STy → STy
dual (SSend x s) = SRecv x (dual s)
dual (SRecv x s) = SSend x (dual s)
dual (SInternal s s₁) = SExternal (dual s) (dual s₁)
dual (SExternal s s₁) = SInternal (dual s) (dual s₁)
dual SEnd = SEnd

Ctx = List Ty

data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)

-- syntax of typed expressions
data Expr (A : Ctx) : Ty → Set where
  var : ∀ { t } → t ∈ A → Expr A t
  pair : ∀ { t₁ t₂ } → Expr A t₁ → Expr A t₂ → Expr A (TPair t₁ t₂)
  fst :  ∀ { t₁ t₂ } → Expr A (TPair t₁ t₂) → Expr A t₁
  snd :  ∀ { t₁ t₂ } → Expr A (TPair t₁ t₂) → Expr A t₂
  new : (s : STy) → Expr A (TPair (TChan s) (TChan (dual s)))
  send : ∀ { t s } → Expr A (TChan (SSend t s)) → Expr A t → Expr A (TChan s)
  recv : ∀ { t s } → Expr A (TChan (SRecv t s)) → Expr A (TPair (TChan s) t)
  close : Expr A (TChan SEnd) → Expr A TUnit

-- threaded lookup
data Lin : Ty → Set where
  LChan : ∀ {s} → Lin (TChan s)
  LPair1 : ∀ {t₁ t₂} → Lin t₁ → Lin (TPair t₁ t₂)
  LPair2 : ∀ {t₁ t₂} → Lin t₂ → Lin (TPair t₁ t₂)

data Unr : Ty → Set where
  UUnit : Unr TUnit
  UInt : Unr TInt
  UPair : ∀ {t₁ t₂} → Unr t₁ → Unr t₂ → Unr (TPair t₁ t₂)

data Lookup (t : Ty) : (A : Ctx) → (B : Ctx) → Set where
  herelin : ∀ {A} → Lin t → Lookup t (t ∷ A) (TUnit ∷ A)
  hereunr : ∀ {A} → Unr t → Lookup t (t ∷ A) (t ∷ A)
  there   : ∀ {A B x} → Lookup t A B → Lookup t (x ∷ A) (x ∷ B)

-- syntax of type threaded expressions
data Expr' (A : Ctx) (B : Ctx) : Ty → Set where

-- type indexed values
data Val : Ty → Set where
  VUnit : Val TUnit
  VInt : ℕ → Val TInt
  VPair : ∀ { t₁ t₂ } → Val t₁ → Val t₂ → Val (TPair t₁ t₂)
  VChan : ∀ { s } → ℕ → Val (TChan s)

-- typed environments
data Env : Ctx → Set where
  [] : Env []
  _∷_ : ∀ { t A } (x : Val t) (xs : Env A) → Env (t ∷ A)

-- interpreter for expressions
runExpr : ∀ {t} → (A : Ctx) → Env A → Expr A t → Val t
runExpr A ϱ e = {!!}

-- outcomes of a computation
data Result (A : Set) : Set where
  Return : (x : A) → Result A
  Next : Result A
  InputFrom : (t : Ty) → ℕ → (Val t → Result A) → Result A
  OutputTo  : (t : Ty) → ℕ → Val t → Result A
