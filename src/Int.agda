module Int where

open import Data.List

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

data Expr (A : Ctx) : Ty → Set where
  new : (s : STy) → Expr A (TPair (TChan s) (TChan (dual s)))
  send : ∀ { t s } → Expr A (TChan (SSend t s)) → Expr A t → Expr A (TChan s)
  recv : ∀ { t s } → Expr A (TChan (SRecv t s)) → Expr A (TPair (TChan s) t)
  close : Expr A (TChan SEnd) → Expr A TUnit
