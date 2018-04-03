module Syntax where

open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Nat

open import Typing

-- expressions
data Expr : (φ : TCtx) → Ty → Set where
  var : ∀ {t φ}
      → (x : t ∈ φ)
      → Expr φ t

  nat : ∀ {φ}
      → (unr-φ : All Unr φ)
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
      → (unr-φ : All Unr φ)
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

lift-expr : ∀ {φ t tᵤ} → Unr tᵤ → Expr φ t → Expr (tᵤ ∷ φ) t
lift-expr unrtu (var x) = var (there unrtu x)
lift-expr unrtu (nat unr-φ i) = nat (unrtu ∷ unr-φ) i
lift-expr unrtu (letbind sp e e₁) = letbind (left sp) (lift-expr unrtu e) e₁
lift-expr unrtu (pair sp x₁ x₂) = pair (rght sp) x₁ (there unrtu x₂)
lift-expr unrtu (letpair sp p e) = letpair (left sp) (there unrtu p) e
lift-expr unrtu (fork e) = lift-expr unrtu e
lift-expr unrtu (new unr-φ s) = new (unrtu ∷ unr-φ) s
lift-expr unrtu (close ch) = close (there unrtu ch)
lift-expr unrtu (wait ch) = wait (there unrtu ch)
