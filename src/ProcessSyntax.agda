module ProcessSyntax where

open import Data.List

open import Typing
open import Syntax

-- processes
data Proc : (Φ : TCtx) → Set where
  exp : ∀ {Φ}
    → Expr Φ TUnit
    → Proc Φ

  par : ∀ {Φ Φ₁ Φ₂}
    → (sp : Split Φ Φ₁ Φ₂)
    → (P₁ : Proc Φ₁)
    → (P₂ : Proc Φ₂)
    → Proc Φ

  res : ∀ {Φ}
    → (s : SType)
    → Proc (TChan (SType.force s) ∷ TChan (SType.force (dual s)) ∷ Φ)
    → Proc Φ

