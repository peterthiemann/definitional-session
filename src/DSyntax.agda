module DSyntax where

open import Data.List
open import Data.List.All
open import Data.Nat

open import Typing

data DExpr φ : Type → Set where
  var : ∀ {t}
      → (x : t ∈ φ)
      → DExpr φ t

  nat : (unr-φ : All Unr φ)
      → (i : ℕ)
      → DExpr φ TInt

  unit : (unr-φ : All Unr φ)
      → DExpr φ TUnit

  pair : ∀ {φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (e₁ : DExpr φ₁ t₁)
    → (e₂ : DExpr φ₂ t₂)
    → DExpr φ (TPair t₁ t₂)

  letpair : ∀ {φ₁ φ₂ t₁ t₂ t}
    → (sp : Split φ φ₁ φ₂)
    → (epair : DExpr φ₁ (TPair t₁ t₂))
    → (ebody : DExpr (t₁ ∷ t₂ ∷ φ₂) t)
    → DExpr φ t

  fork : (e : DExpr φ TUnit)
    → DExpr φ TUnit

  new : (unr-φ : All Unr φ)
      → (s : SType)
      → DExpr φ (TPair (TChan (SType.force s)) (TChan (SType.force (dual s))))

  send : ∀ {φ₁ φ₂ s t}
      → (sp : Split φ φ₁ φ₂)
      → (ech : DExpr φ₁ (TChan (send t s)))
      → (earg : DExpr φ₂ t)
      → DExpr φ (TChan (SType.force s))

  recv : ∀ {s t}
      → (ech : DExpr φ (TChan (recv t s)))
      → DExpr φ (TPair (TChan (SType.force s)) t)

  close : (ech : DExpr φ (TChan send!))
      → DExpr φ TUnit

  wait : (ech : DExpr φ (TChan send?))
      → DExpr φ TUnit

  select : ∀ {s₁ s₂}
      → (lab : Selector)
      → (ech : DExpr φ (TChan (sintern s₁ s₂)))
      → DExpr φ (TChan (selection lab (SType.force s₁) (SType.force s₂)))

  branch : ∀ {s₁ s₂ φ₁ φ₂ t}
      → (sp : Split φ φ₁ φ₂)
      → (ech : DExpr φ₁ (TChan (sextern s₁ s₂)))
      → (eleft : DExpr (TChan (SType.force s₁) ∷ φ₂) t)
      → (erght : DExpr (TChan (SType.force s₂) ∷ φ₂) t)
      → DExpr φ t

  ulambda : ∀ {t₁ t₂}
      → (unr-φ : All Unr φ)
      → (ebody : DExpr (t₁ ∷ φ) t₂)
      → DExpr φ (TFun UU t₁ t₂)

  llambda : ∀ {t₁ t₂}
      → (ebody : DExpr (t₁ ∷ φ) t₂)
      → DExpr φ (TFun LL t₁ t₂)

  app : ∀ {φ₁ φ₂ lu t₁ t₂}
      → (sp : Split φ φ₁ φ₂)
      → (efun : DExpr φ₁ (TFun lu t₁ t₂))
      → (earg : DExpr φ₂ t₁)
      → DExpr φ t₂

  subsume : ∀ {t₁ t₂}
      → (e : DExpr φ t₁)
      → (t≤t' : SubT t₁ t₂)
      → DExpr φ t₂
