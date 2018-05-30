module DSyntax where

open import Data.List
open import Data.List.All
open import Data.Nat

open import Typing

data DExpr :  (φ : TCtx) → Type → Set where
  var : ∀ {t φ}
      → (x : t ∈ φ)
      → DExpr φ t

  nat : ∀ {φ}
      → (unr-φ : All Unr φ)
      → (i : ℕ)
      → DExpr φ TInt

  unit : ∀ {φ}
      → (unr-φ : All Unr φ)
      → DExpr φ TUnit

  pair : ∀ {φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (e₁ : DExpr φ₁ t₁)
    → (e₂ : DExpr φ₂ t₂)
    → DExpr φ (TPair t₁ t₂)

  letpair : ∀ {φ φ₁ φ₂ t₁ t₂ t}
    → (sp : Split φ φ₁ φ₂)
    → (epair : DExpr φ₁ (TPair t₁ t₂))
    → (ebody : DExpr (t₁ ∷ t₂ ∷ φ₂) t)
    → DExpr φ t

  fork : ∀ {φ}
    → (e : DExpr φ TUnit)
    → DExpr φ TUnit

  new : ∀ {φ}
      → (unr-φ : All Unr φ)
      → (s : Session)
      → DExpr φ (TPair (TChan (Session.force s)) (TChan (Session.force (dual s))))

  send : ∀ {φ φ₁ φ₂ s t}
      → (sp : Split φ φ₁ φ₂)
      → (ech : DExpr φ₁ (TChan (send t s)))
      → (earg : DExpr φ₂ t)
      → DExpr φ (TChan (Session.force s))

  recv : ∀ {φ s t}
      → (ech : DExpr φ (TChan (recv t s)))
      → DExpr φ (TPair (TChan (Session.force s)) t)

  close : ∀ {φ}
      → (ech : DExpr φ (TChan send!))
      → DExpr φ TUnit

  wait : ∀ {φ}
      → (ech : DExpr φ (TChan send?))
      → DExpr φ TUnit

  select : ∀ {s₁ s₂ φ}
      → (lab : Selector)
      → (ech : DExpr φ (TChan (sintern s₁ s₂)))
      → DExpr φ (TChan (selection lab (Session.force s₁) (Session.force s₂)))

  -- potential problem: if both branches return a channel, this typing does not require that it's the *same* channel
  -- later on in the semantic model, there may be a mismatch in the resources returned by the branches
  branch : ∀ {s₁ s₂ φ φ₁ φ₂ t}
      → (sp : Split φ φ₁ φ₂)
      → (ech : DExpr φ₁ (TChan (sextern s₁ s₂)))
      → (eleft : DExpr (TChan (Session.force s₁) ∷ φ₂) t)
      → (erght : DExpr (TChan (Session.force s₂) ∷ φ₂) t)
      → DExpr φ t

  ulambda : ∀ {φ t₁ t₂}
      → (unr-φ : All Unr φ)
      → (ebody : DExpr (t₁ ∷ φ) t₂)
      → DExpr φ (TFun UU t₁ t₂)

  llambda : ∀ {φ t₁ t₂}
      → (ebody : DExpr (t₁ ∷ φ) t₂)
      → DExpr φ (TFun LL t₁ t₂)

  app : ∀ {φ φ₁ φ₂ lu t₁ t₂}
      → (sp : Split φ φ₁ φ₂)
      → (efun : DExpr φ₁ (TFun lu t₁ t₂))
      → (earg : DExpr φ₂ t₁)
      → DExpr φ t₂

