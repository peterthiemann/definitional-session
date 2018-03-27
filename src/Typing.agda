module Typing where

open import Data.Bool
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- general
data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)

-- specific
data PosNeg : Set where
  POS NEG POSNEG : PosNeg

-- types and session types
mutual
  -- keep track which ends of a channel a process is allowed to possess
  -- m >= n, but they are equal on the top level
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

lemma-unr-lin : ∀  {t} → Unr t → ¬ Lin t
lemma-unr-lin UUnit ()
lemma-unr-lin UInt ()
lemma-unr-lin (UPair unr unr₁) (LPair1 lin) = lemma-unr-lin unr lin
lemma-unr-lin (UPair unr unr₁) (LPair2 lin) = lemma-unr-lin unr₁ lin

-- typing context
TCtx : Set
TCtx = List Ty

-- context splitting, respecting linearity
data Split : TCtx → TCtx → TCtx → Set where
  [] : Split [] [] []
  unr : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  linleft : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) Φ₂
  linrght : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ (t ∷ Φ₂)

