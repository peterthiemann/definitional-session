module Typing where

open import Data.Bool
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- types and session types
data LU : Set where
  LL UU : LU

mutual
  data Ty : Set where
    TUnit TInt : Ty
    TPair : Ty → Ty → Ty
    TChan : STy → Ty
    TFun : LU → Ty → Ty → Ty

  data STy : Set where
    SSend SRecv : (t : Ty) → STy → STy
    SIntern SExtern : (s₁ : STy) → (s₂ : STy) → STy
    SEnd! SEnd? : STy

dual : STy → STy
dual (SSend x s) = SRecv x (dual s)
dual (SRecv x s) = SSend x (dual s)
dual (SIntern s₁ s₂) = SExtern (dual s₁) (dual s₂)
dual (SExtern s₁ s₂) = SIntern (dual s₁) (dual s₂)
dual SEnd! = SEnd?
dual SEnd? = SEnd!

dual-involution : (s : STy) → dual (dual s) ≡ s
dual-involution (SSend x s) rewrite dual-involution s = refl
dual-involution (SRecv x s) rewrite dual-involution s = refl
dual-involution (SIntern s₁ s₂) rewrite dual-involution s₁ | dual-involution s₂ = refl
dual-involution (SExtern s₁ s₂) rewrite dual-involution s₁ | dual-involution s₂ = refl
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
  LFun : ∀ {t₁ t₂} → Lin (TFun LL t₁ t₂)

data Unr : Ty → Set where
  UUnit : Unr TUnit
  UInt : Unr TInt
  UPair : ∀ {t₁ t₂} → Unr t₁ → Unr t₂ → Unr (TPair t₁ t₂)
  UFun :  ∀ {t₁ t₂} → Unr (TFun UU t₁ t₂)

-- lin and unr are mutually exclusive
lemma-lin-unr : ∀ {t} → Lin t → ¬ Unr t
lemma-lin-unr LChan ()
lemma-lin-unr (LPair1 lint) (UPair x x₁) = lemma-lin-unr lint x
lemma-lin-unr (LPair2 lint) (UPair x x₁) = lemma-lin-unr lint x₁
lemma-lin-unr LFun = λ ()

lemma-unr-lin : ∀  {t} → Unr t → ¬ Lin t
lemma-unr-lin UUnit ()
lemma-unr-lin UInt ()
lemma-unr-lin (UPair unr unr₁) (LPair1 lin) = lemma-unr-lin unr lin
lemma-unr-lin (UPair unr unr₁) (LPair2 lin) = lemma-unr-lin unr₁ lin
lemma-unr-lin UFun = λ ()

-- should be expressible by pattern matching lambda, but ...
destroy-left : ∀ {t₁ t₂} → ¬ Unr t₁ → ¬ Unr (TPair t₁ t₂)
destroy-left ¬p (UPair u₁ u₂) = ¬p u₁

destroy-right : ∀ {t₁ t₂} → ¬ Unr t₂ → ¬ Unr (TPair t₁ t₂)
destroy-right ¬p (UPair u₁ u₂) = ¬p u₂

unrestricted-type : (t : Ty) → Dec (Unr t)
unrestricted-type TUnit = yes UUnit
unrestricted-type TInt = yes UInt
unrestricted-type (TPair t₁ t₂) with unrestricted-type t₁ | unrestricted-type t₂
unrestricted-type (TPair t₁ t₂) | yes p | yes p₁ = yes (UPair p p₁)
unrestricted-type (TPair t₁ t₂) | yes p | no ¬p = no (destroy-right ¬p)
unrestricted-type (TPair t₁ t₂) | no ¬p | yes p = no (destroy-left ¬p)
unrestricted-type (TPair t₁ t₂) | no ¬p | no ¬p₁ = no (destroy-left ¬p)
unrestricted-type (TChan x) = no (λ ())
unrestricted-type (TFun LL t₁ t₂) = no (λ ())
unrestricted-type (TFun UU t₁ t₂) = yes UFun


destroy-both : ∀ {t₁ t₂} → ¬ Lin t₁ → ¬ Lin t₂ → ¬ Lin (TPair t₁ t₂)
destroy-both ¬l₁ ¬l₂ (LPair1 ltp) = ¬l₁ ltp
destroy-both ¬l₁ ¬l₂ (LPair2 ltp) = ¬l₂ ltp

linear-type : (t : Ty) → Dec (Lin t)
linear-type TUnit = no (λ ())
linear-type TInt = no (λ ())
linear-type (TPair t₁ t₂) with linear-type t₁ | linear-type t₂
linear-type (TPair t₁ t₂) | yes p | yes p₁ = yes (LPair1 p)
linear-type (TPair t₁ t₂) | yes p | no ¬p = yes (LPair1 p)
linear-type (TPair t₁ t₂) | no ¬p | yes p = yes (LPair2 p)
linear-type (TPair t₁ t₂) | no ¬p | no ¬p₁ = no (destroy-both ¬p ¬p₁)
linear-type (TChan x) = yes LChan
linear-type (TFun LL t₁ t₂) = yes LFun
linear-type (TFun UU t₁ t₂) = no (λ ())


classify-type : (t : Ty) → Lin t ⊎ Unr t
classify-type TUnit = inj₂ UUnit
classify-type TInt = inj₂ UInt
classify-type (TPair t₁ t₂) with classify-type t₁ | classify-type t₂
classify-type (TPair t₁ t₂) | inj₁ x | inj₁ x₁ = inj₁ (LPair1 x)
classify-type (TPair t₁ t₂) | inj₁ x | inj₂ y = inj₁ (LPair1 x)
classify-type (TPair t₁ t₂) | inj₂ y | inj₁ x = inj₁ (LPair2 x)
classify-type (TPair t₁ t₂) | inj₂ y | inj₂ y₁ = inj₂ (UPair y y₁)
classify-type (TChan x) = inj₁ LChan
classify-type (TFun LL t₁ t₂) = inj₁ LFun
classify-type (TFun UU t₁ t₂) = inj₂ UFun


-- typing context
TCtx : Set
TCtx = List Ty

-- context splitting, respecting linearity
data Split : TCtx → TCtx → TCtx → Set where
  [] : Split [] [] []
  unr : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  left : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) Φ₂
  rght : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ (t ∷ Φ₂)

-- split the unrestricted part from a typing context
split-refl-left : (φ : TCtx) → Σ TCtx λ φ' → All Unr φ' × Split φ φ φ'
split-refl-left [] = [] , [] , []
split-refl-left (t ∷ φ) with split-refl-left φ | classify-type t
split-refl-left (t ∷ φ) | φ' , unr-φ' , sp' | inj₁ x = φ' , unr-φ' , left sp'
split-refl-left (t ∷ φ) | φ' , unr-φ' , sp' | inj₂ y = t ∷ φ' , y ∷ unr-φ' , unr y sp'

-- reorganize splits
split-rotate : ∀ {φ φ₁ φ₂ φ₁₁ φ₁₂}
  → Split φ φ₁ φ₂ → Split φ₁ φ₁₁ φ₁₂ → Σ TCtx λ φ' → Split φ φ₁₁ φ' × Split φ' φ₁₂ φ₂
split-rotate [] [] = [] , [] , []
split-rotate (unr x sp12) (unr x₁ sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , unr x₁ sp-φ' , unr x₁ φ'-sp
split-rotate (unr x sp12) (left sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , unr x sp-φ' , rght φ'-sp
split-rotate (unr x sp12) (rght sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , rght sp-φ' , unr x φ'-sp
split-rotate (left sp12) (unr x₁ sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , unr x₁ sp-φ' , left φ'-sp
split-rotate (left sp12) (left sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = φ' , left sp-φ' , φ'-sp
split-rotate (left sp12) (rght sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , rght sp-φ' , left φ'-sp
split-rotate (rght sp12) sp1112 with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , rght sp-φ' , rght φ'-sp

-- extract from type context where all other entries are unrestricted
data _∈_ (x : Ty) : TCtx → Set where
  here  : ∀ { xs } → All Unr xs → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → Unr x₀ → x ∈ xs → x ∈ (x₀ ∷ xs)

