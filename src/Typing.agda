module Typing where

open import Data.Bool
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.List.All
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- only used finitary for (Fin m → A)
postulate ext : ∀ {a b} → Extensionality a b

-- types and session types
mutual
  -- linearity tag: linear / unrestricted
  data LU : Set where
    LL UU : LU

  data Ty : Set where
    TUnit TInt : Ty
    TPair : Ty → Ty → Ty
    TChan : STy₁ 0 → Ty
    TFun  : LU → Ty → Ty → Ty

  data STy₀ (n : ℕ) : Set where
    S1 : (s1 : STy₁ n) → STy₀ n
    SMu : (s1 : STy₁ (suc n)) → STy₀ n
    SVar : (i : Fin n) → STy₀ n

  data STy₁ (n : ℕ) : Set where
    SSend SRecv : (t : Ty) → (s : STy₀ n) → STy₁ n
    SIntern SExtern : (s₁ : STy₀ n) → (s₂ : STy₀ n) → STy₁ n
    SIntN SExtN : (m : ℕ) (alt : Fin m → STy₀ n) → STy₁ n
    SEnd! SEnd? : STy₁ n

  STy = STy₀ 0

slift : ∀ {m} → STy₀ m → STy₀ (suc m)
slift₁ : ∀ {m} → STy₁ m → STy₁ (suc m)

slift (S1 s1) = S1 (slift₁ s1)
slift (SMu s1) = SMu (slift₁ s1)
slift (SVar i) = SVar (suc i)

slift₁ (SSend t s) = SSend t (slift s)
slift₁ (SRecv t s) = SRecv t (slift s)
slift₁ (SIntern s₁ s₂) = SIntern (slift s₁) (slift s₂)
slift₁ (SExtern s₁ s₂) = SExtern (slift s₁) (slift s₂)
slift₁ (SIntN m alt) = SIntN m λ x → slift (alt x)
slift₁ (SExtN m alt) = SExtN m λ x → slift (alt x)
slift₁ SEnd! = SEnd!
slift₁ SEnd? = SEnd?

ssubst : ∀ {m n} → STy₀ n → STy₀ (m + suc n) → STy₀ (m + n)
ssubst₁ : ∀ {m n} → STy₀ n → STy₁ (m + suc n) → STy₁ (m + n)

ssubst₁ {m} s (SSend t s₁) = SSend t (ssubst {m} s s₁)
ssubst₁ {m} s (SRecv t s₁) = SRecv t (ssubst {m} s s₁)
ssubst₁ {m} s (SIntern s₁ s₂) = SIntern (ssubst {m} s s₁) (ssubst {m} s s₂)
ssubst₁ {m} s (SExtern s₁ s₂) = SExtern (ssubst {m} s s₁) (ssubst {m} s s₂)
ssubst₁ {m} s (SIntN m' alt) = SIntN m' λ x → ssubst {m} s (alt x)
ssubst₁ {m} s (SExtN m' alt) = SExtN m' λ x → ssubst {m} s (alt x)
ssubst₁ s SEnd! = SEnd!
ssubst₁ s SEnd? = SEnd?

ssubst {m} s (S1 s1) = S1 (ssubst₁ {m} s s1)
ssubst {m} s (SMu s1) = SMu (ssubst₁ { suc m } s s1)
ssubst {zero} s (SVar zero) = s
ssubst {zero} s (SVar (suc i)) = SVar i
ssubst {suc m} s (SVar zero) = SVar zero
ssubst {suc m} s (SVar (suc i)) = slift (ssubst {m} s (SVar i))

unroll : STy₀ 0 → STy₁ 0
unroll (S1 s1) = s1
unroll s@(SMu s1) = ssubst₁ {0} s s1
unroll (SVar ())

dual : ∀ {n} → STy₀ n → STy₀ n
dual₁ : ∀ {n} → STy₁ n → STy₁ n

dual₁ (SSend x s) = SRecv x (dual s)
dual₁ (SRecv x s) = SSend x (dual s)
dual₁ (SIntern s₁ s₂) = SExtern (dual s₁) (dual s₂)
dual₁ (SExtern s₁ s₂) = SIntern (dual s₁) (dual s₂)
dual₁ (SIntN m alt) = SExtN m λ x → dual (alt x)
dual₁ (SExtN m alt) = SIntN m λ x → dual (alt x)
dual₁ SEnd! = SEnd?
dual₁ SEnd? = SEnd!

dual (S1 x) = S1 (dual₁ x)
dual (SMu x) = SMu (dual₁ x)
dual (SVar x) = SVar x

dual-involution₁ : ∀ {n} → (s : STy₁ n) → dual₁ (dual₁ s) ≡ s
dual-involution : ∀ {n} → (s : STy₀ n) → dual (dual s) ≡ s

dual-involution₁ (SSend x s) = cong (SSend x) (dual-involution s)
dual-involution₁ (SRecv x s) = cong (SRecv x) (dual-involution s)
dual-involution₁ (SIntern s₁ s₂) rewrite dual-involution s₁ | dual-involution s₂ = refl
dual-involution₁ (SExtern s₁ s₂) rewrite dual-involution s₁ | dual-involution s₂ = refl
dual-involution₁ (SIntN m alt) = cong (SIntN m) (ext λ x → dual-involution (alt x))
dual-involution₁ (SExtN m alt) = cong (SExtN m) (ext λ x → dual-involution (alt x))
dual-involution₁ SEnd! = refl
dual-involution₁ SEnd? = refl

dual-involution (S1 s) = cong S1 (dual-involution₁ s)
dual-involution (SMu s) = cong SMu (dual-involution₁ s)
dual-involution (SVar i) = refl

xdual : ∀ {n} → Bool → STy₀ n → STy₀ n
xdual false s = dual s
xdual true s = s

slift-dual : ∀ {n} (s : STy₀ n) → dual (slift s) ≡ slift (dual s)
slift-dual₁ : ∀ {n} (s : STy₁ n) → dual₁ (slift₁ s) ≡ slift₁ (dual₁ s)

slift-dual (S1 s1) = cong S1 (slift-dual₁ s1)
slift-dual (SMu s1) = cong SMu (slift-dual₁ s1)
slift-dual (SVar i) = refl

slift-dual₁ (SSend t s) = cong (SRecv t) (slift-dual s)
slift-dual₁ (SRecv t s) = cong (SSend t) (slift-dual s)
slift-dual₁ (SIntern s₁ s₂) = cong₂ SExtern (slift-dual s₁) (slift-dual s₂)
slift-dual₁ (SExtern s₁ s₂) = cong₂ SIntern (slift-dual s₁) (slift-dual s₂)
slift-dual₁ (SIntN m alt) = cong (SExtN m) (ext λ x → slift-dual (alt x))
slift-dual₁ (SExtN m alt) = cong (SIntN m) (ext λ x → slift-dual (alt x))
slift-dual₁ SEnd! = refl
slift-dual₁ SEnd? = refl

ssubst-dual₁ : ∀ {n} → (s1 : STy₁ 1) (s2 : STy₁ (n + 1))
  → dual₁ (ssubst₁ {n} (SMu s1) s2) ≡ ssubst₁ {n} (SMu (dual₁ s1)) (dual₁ s2)
ssubst-dual : ∀ {n} → (s1 : STy₁ 1) (s2 : STy₀ (n + 1))
  → dual (ssubst {n} (SMu s1) s2) ≡ ssubst {n} (SMu (dual₁ s1)) (dual s2)

ssubst-dual₁ {n} s1 (SSend t s) = cong (SRecv t) (ssubst-dual {n} s1 s)
ssubst-dual₁ {n} s1 (SRecv t s) = cong (SSend t) (ssubst-dual {n} s1 s)
ssubst-dual₁ {n} s1 (SIntern s₁ s₂) = cong₂ SExtern (ssubst-dual {n} s1 s₁) (ssubst-dual {n} s1 s₂)
ssubst-dual₁ {n} s1 (SExtern s₁ s₂) = cong₂ SIntern (ssubst-dual {n} s1 s₁) (ssubst-dual {n} s1 s₂)
ssubst-dual₁ {n} s1 (SIntN m alt) = cong (SExtN m) (ext λ x → ssubst-dual {n} s1 (alt x))
ssubst-dual₁ {n} s1 (SExtN m alt) = cong (SIntN m) (ext λ x → ssubst-dual {n} s1 (alt x))
ssubst-dual₁ s1 SEnd! = refl
ssubst-dual₁ s1 SEnd? = refl

ssubst-dual {n} s1 (S1 s2) = cong S1 (ssubst-dual₁ {n} s1 s2)
ssubst-dual {n} s1 (SMu s2) = cong SMu (ssubst-dual₁ s1 s2)
ssubst-dual {zero} s1 (SVar zero) = refl
ssubst-dual {zero} s1 (SVar (suc i)) = refl
ssubst-dual {suc n} s1 (SVar zero) = refl
ssubst-dual {suc n} s1 (SVar (suc i)) rewrite slift-dual (ssubst {n} (SMu s1) (SVar i)) = cong slift (ssubst-dual {n} s1 (SVar i))

unroll-dual : (s : STy₀ 0) → dual₁ (unroll s) ≡ unroll (dual s)
unroll-dual (S1 s1) = refl
unroll-dual (SMu s1) = ssubst-dual₁ s1 s1
unroll-dual (SVar ())

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

-- split is symmetric
split-sym : ∀ {φ φ₁ φ₂} → Split φ φ₁ φ₂ → Split φ φ₂ φ₁
split-sym [] = []
split-sym (unr x sp) = unr x (split-sym sp)
split-sym (left sp) = rght (split-sym sp)
split-sym (rght sp) = left (split-sym sp)

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

split-all-left : (φ : TCtx) → Split φ φ []
split-all-left [] = []
split-all-left (x ∷ φ) = left (split-all-left φ)

split-all-right : (φ : TCtx) → Split φ [] φ
split-all-right [] = []
split-all-right (x ∷ φ) = rght (split-all-right φ)

split-all-unr : ∀ {φ} → All Unr φ → Split φ φ φ
split-all-unr [] = []
split-all-unr (px ∷ un-φ) = unr px (split-all-unr un-φ)

split-from-disjoint : (φ₁ φ₂ : TCtx) → Σ TCtx λ φ → Split φ φ₁ φ₂
split-from-disjoint [] φ₂ = φ₂ , split-all-right φ₂
split-from-disjoint (t ∷ φ₁) φ₂ with split-from-disjoint φ₁ φ₂
... | φ' , sp = t ∷ φ' , left sp

split-unr : ∀ {φ φ₁ φ₂} → (sp : Split φ φ₁ φ₂) → All Unr φ₁ → All Unr φ₂ → All Unr φ
split-unr [] [] [] = []
split-unr (unr x sp) (px ∷ unr1) (px₁ ∷ unr2) = px ∷ split-unr sp unr1 unr2
split-unr (left sp) (px ∷ unr1) unr2 = px ∷ split-unr sp unr1 unr2
split-unr (rght sp) unr1 (px ∷ unr2) = px ∷ split-unr sp unr1 unr2

-- extract from type context where all other entries are unrestricted
data _∈_ (x : Ty) : TCtx → Set where
  here  : ∀ { xs } → All Unr xs → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → Unr x₀ → x ∈ xs → x ∈ (x₀ ∷ xs)

-- left and right branching
data Selector : Set where
  Left Right : Selector

selection : ∀ {A : Set} → Selector → A → A → A
selection Left x y = x
selection Right x y = y

