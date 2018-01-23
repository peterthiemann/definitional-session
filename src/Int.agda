module Int where

open import Category.Monad
open import Data.Product
open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

mutual
  data Ty : Set where
    TUnit : Ty
    TInt : Ty
    TPair : Ty → Ty → Ty
    TFun  : Ty → Ty → Ty
    TChan : STy → Ty

  data STy : Set where
    SSend : Ty → STy → STy
    SRecv : Ty → STy → STy
    SInternal : STy → STy → STy
    SExternal : STy → STy → STy
    SEnd! SEnd? : STy

dual : STy → STy
dual (SSend x s) = SRecv x (dual s)
dual (SRecv x s) = SSend x (dual s)
dual (SInternal s s₁) = SExternal (dual s) (dual s₁)
dual (SExternal s s₁) = SInternal (dual s) (dual s₁)
dual SEnd! = SEnd?
dual SEnd? = SEnd!

dual-involution : (s : STy) → dual (dual s) ≡ s
dual-involution (SSend x s) rewrite dual-involution s = refl
dual-involution (SRecv x s) rewrite dual-involution s = refl
dual-involution (SInternal s₁ s₂) rewrite dual-involution s₁ | dual-involution s₂ = refl
dual-involution (SExternal s₁ s₂) rewrite dual-involution s₁ | dual-involution s₂ = refl
dual-involution SEnd! = refl
dual-involution SEnd? = refl

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
  close : Expr A (TChan SEnd!) → Expr A TUnit
  wait  : Expr A (TChan SEnd?) → Expr A TUnit
  

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

-- threaded lookup
data Lookup (t : Ty) : (A : Ctx) → (B : Ctx) → Set where
  herelin : ∀ {A} → Lin t → Lookup t (t ∷ A) (TUnit ∷ A)
  hereunr : ∀ {A} → Unr t → Lookup t (t ∷ A) (t ∷ A)
  there   : ∀ {A B x} → Lookup t A B → Lookup t (x ∷ A) (x ∷ B)

-- syntax of type threaded expressions
data Expr' : Ctx → Ctx → Ty → Set where
  var : ∀ { t A B } → Lookup t A B → Expr' A B t
  pair : ∀ { t₁ t₂ A B C } → Expr' A B t₁ → Expr' B C t₂ → Expr' A C (TPair t₁ t₂)
  fst : ∀ { t₁ t₂ A B } → Expr' A B (TPair t₁ t₂) → Expr' A B t₁
  snd : ∀ { t₁ t₂ A B } → Expr' A B (TPair t₁ t₂) → Expr' A B t₂
  new : ∀ { A } → (s : STy) → Expr' A A (TPair (TChan s) (TChan (dual s)))
  send : ∀ { t s A B C } → Expr' A B (TChan (SSend t s)) → Expr' B C t → Expr' A C (TChan s)
  recv : ∀ { t s A B } → Expr' A B (TChan (SRecv t s)) → Expr' A B (TPair (TChan s) t)
  close : ∀ { A B } → Expr' A B (TChan SEnd!) → Expr' A B TUnit
  wait  : ∀ { A B } → Expr' A B (TChan SEnd?) → Expr' A B TUnit

xdual : Bool → STy → STy
xdual false s = dual s
xdual true s = s


-- type indexed values
data Val : Ty → Set where
  VUnit : Val TUnit
  VInt : ℕ → Val TInt
  VPair : ∀ { t₁ t₂ } → Val t₁ → Val t₂ → Val (TPair t₁ t₂)
  VChan : ∀ { s C } → (b : Bool) → (xdual b s) ∈ C → Val (TChan s)

-- typed environments
data Env : Ctx → Set where
  []  : Env []
  _∷_ : ∀ { t A } (x : Val t) (xs : Env A) → Env (t ∷ A)

data Chan : STy → Set where
  CToken : (s : STy) → Chan s

-- typed channel environements
data CEnv : List STy → Set where
  [] : CEnv []
  _∷_ : ∀ { s C } (x : Chan s) (xs : CEnv C) → CEnv (s ∷ C)

lookup : ∀ {A t} → t ∈ A → Env A → Val t
lookup here (t ∷ ϱ) = t
lookup (there x) (x₁ ∷ ϱ) = lookup x ϱ

simp-∈ : {s : STy} {C : List STy} → s ∈ C → dual (dual s) ∈ C
simp-∈ {s} s∈C rewrite dual-involution s = s∈C

-- interpreter for expressions
runExpr : ∀ {t} → {A : Ctx} {C : List STy} 
  → Env A → CEnv C → Expr A t → Σ (List STy) λ C' → (CEnv C' × Val t)
runExpr ϱ σ (var x) = _ , σ , lookup x ϱ
runExpr ϱ σ (pair e₁ e₂) with runExpr ϱ σ e₁
runExpr ϱ σ (pair e₁ e₂) | C₁ , σ₁ , v₁ with runExpr ϱ σ₁ e₂
runExpr ϱ σ (pair e₁ e₂) | C₁ , σ₁ , v₁ | C₂ , σ₂ , v₂ = C₂ , σ₂ , VPair v₁ v₂
runExpr ϱ σ (fst e) with runExpr ϱ σ e
runExpr ϱ σ (fst e) | C₁ , σ₁ , VPair v₁ v₂ = C₁ , σ₁ , v₁
runExpr ϱ σ (snd e) with runExpr ϱ σ e
runExpr ϱ σ (snd e) | C₁ , σ₁ , VPair v₁ v₂ = C₁ , σ₁ , v₂
runExpr {t}{A}{C} ϱ σ (new s) =
   s ∷ C ,  CToken s ∷ σ , VPair (VChan {s} {s ∷ C} true here) (VChan {dual s} {s ∷ C} false (simp-∈ here))
runExpr ϱ σ (send e e₁) = {!!}
runExpr ϱ σ (recv e) = {!!}
runExpr ϱ σ (close e) = {!!}
runExpr ϱ σ (wait e) = {!!}

-- outcomes of a computation
data Result (A : Set) : Set where
  Return : (x : A) → Result A
  Next : Result A → Result A
  InputFrom : (t : Ty) → ℕ → (Val t → Result A) → Result A
  OutputTo  : (t : Ty) → ℕ → Val t → Result A → Result A

return : ∀ {A} → A → Result A
return = Return

_>>=_ : ∀ {A B} → Result A → (A → Result B) → Result B
_>>=_ (Return x) frb = frb x
_>>=_ (Next r) frb = Next (_>>=_ r frb)
_>>=_ (InputFrom t x x₁) frb = InputFrom t x (λ z → _>>=_ (x₁ z) frb)
_>>=_ (OutputTo t n v r) frb = OutputTo t n v (_>>=_ r frb)

-- make into a monad
monadR : ∀ {f} → RawMonad Result
monadR = record { return = Return
                ; _>>=_  = _>>=_
                }

-- monadic interpreter for expressions
runMon : ∀ {t} → {A : Ctx} {C : List STy} 
  → Env A → CEnv C → Expr A t → Result (Σ (List STy) λ C' → (CEnv C' × Val t))
runMon ϱ σ (var x) = return (_ , σ , lookup x ϱ)
runMon ϱ σ (pair e₁ e₂) = runMon ϱ σ e₁ >>= (λ v₁ → 
                          runMon ϱ (proj₁ (proj₂ v₁)) e₂ >>= λ v₂ → 
                          return (proj₁ v₂ , proj₁ (proj₂ v₂) , VPair (proj₂ (proj₂ v₁)) (proj₂ (proj₂ v₂))))
runMon ϱ σ (fst e) = {!!}
runMon ϱ σ (snd e) = {!!}
runMon ϱ σ (new s) = {!!}
runMon ϱ σ (send e e₁) = {!!}
runMon ϱ σ (recv e) = {!!}
runMon ϱ σ (close e) = {!!}
runMon ϱ σ (wait e) = {!!}
