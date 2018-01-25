module Int where

open import Category.Monad.Indexed
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
SCtx = List STy

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
  VChan : ∀ { s } → (C : SCtx) → (b : Bool) → (p : (xdual b s) ∈ C) → Val (TChan s)

getChanInfo : ∀ {s} → Val (TChan s) → Σ SCtx (λ C → Σ Bool (λ b → (xdual b s) ∈ C))
getChanInfo (VChan C b p) = C , b , p


-- typed environments
data Env : Ctx → Set where
  []  : Env []
  _∷_ : ∀ { t A } (x : Val t) (xs : Env A) → Env (t ∷ A)

data Chan : STy → Set where
  CToken : (s : STy) → Chan s

-- typed channel environements
data CEnv : SCtx → Set where
  [] : CEnv []
  _∷_ : ∀ { s C } (x : Chan s) (xs : CEnv C) → CEnv (s ∷ C)

lookup : ∀ {A t} → t ∈ A → Env A → Val t
lookup here (t ∷ ϱ) = t
lookup (there x) (x₁ ∷ ϱ) = lookup x ϱ

simp-∈ : {s : STy} {C : SCtx} → s ∈ C → dual (dual s) ∈ C
simp-∈ {s} s∈C rewrite dual-involution s = s∈C

-- interpreter for expressions
runExpr : ∀ {t} → {A : Ctx} {C : SCtx} 
  → Env A → CEnv C → Expr A t → Σ SCtx λ C' → (CEnv C' × Val t)
runExpr ϱ σ (var x) = _ , σ , lookup x ϱ
runExpr ϱ σ (pair e₁ e₂) with runExpr ϱ σ e₁
runExpr ϱ σ (pair e₁ e₂) | C₁ , σ₁ , v₁ with runExpr ϱ σ₁ e₂
runExpr ϱ σ (pair e₁ e₂) | C₁ , σ₁ , v₁ | C₂ , σ₂ , v₂ = C₂ , σ₂ , VPair v₁ v₂
runExpr ϱ σ (fst e) with runExpr ϱ σ e
runExpr ϱ σ (fst e) | C₁ , σ₁ , VPair v₁ v₂ = C₁ , σ₁ , v₁
runExpr ϱ σ (snd e) with runExpr ϱ σ e
runExpr ϱ σ (snd e) | C₁ , σ₁ , VPair v₁ v₂ = C₁ , σ₁ , v₂
runExpr {t}{A}{C} ϱ σ (new s) =
   s ∷ C ,  CToken s ∷ σ , VPair (VChan (s ∷ C) true here) (VChan {dual s} (s ∷ C) false (simp-∈ here))
runExpr ϱ σ (send e e₁) = {!!}
runExpr ϱ σ (recv e) = {!!}
runExpr ϱ σ (close e) = {!!}
runExpr ϱ σ (wait e) = {!!}

-- outcomes of a computation
data Result (A : Set) : Set where
  Return : (x : A) → Result A
  Pause     : (cont : (C : SCtx) (σ : CEnv C) → Result A)
            → Result A
  InputFrom : {t : Ty} {s : STy} 
            → (C : SCtx)
            → (b : Bool)
            → (p : (xdual b (SRecv t s)) ∈ C)
            → (σ : CEnv C)
            → (cont : (c : Val (TChan (xdual b s)))
                    → Val t
                    → (σ' : CEnv (proj₁ (getChanInfo c)))
                    → Result A)
            → Result A
  OutputTo  : {t : Ty} {s : STy}
            → (C : SCtx)
            → (b : Bool)
            → (xdual b (SSend t s)) ∈ C → Val t
            → (σ : CEnv C)
            → (cont : (c : Val (TChan (xdual b s)))
                    → proj₁ (proj₂ (getChanInfo c)) ≡ b
                    → (σ' : CEnv (proj₁ (getChanInfo c))) 
                    → Result A)
            → Result A

return : ∀ {A} → A → Result A
return = Return

_>>=_ : ∀ {A B} → Result A → (A → Result B) → Result B
Return x               >>= frb = frb x
Pause cont             >>= frb = Pause λ C σ → cont C σ >>= frb 
InputFrom C b p σ cont >>= frb = InputFrom C b p σ (λ c z σ' → cont c z σ' >>= frb)
OutputTo C t n v σ r   >>= frb = OutputTo C t n v σ (λ z p a → r z p a >>= frb)


-- monadic interpreter for expressions
runMon : ∀ {t} → {A : Ctx} {C : SCtx} 
  → Env A → CEnv C → Expr A t → Result (Σ SCtx λ C' → (CEnv C' × Val t))
runMon ϱ σ (var x) = return (_ , σ , lookup x ϱ)
runMon {TPair t₁ t₂} ϱ σ (pair e₁ e₂) = 
  runMon ϱ σ e₁ >>= λ csv₁ →
  runMon ϱ (proj₁ (proj₂ csv₁)) e₂ >>= λ csv₂ →
  return (proj₁ csv₂ , proj₁ (proj₂ csv₂) , VPair (proj₂ (proj₂ csv₁)) (proj₂ (proj₂ csv₂)))
runMon ϱ σ (fst e) =
  runMon ϱ σ e >>= f
  where
    f : ∀ {t₁} {t₂} → Σ SCtx (λ C' → CEnv C' × Val (TPair t₁ t₂)) → Result (Σ SCtx (λ C' → CEnv C' × Val t₁))
    f (C' , σ' , VPair v₁ v₂) = return (C' , σ' , v₁)
runMon ϱ σ (snd e) =
  runMon ϱ σ e >>= f
  where
    f : ∀ {t₁} {t₂} → Σ SCtx (λ C' → CEnv C' × Val (TPair t₁ t₂)) → Result (Σ SCtx (λ C' → CEnv C' × Val t₂))
    f (C' , σ' , VPair v₁ v₂) = return (C' , σ' , v₂)
runMon {t}{A}{C} ϱ σ (new s) =
  return ( s ∷ C
         , CToken s ∷ σ
         , VPair (VChan (s ∷ C) true here) (VChan (s ∷ C) false (simp-∈ here)))
runMon ϱ σ₀ (send ec ev) =
  runMon ϱ σ₀ ec >>= λ {(C₁ , σ₁ , (VChan Cc bc pc)) →
  runMon ϱ σ₁ ev >>= λ {(C₂ , σ₂ , vv) →
  -- need to lift Cc to C₁ and then to C₂
  OutputTo C₂ bc {!pc!} vv σ₂
  λ c₁ p σ' → let vchan' = getChanInfo c₁ in return (proj₁ vchan' , σ' , {!c₁!})
  }}
runMon {TPair (TChan s) t} ϱ σ (recv e) =
  runMon ϱ σ e >>= λ {( C₁ , σ₁ , VChan {SRecv .t .s} Cc bc pc) →
  InputFrom Cc bc pc {!!} λ vc vt σ' → return {!!}  }
runMon ϱ σ (close e) =
  runMon ϱ σ e >>= {!!}
runMon ϱ σ (wait e) =
  runMon ϱ σ e >>= {!!}

{-
  OutputTo  : (t : Ty) → ℕ → Val t → Result A → Result A
-}

-- the real thing is an indexed monad
-- 
data Channels {a} (A : Set a) : Set a where
  Ch : (C : SCtx) → (σ : CEnv C) → (Σ SCtx λ C' → (CEnv C' × A)) → Channels A

data IChannels {a} : SCtx → SCtx → Set a → Set a where
  Ch : (C C' : SCtx) → (A : Set a) → ((σ : CEnv C) → (CEnv C' × A)) → IChannels C C' A
  Ou : (C C' : SCtx) → (A : Set a) → ℕ → (⊤ → IChannels C C' A) → IChannels C C' A

ireturn : ∀ {a} {A : Set a} {C} → A → IChannels C C A
ireturn {a} {A} {C} x = Ch C C A (λ σ → σ , x)

ibindaux : ∀ {a} → (C C' C'' : SCtx) (B : Set a) → IChannels C' C'' B → CEnv C' → CEnv C'' × B
ibindaux C C' C'' B (Ch .C' .C'' .B x) = x
ibindaux C C' C'' B (Ou .C' .C'' .B x x₁) = {!!}

ibind : ∀ {a} {A B : Set a} {C C' C''} → IChannels C C' A → (A → IChannels C' C'' B) → IChannels C C'' B
ibind {B = B} {C'' = C''} (Ch C C' A st) f =
  Ch C C'' B λ σ → 
  let r = st σ
      q = f (proj₂ r)
      final = ibindaux C C' C'' B q (proj₁ r)
  in final
ibind {B = B} {C'' = C''} (Ou C C' A n cont) f =
  Ou C C'' B n (λ _ → ibind (cont tt) f)

-- output : ℕ → (⊤ → Mon C C' A) → Mon C C' A
-- input  : (ℕ → Mon C C' A) → Mon C C' A
-- return : A → Mon C C A
-- bind   : Mon C C' A → (A → Mon C' C'' B) → Mon C C'' B

-- output n cont `bind` f = output n (cont [] f) -- Kleisli composition
-- input  g      `bind` f = input    (g [] f)
-- return x      `bind` f = f x


--- maybe need this
--- S → Mon O S A
--- Mon I O S A = Return S A | Output O S (⊤ → S → Mon I O S A) | Input S (I → S → Mon I O S A)
--- Return S A `bind` f = f A S
--- Output O S g `bind` f = Output O S (λ x → g x `comp` f)
--- Input S g `bind` f = Input S (λ x → g x `comp` f)

