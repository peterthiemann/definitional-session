module Int where

open import Category.Monad.Indexed
open import Data.Product hiding (map)
open import Data.List hiding (map)
open import Data.Nat
open import Data.Bool
open import Data.Sum
open import Data.Unit
open import Function
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

-- contexts for types and session types
TCtx = List Ty
SCtx = List STy

data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)

-- effects (?)
data Eff (C : SCtx) : Set where
  Send : ∀ {t s} → SSend t s ∈ C → Eff C
  Recv : ∀ {t s} → SRecv t s ∈ C → Eff C

-- a list of effect only makes sense if the effects can be put in sequence
data Effect : SCtx → SCtx → Set where
  send-here : ∀ { t s C } → Effect (SSend t s ∷ C) (s ∷ C)
  recv-here : ∀ { t s C } → Effect (SRecv t s ∷ C) (s ∷ C)
  not-here  : ∀ { s C₁ C₂ } → Effect C₁ C₂ → Effect (s ∷ C₁) (s ∷ C₂)

-- syntax of typed expressions
data Expr (A : TCtx) : Ty → Set where
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

data Split : TCtx → TCtx → TCtx → Set where
  [] : Split [] [] []
  unr : ∀ {t A A₁ A₂} → Unr t → Split A A₁ A₂ → Split (t ∷ A) (t ∷ A₁) (t ∷ A₂)
  linleft : ∀ {t A A₁ A₂} → Lin t → Split A A₁ A₂ → Split (t ∷ A) (t ∷ A₁) A₂
  linrght : ∀ {t A A₁ A₂} → Lin t → Split A A₁ A₂ → Split (t ∷ A) A₁ (t ∷ A₂)

splitting-preserves : ∀ {t A A₁ A₂} → Split A A₁ A₂ → t ∈ A → t ∈ A₁ ⊎ t ∈ A₂
splitting-preserves (unr x split) here = inj₁ here
splitting-preserves (unr x split) (there t∈A) = map there there (splitting-preserves split t∈A)
splitting-preserves (linleft x split) here = inj₁ here
splitting-preserves (linleft x split) (there t∈A) = map there id (splitting-preserves split t∈A)
splitting-preserves (linrght x split) here = inj₂ here
splitting-preserves (linrght x split) (there t∈A) = map id there (splitting-preserves split t∈A)

data Expr1 (A : TCtx) : Ty → Set where
  var  : ∀ { t } → t ∈ A → Expr1 A t
  pair : ∀ { t₁ t₂ A₁ A₂ } → Split A A₁ A₂ → Expr1 A₁ t₁ → Expr1 A₂ t₂ → Expr1 A (TPair t₁ t₂)
  fst :  ∀ { t₁ t₂ } → Expr1 A (TPair t₁ t₂) → Expr1 A t₁
  snd :  ∀ { t₁ t₂ } → Expr1 A (TPair t₁ t₂) → Expr1 A t₂
  new : (s : STy) → Expr1 A (TPair (TChan s) (TChan (dual s)))
  send : ∀ { t s A₁ A₂} → Split A A₁ A₂ → Expr1 A₁ (TChan (SSend t s)) → Expr1 A₂ t → Expr1 A (TChan s)
  recv : ∀ { t s } → Expr1 A (TChan (SRecv t s)) → Expr1 A (TPair (TChan s) t)
  close : Expr1 A (TChan SEnd!) → Expr1 A TUnit
  wait  : Expr1 A (TChan SEnd?) → Expr1 A TUnit

-- threaded lookup
data Lookup (t : Ty) : (A : TCtx) → (B : TCtx) → Set where
  herelin : ∀ {A} → Lin t → Lookup t (t ∷ A) (TUnit ∷ A)
  hereunr : ∀ {A} → Unr t → Lookup t (t ∷ A) (t ∷ A)
  there   : ∀ {A B x} → Lookup t A B → Lookup t (x ∷ A) (x ∷ B)

-- syntax of type threaded expressions
data Expr' : TCtx → TCtx → Ty → Set where
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

-- relation on session types
-- session type evolves to another by a single action
data _≼S_ : STy → STy → Set where
  ≼-send : ∀ {s t} → SSend t s ≼S s
  ≼-recv : ∀ {s t} → SRecv t s ≼S s
  ≼-ilft : ∀ {s₁ s₂} → SInternal s₁ s₂ ≼S s₁
  ≼-irgt : ∀ {s₁ s₂} → SInternal s₁ s₂ ≼S s₂
  ≼-elft : ∀ {s₁ s₂} → SExternal s₁ s₂ ≼S s₁
  ≼-ergt : ∀ {s₁ s₂} → SExternal s₁ s₂ ≼S s₂

xdual-consistent : ∀ {s₁ s₂} → (b : Bool) → s₁ ≼S s₂ → xdual b s₁ ≼S xdual b s₂
xdual-consistent false ≼-send = ≼-recv
xdual-consistent true ≼-send = ≼-send
xdual-consistent false ≼-recv = ≼-send
xdual-consistent true ≼-recv = ≼-recv
xdual-consistent false ≼-ilft = ≼-elft
xdual-consistent true ≼-ilft = ≼-ilft
xdual-consistent false ≼-irgt = ≼-ergt
xdual-consistent true ≼-irgt = ≼-irgt
xdual-consistent false ≼-elft = ≼-ilft
xdual-consistent true ≼-elft = ≼-elft
xdual-consistent false ≼-ergt = ≼-irgt
xdual-consistent true ≼-ergt = ≼-ergt

data _≼T_ : Ty → Ty → Set where
  ≼-unit : TUnit ≼T TUnit
  ≼-int  : TInt ≼T TInt
  ≼-pair : ∀ {t₁ t₂ t₁' t₂'} → t₁ ≼T t₁' → t₂ ≼T t₂' → TPair t₁ t₂ ≼T TPair t₁' t₂'
  ≼-fun  : ∀ {t₁ t₂ t₁' t₂'} → t₁ ≼T t₁' → t₂ ≼T t₂' → TFun t₁ t₂ ≼T TFun t₁' t₂' -- makes sense?
  ≼-chan : ∀ {s s'} → s ≼S s' → TChan s ≼T TChan s'

-- session type evolves to another by a sequence of actions
data _≼S*_ : STy → STy → Set where
  ≼-refl : ∀ {s} → s ≼S* s
  ≼-trans : ∀ {s₁ s₂ s₃} → s₁ ≼S s₂ → s₂ ≼S* s₃ → s₁ ≼S* s₃

-- a relation on session type contexts
-- meaning that one session type context evolves into another
data _↝₀_ : SCtx → SCtx → Set where
  ↝Nil : [] ↝₀ []
  ↝Cons : ∀ {s₁ s₂ C₁ C₂} → s₁ ≼S* s₂ → C₁ ↝₀ C₂ → (s₁ ∷ C₁) ↝₀ (s₂ ∷ C₂)

data _↝₀[_,_]_ : {s₁ s₂ : STy} → (C : SCtx) → s₁ ∈ C → s₁ ≼S s₂ → SCtx → Set where
  ↝-here  : ∀ {s₁ s₂ C} 
          → (ps12 : s₁ ≼S s₂)
          → (s₁ ∷ C) ↝₀[ here , ps12 ] (s₂ ∷ C)
  ↝-there : ∀ {s s₁ s₂ C₁ C₂} {p : s₁ ∈ C₁}
          → (ps12 : s₁ ≼S s₂)
          → C₁ ↝₀[ p , ps12 ] C₂ 
          → (s ∷ C₁) ↝₀[ there p , ps12 ] (s ∷ C₂)

context-step : ∀ {C₁ C₂ : SCtx} {s₁ s₂} → {ps12 : s₁ ≼S s₂} → {p : s₁ ∈ C₁} → C₁ ↝₀[ p , ps12 ] C₂ → s₂ ∈ C₂
context-step (↝-here ps12) = here
context-step (↝-there ps12 c12) = there (context-step c12)

data _↝[_]_ : {s : STy} → (C : SCtx) → s ∈ C → SCtx → Set where
  ↝Keep : ∀ {C₁ C₂ p} → C₁ ↝₀ C₂ → C₁ ↝[ p ] C₂
  ↝Extend : ∀ {C₁ C₂ s p} → C₁ ↝[ p ] C₂ → C₁ ↝[ p ] (s ∷ C₂)

data _↝_ : (C : SCtx) → SCtx → Set where
  ↝Keep : ∀ {C₁ C₂} → C₁ ↝₀ C₂ → C₁ ↝ C₂
  ↝Extend : ∀ {C₁ C₂ s} → C₁ ↝ C₂ → C₁ ↝ (s ∷ C₂)


-- type indexed values
data Val (C : SCtx) : Ty → Set where
  VUnit : Val C TUnit
  VInt : ℕ → Val C TInt
  VPair : ∀ { t₁ t₂ } → Val C t₁ → Val C t₂ → Val C (TPair t₁ t₂)
  VChan : ∀ { s } → (b : Bool) → (p : (xdual b s) ∈ C) → Val C (TChan s)

data Unaffected {C : SCtx} {s : STy} : (t : Ty) → (x : Val C t) → (p : s ∈ C) → Set where
  U-unit : ∀ {p t} → Unaffected TUnit VUnit p

-- how about we can only lift values that are unaffected?
liftValueUnaffected :  ∀ {C₁ C₂ t s₁ s₂ p} {ps12 : s₁ ≼S s₂} 
                    → C₁ ↝₀[ p , ps12 ] C₂ → (x : Val C₁ t) → Unaffected t x p → Val C₂ t
liftValueUnaffected c12 xv uaxp = {!!}

liftValue : ∀ {C₁ C₂ t₁ t₂ s₁ s₂ p} {ps12 : s₁ ≼S s₂} → (t12 : t₁ ≼T t₂) → C₁ ↝₀[ p , ps12 ] C₂ → Val C₁ t₁ → Val C₂ t₂
liftValue ≼-unit c12 VUnit = VUnit
liftValue ≼-int c12 (VInt x) = VInt x
liftValue (≼-pair t12 t13) c12 (VPair v1 v2) = VPair (liftValue t12 c12 v1) (liftValue t13 c12 v2)
liftValue (≼-chan x) (↝-here ps12) (VChan b here) = VChan b {!!}
liftValue (≼-chan x) (↝-here ps12) (VChan b (there p)) = VChan b {!!}
liftValue (≼-chan x) (↝-there ps12 c12) (VChan b p) = {!!}

liftChan₀ : ∀ {s₁ s₂ C₁ C₂} → (b : Bool) → (p : s₁ ≼S s₂) → (cc : C₁ ↝₀ C₂) → xdual b s₁ ∈ C₁ → xdual b s₂ ∈ C₂
liftChan₀ b p ↝Nil ()
liftChan₀ b p (↝Cons x cc) here = {!!}
liftChan₀ b p (↝Cons x cc) (there ch) = {!!}

liftChan : ∀ {s₁ s₂ C₁ C₂} → (b : Bool) → (p : s₁ ≼S s₂) → (cc : C₁ ↝ C₂) → xdual b s₁ ∈ C₁ → xdual b s₂ ∈ C₂
liftChan b p (↝Keep x) ch = liftChan₀ b p x ch
liftChan b p (↝Extend cc) ch with liftChan b p cc ch
... | ch₂ = there ch₂

-- lift a value to an extended context
liftVal : ∀ {C₁ C₂ t₁ t₂} → Val C₁ t₁ → C₁ ↝ C₂ → t₁ ≼T t₂ → Val C₂ t₂
liftVal VUnit cc ≼-unit = VUnit
liftVal (VInt x) cc ≼-int = VInt x
liftVal (VPair v v₁) cc (≼-pair sub sub₁) with liftVal v cc sub | liftVal v₁ cc sub₁
... | lf1 | lf2 = VPair lf1 lf2
liftVal (VChan b p) cc (≼-chan x) = VChan b {!!}

getChanInfo : ∀ {C s} → Val C (TChan s) → Σ SCtx (λ C → Σ Bool (λ b → (xdual b s) ∈ C))
getChanInfo {C} (VChan b p) = C , b , p


-- typed environments
data Env (C : SCtx) : TCtx → Set where
  []  : Env C []
  _∷_ : ∀ { t A } (x : Val C t) (xs : Env C A) → Env C (t ∷ A)

data Chan : STy → Set where
  CToken : (s : STy) → Chan s

-- typed channel environements
data CEnv : SCtx → Set where
  [] : CEnv []
  _∷_ : ∀ { s C } (x : Chan s) (xs : CEnv C) → CEnv (s ∷ C)

lookup : ∀ {t A C} → t ∈ A → Env C A → Val C t
lookup here (t ∷ ϱ) = t
lookup (there x) (x₁ ∷ ϱ) = lookup x ϱ

simp-∈ : {s : STy} {C : SCtx} → s ∈ C → dual (dual s) ∈ C
simp-∈ {s} s∈C rewrite dual-involution s = s∈C

{-
-- interpreter for expressions
runExpr : ∀ {t} → {A : TCtx} {C : SCtx} 
  → Env C A → CEnv C → Expr A t → Σ SCtx λ C' → (CEnv C' × Val C' t)
runExpr ϱ σ (var x) = _ , σ , lookup x ϱ
runExpr ϱ σ (pair e₁ e₂) with runExpr ϱ σ e₁
runExpr ϱ σ (pair e₁ e₂) | C₁ , σ₁ , v₁ with runExpr {C = C₁} ϱ σ₁ e₂
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
runMon : ∀ {t} → {A : TCtx} {C : SCtx} 
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

-}
