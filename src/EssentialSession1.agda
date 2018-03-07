module EssentialSession1 where

open import Data.Bool
open import Data.Fin
open import Data.List hiding (map ; reverse ; _++_)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum
open import Data.Unit
open import Data.Vec hiding (_∈_ ; map ; _>>=_ )
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_] ; cong)
open import Relation.Binary.HeterogeneousEquality

-- types and session types
mutual
  data Ty : Set where
    TUnit : Ty
    TInt : Ty
    TPair : Ty → Ty → Ty
    TChan : STy → Ty

  data STy : Set where
    SSend : Ty → STy → STy
    SRecv : Ty → STy → STy
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

data PosNeg : Set where
  POS NEG POSNEG : PosNeg

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

-- contexts for types and session types
TCtx = List Ty
SCtx = List STy

data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)

-- context splitting, respecting linearity
data Split : TCtx → TCtx → TCtx → Set where
  [] : Split [] [] []
  unr : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  linleft : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) Φ₂
  linrght : ∀ {t Φ Φ₁ Φ₂} → Lin t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ (t ∷ Φ₂)

splitting-preserves : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → t ∈ Φ → t ∈ Φ₁ ⊎ t ∈ Φ₂
splitting-preserves (unr x split) here = inj₁ here
splitting-preserves (unr x split) (there t∈Φ) = map there there (splitting-preserves split t∈Φ)
splitting-preserves (linleft x split) here = inj₁ here
splitting-preserves (linleft x split) (there t∈Φ) = map there id (splitting-preserves split t∈Φ)
splitting-preserves (linrght x split) here = inj₂ here
splitting-preserves (linrght x split) (there t∈Φ) = map id there (splitting-preserves split t∈Φ)

splitting-reflects-left : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → t ∈ Φ₁ → t ∈ Φ
splitting-reflects-left (unr x split) here = here
splitting-reflects-left (linleft x split) here = here
splitting-reflects-left (linrght x split) here = there (splitting-reflects-left split here)
splitting-reflects-left (unr x split) (there t∈Φ₁) = there (splitting-reflects-left split t∈Φ₁)
splitting-reflects-left (linleft x split) (there t∈Φ₁) = there (splitting-reflects-left split t∈Φ₁)
splitting-reflects-left (linrght x split) (there t∈Φ₁) = there (splitting-reflects-left split (there t∈Φ₁))

-- syntax of typed expressions
data Expr (Φ : TCtx) : Ty → Set where
  var : ∀ { t } → t ∈ Φ → Expr Φ t
  nat : ℕ → Expr Φ TInt
  letx : ∀ { t₁ t₂ Φ₁ Φ₂ } → (sp : Split Φ Φ₁ Φ₂) → (e₁ : Expr Φ₁ t₁) → (e₂ : Expr (t₁ ∷ Φ₂) t₂) → Expr Φ t₂
  pair : ∀ { t₁ t₂ Φ₁ Φ₂ } → (sp : Split Φ Φ₁ Φ₂) → (e₁ : Expr Φ₁ t₁) → (e₂ : Expr Φ₂ t₂) → Expr Φ (TPair t₁ t₂)
  letpair : ∀ { t t₁ t₂ Φ₁ Φ₂ } → (sp : Split Φ Φ₁ Φ₂) → (e₁ : Expr Φ₁ (TPair t₁ t₂)) → (e₂ : Expr (t₁ ∷ t₂ ∷ Φ₂) t) → Expr Φ t
  fork : Expr Φ TUnit → Expr Φ TUnit
  new : (s : STy) → Expr Φ (TPair (TChan s) (TChan (dual s)))
  send : ∀ { t s Φ₁ Φ₂ } → (sp : Split Φ Φ₁ Φ₂) → (e₂ : Expr Φ₁ (TChan (SSend t s))) → (e₂ : Expr Φ₂ t) → Expr Φ (TChan s)
  recv : ∀ { t s } → Expr Φ (TChan (SRecv t s)) → Expr Φ (TPair (TChan s) t)
  close : Expr Φ (TChan SEnd!) → Expr Φ TUnit
  wait  : Expr Φ (TChan SEnd?) → Expr Φ TUnit


-- type indexed values
data Val : Ty → Set where
  VUnit : Val TUnit
  VInt  : ℕ → Val TInt
  VPair : ∀ { t₁ t₂ } → Val t₁ → Val t₂ → Val (TPair t₁ t₂)
  VChan : ∀ { s } → (b : Bool) → Val (TChan (xdual b s))

-- a channel is represented by a single entry in the session context
-- two channel endpoints belong to each channel, distinguished by a boolean flag
-- dependending on the flag value, the type of the endpoint corresponds either to session type in the context or to its dual
-- the run-time representation of a channel is unit

-- type indexed environments
data VEnv : TCtx → Set where
  []  : VEnv []
  _∷_ : ∀ { t Φ } (x : Val t) (xs : VEnv Φ) → VEnv (t ∷ Φ)

-- outcomes of a computation
-- for implementing a state transformers with resumptions and extra actions
-- * Pause is a paused computation with a continuation
-- * Fork requests creation of a new process by offering two continuations
-- * RecvFrom waits for input from a designated channel (with continuation)
-- * SendTo sends output to a designated channel (waits for rendezvous, with continuation)
data Result (A : Set) : Set where
  Return    : (x : A) 
            → Result A
  Pause     : (cont   : ⊤ → Result A)
            → Result A
  Fork      : (forked : ⊤ → Result (Val TUnit))
            → (cont   : ⊤ → Result A)
            → Result A
  New       : (s : STy)
            → (cont : (cp : Val (TPair (TChan s) (TChan (dual s)))) → Result A)
            → Result A
  RecvFrom : {t : Ty} {s : STy} 
            → (ch :  Val (TChan (SRecv t s)))
            → (cont : (ch' : Val (TChan s))
                    → Val t
                    → Result A)
            → Result A
  SendTo  : {t : Ty} {s : STy}
            → (ch :  Val (TChan (SSend t s)))
            → Val t
            → (cont : Val (TChan s) → Result A)
            → Result A
  Close     : (ch : Val (TChan SEnd!))
            → (cont : Val TUnit → Result A)
            → Result A
  Wait      : (ch : Val (TChan SEnd?))
            → (cont : Val TUnit → Result A)
            → Result A


-- the Result data type can be made into a monad
return : ∀ {A} → A → Result A
return a = Return a

_>>=_ : ∀ {A B} → Result A → (A → Result B) → Result B
Return x >>= f = f x
Pause cont >>= f = Pause λ x → cont x >>= f
Fork forked cont >>= f = Fork forked (λ _ → cont tt >>= f)
New s cont >>= f = New s λ v → cont v >>= f
RecvFrom ch cont >>= f = RecvFrom ch (λ ch' z → cont ch' z >>= f)
SendTo ch x cont >>= f = SendTo ch x (λ ch' → cont ch' >>= f)
Close ch cont >>= f = Close ch (λ z → cont z >>= f)
Wait ch cont >>= f = Wait ch (λ z → cont z >>= f)


-- split environment according to type context split
split-env : ∀ {Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → VEnv Φ → VEnv Φ₁ × VEnv Φ₂
split-env [] [] = [] , []
split-env (unr x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env (linleft x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env (linrght x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- lookup an entry in a typed environemtn
lookupEnv : ∀ {Φ t} → VEnv Φ → t ∈ Φ → Val t
lookupEnv (x ∷ ϱ) here = x
lookupEnv (x ∷ ϱ) (there x₁) = lookupEnv ϱ x₁

-- -- monadic interpreter for expressions
-- * TODO: make mutually recursive with a function that counts down fuel and changes Return to Pause when fuel runs out
runExpr : ∀ {t Φ} → Expr Φ t → VEnv Φ → Result (Val t)
runExpr (var x) ϱ = return (lookupEnv ϱ x)
runExpr (nat x) ϱ = return (VInt x)
runExpr (letx sp e₁ e₂) ϱ with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr e₁ ϱ₁ >>= λ v₁ → runExpr e₂ (v₁ ∷ ϱ₂)
runExpr (pair sp e₁ e₂) ϱ with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr e₁ ϱ₁ >>= λ v₁ → runExpr e₂ ϱ₂ >>= λ v₂ → return (VPair v₁ v₂)
runExpr (letpair sp e₁ e₂) ϱ with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr e₁ ϱ₁ >>= λ{(VPair v₁ v₂) → runExpr e₂ (v₁ ∷ v₂ ∷ ϱ₂)}
runExpr (fork e) ϱ = Fork (λ _ → runExpr e ϱ) (λ _ → Return VUnit)
runExpr (new s) ϱ = New s Return
runExpr (send sp e₁ e₂) ϱ with split-env sp ϱ
... | ϱ₁ , ϱ₂ = runExpr e₁ ϱ₁ >>= λ v₁ → runExpr e₂ ϱ₂ >>= λ v₂ → SendTo v₁ v₂ Return
runExpr (recv e) ϱ = runExpr e ϱ >>= λ v → RecvFrom v (λ ch' z → Return (VPair ch' z))
runExpr (close e) ϱ = runExpr e ϱ >>= λ v → Close v Return
runExpr (wait e) ϱ = runExpr e ϱ >>= λ v → Wait v Return

-- processes
data Proc (Φ : TCtx) : Set where
  Pi : (s : STy) → (P : Proc (TChan s ∷ TChan (dual s) ∷ Φ)) → Proc Φ
  Par : ∀ {Φ₁ Φ₂} → (sp : Split Φ Φ₁ Φ₂) → (P : Proc Φ₁) → (Q : Proc Φ₂) → Proc Φ
  Exp : Expr Φ TUnit → Proc Φ

-- -- missing stuff
-- -- * monadic scheduler for processes



actOn   : SCtx → List (Result (Val TUnit)) → List (Result (Val TUnit))
runProc : Expr [] TUnit → List (Result (Val TUnit))

actOn G [] = []
actOn G (Return x ∷ rs) = Return x ∷ actOn G rs
actOn G (Pause cont ∷ rs) = cont tt ∷ actOn G rs
actOn G (Fork forked cont ∷ rs) = forked tt ∷ cont tt ∷ actOn G rs
actOn G (New s cont ∷ rs) = let G' = s ∷ G
                                v₁ = VChan true
                                v₂ = VChan false
                            in  (cont (VPair v₁ v₂)) ∷ (actOn G' rs)
actOn G (RecvFrom ch cont ∷ rs) = {!!}
actOn G (SendTo ch x cont ∷ rs) = {!!}
actOn G (Close ch cont ∷ rs) = {!!}
actOn G (Wait ch cont ∷ rs) = {!!}

runProc e = actOn [] Data.List.[ runExpr e [] ]

--------------------------------------------------------------------------------
-- experiment #2

-- keep track which ends of a channel a process is allowed to possess
SCtx' = List (STy × PosNeg)

-- SSplit G G₁ G₂
-- split G into G₁ and G₂
data SSplit : SCtx' → SCtx' → SCtx' → Set where
  ss-[]    : SSplit [] [] []
  ss-left  : ∀ {G G₁ G₂ sp} → SSplit G G₁ G₂ → SSplit (sp ∷ G) (sp ∷ G₁) G₂
  ss-right : ∀ {G G₁ G₂ sp} → SSplit G G₁ G₂ → SSplit (sp ∷ G) G₁ (sp ∷ G₂)
  ss-pn    : ∀ {G G₁ G₂ s} → SSplit G G₁ G₂ → SSplit ((s , POSNEG) ∷ G) ((s , POS) ∷ G₁) ((s , NEG) ∷ G₂)
  ss-np    : ∀ {G G₁ G₂ s} → SSplit G G₁ G₂ → SSplit ((s , POSNEG) ∷ G) ((s , NEG) ∷ G₁) ((s , POS) ∷ G₂)

-- ValidEnd indicates that the channel end available in the typing environment matches the one indicated by the channel value
data ValidEnd : PosNeg → Bool → Set where
  ValidPosTrue  : ValidEnd POS true
  ValidNegFalse : ValidEnd NEG false
  -- obsolete after introducing splitting
  -- ValidPosNegTrue : ValidEnd POSNEG true
  -- ValidPosNegFalse : ValidEnd POSNEG false

-- revision for channel values
data Val' (G : SCtx') : Ty → Set where
  VUnit : Val' G TUnit
  VInt  : ℕ → Val' G TInt
  VPair : ∀ { G₁ G₂ t₁ t₂ } (ss : SSplit G G₁ G₂) (v₁ : Val' G₁ t₁) (v₂ : Val' G₂ t₂) → Val' G (TPair t₁ t₂)
  VChan : ∀ {s pn} → (s , pn) ∈ G → (b : Bool) → ValidEnd pn b → Val' G (TChan (xdual b s))

-- type indexed environments
data VEnv' : SCtx' → TCtx → Set where
  []  : VEnv' [] []
  _∷_ : ∀ { t Φ G G₁ G₂ }
      (ss : SSplit G G₁ G₂) (x : Val' G₁ t) (xs : VEnv' G₂ Φ) → VEnv' G (t ∷ Φ)

split-env' : ∀ {Φ Φ₁ Φ₂ G₁ G₂ G₃}
            → Split Φ Φ₁ Φ₂ → VEnv' G₁ Φ → VEnv' G₂ Φ₁ × VEnv' G₃ Φ₂
split-env' = {!!}

-- outcomes of a computation
-- the actual computation with result A is a map:
-- (G : SCtx) → (ϱ : VEnv' G Φ) → Result' G A

-- (G : SCtx) → (ϱ : VEnv' G Φ) → Σ SCtx λ G' → G ↝ G' → Result' G' A

-- Σ TCtx λ Φ → (G G' : SCtx) → G ↝ G' → (ϱ : VEnv' G Φ) → Result G' A

-- bind : M G G' A → (A → M G' G'' B) → M G G'' B

-- fork  : M G [] TUnit
--       → M G [] TUnit
-- new s : M [] [s] (TPair (TChan s) (TChan (dual s)))
-- recv  : TChan 'here' (SRecv t s) 
--       → M  [SRecv t s] [s] t
-- send  : TChan 'here' (SSend t s) → t
--       → M [SSend t s] [s] TUnit
-- close : TChan 'here' SEnd!
--       → M [SEnd!] [] TUnit
-- wait  : TChan 'here' SEnd?
--       → M [SEnd?] [] TUnit

-- Fork  : split G G₁ G₂
--       → M G₁ [] TUnit
--       → M G G₂ TUnit
-- new s : M G (s ∷ G) (TPair (TChan s) (TChan (dual s)))
-- recv  : TChan p (SRecv t s) 
--       → M G@p=[SRecv t s] G@p=[s] t
-- send  : TChan p (SSend t s) → t
--       → M G@p=[SSend t s] G@p=[s] TUnit
-- close : TChan p SEnd!
--       → M G@p=[SEnd!] (delete G p) TUnit
-- wait  : TChan p SEnd?
--       → M G@p=[SEnd?] (delete G p) TUnit

-- M Φ G1 G2 A = (Φ) → (G1) → VEnv G1 Φ → Result G2 A

-- bind : split Φ Φ₁ Φ₂ → M Φ₁ G G2 A -> (A -> M Φ₂ G2 G3 B) → M Φ G G3 B
-- bind sp m f =
--   λ Φ G ϱ → 
--   let (ϱ₁ , ϱ₂) = split-env sp ϱ in
--   case (m Φ₁ G ϱ₁) of
--     Return a   → f a Φ₂ G ϱ₂ -- G1=G2
--     Pause  m   → Pause (bind m f)
--     New s  c   → New s (λ z → bind sp (c z) f)
--     Recv x c   → Recv x (λ z → bind sp (c z) f)
--     Send x y c → Send x y (λ z → bind sp (c z) f)

Mon : (Φ : TCtx) (G₁ : SCtx) (G₂ : SCtx) (A : Set) → Set
Mon Φ G₁ G₂ A = {!!}

data Result0 (G : SCtx') (A : Set) : Set where
  Return : (x : A) → Result0 G A

{-
bind0 : ∀ {Φ Φ₁ Φ₂ G₁ G2 G3 A B} 
      → Split Φ Φ₁ Φ₂
      → Mon Φ₁ G₁ G2 A 
      → (A -> Mon Φ₂ G2 G3 B)
      → Mon Φ G₁ G3 B
-}
bind0 : ∀ {Φ Φ₁ Φ₂ G₁ G₂ G₃ A B} 
      → Split Φ Φ₁ Φ₂
      → (VEnv' G₁ Φ₁ → Result0 G₂ A)
      → (A -> VEnv' G₂ Φ₂ → Result0 G₃ B)
      → (VEnv' G₁ Φ → Result0 G₃ B)
bind0 sp ma fab ϱ with split-env' sp ϱ
... | pp = {!!}


-- data Result' (G : SCtx') : (G' : SCtx') (A : Set) → Set where
--   Return    : ∀ {A}
--             → (x : A) 
--             → Result' G G A
--   -- to resume a computation later on, I can continue with the same G
--   Pause     : ∀ {A G'}
--             → (cont   : ⊤ → Result' G G' A)
--             → Result' G G' A
-- --   Fork      : (forked : Σ TCtx λ Φ → VEnv' G Φ × ((G' : SCtx) → VEnv' G' Φ → Result' G' (Val' G' TUnit)))
-- --             → (cont   : (G' : SCtx) → Result' G' A)
-- --             → Result' G A
--   -- to create a new channel
--   New       : ∀ {A}
--             → (s : STy)
--             → let G' = ( s , POSNEG ) ∷ G in
--               (cont : Σ TCtx λ Φ → VEnv' G Φ
--                     × (VEnv' G' Φ → (cp : Val' G' (TPair (TChan s) (TChan (dual s)))) → Result' G G' A))
--             → Result' G G' A
-- --   RecvFrom : {t : Ty} {s : STy} 
-- --             → (ch :  Val' G (TChan (SRecv t s)))
-- --             → (cont : (ch' : Val' G (TChan s))
-- --                     → Val' G t
-- --                     → Result' G A)
-- --             → Result' G A
-- --   SendTo  : {t : Ty} {s : STy}
-- --             → (ch :  Val' G (TChan (SSend t s)))
-- --             → Val' G t
-- --             → (cont : Val' G (TChan s) → Result' G A)
-- --             → Result' G A
-- --   Close     : (ch : Val' G (TChan SEnd!))
-- --             → (cont : Val' G TUnit → Result' G A)
-- --             → Result' G A
-- --   Wait      : (ch : Val' G (TChan SEnd?))
-- --             → (cont : Val' G TUnit → Result' G A)
-- --             → Result' G A

-- -- munit : ∀ {A Φ}
-- --       → A
-- --       → ((G : SCtx) → VEnv' G Φ → Result' G A)
-- -- munit = {!!}

-- -- mbind : ∀ {A B Φ}
-- --      → ((G : SCtx) → VEnv' G Φ → Result' G A)
-- --      → (A → ((G' : SCtx) → VEnv' G' Φ → Result' G' B))
-- --      → ((G'' : SCtx) → VEnv' G'' Φ → Result' G'' B)
-- -- mbind = {!!}

-- -- runExpr' : ∀ {t Φ} → Expr Φ t → (G : SCtx) → VEnv' G Φ → Result' G (Val' G t)
-- -- runExpr' (var x) G ϱ = {!!}
-- -- runExpr' (nat x) G ϱ = {!!}
-- -- runExpr' (letx sp e e₁) G ϱ = {!!}
-- -- runExpr' (pair sp e e₁) G ϱ = {!!}
-- -- runExpr' (letpair sp e e₁) G ϱ = {!!}
-- -- runExpr' (fork e) G ϱ = Fork (_ , ϱ , runExpr' e) (λ G' → Return VUnit)
-- -- runExpr' (new s) G ϱ = New s (_ , ϱ , λ G' ϱ' v' → Return {!!})
-- -- runExpr' (send sp e e₁) G ϱ = {!!}
-- -- runExpr' (recv e) G ϱ = {!!}
-- -- runExpr' (close e) G ϱ = {!!}
-- -- runExpr' (wait e) G ϱ = {!!}

-- -- -- experiemnt #3
-- -- data Result'' (A : Set) : Set where
-- --   Return : (x : A) (Φ : TCtx) (G : SCtx) (ϱ : VEnv' G Φ)
-- --          → Result'' A

-- -- -- experiment #4
-- data Val'' {n} : Vec STy n → Ty → Set where
--   VChan : ∀ {G} → (i : Fin n) → Val'' G (TChan (lookup i (reverse G)))

-- -- seems to run into problems involving heterogeneous equality...


data Eff : Set where
  ENone : Eff
  ESeq  : Eff → Eff → Eff
  ENew  : Eff
  EFork : Eff → Eff
  ESend : Ty → Eff
  ERecv : Ty → Eff

-- syntax of typed and effected expressions
data Expr' (Φ : TCtx) : Ty → Eff → Set where
  var : ∀ { t } → t ∈ Φ → Expr' Φ t ENone
  nat : ℕ → Expr' Φ TInt ENone
  letx : ∀ { t₁ t₂ Φ₁ Φ₂ ε₁ ε₂ } 
       → (sp : Split Φ Φ₁ Φ₂)
       → (e₁ : Expr' Φ₁ t₁ ε₁) 
       → (e₂ : Expr' (t₁ ∷ Φ₂) t₂ ε₂) 
       → Expr' Φ t₂ (ESeq ε₁ ε₂)
  pair : ∀ { t₁ t₂ Φ₁ Φ₂ ε₁ ε₂ } 
       → (sp : Split Φ Φ₁ Φ₂)
       → (e₁ : Expr' Φ₁ t₁ ε₁)
       → (e₂ : Expr' Φ₂ t₂ ε₂)
       → Expr' Φ (TPair t₁ t₂) (ESeq ε₁ ε₂)
  letpair : ∀ { t t₁ t₂ Φ₁ Φ₂ ε₁ ε₂ }
       → (sp : Split Φ Φ₁ Φ₂)
       → (e₁ : Expr' Φ₁ (TPair t₁ t₂) ε₁)
       → (e₂ : Expr' (t₁ ∷ t₂ ∷ Φ₂) t ε₁) 
       → Expr' Φ t (ESeq ε₁ ε₂)
  fork : ∀ {ε}
       → Expr' Φ TUnit ε
       → Expr' Φ TUnit (EFork ε)
  new : (s : STy)
      → Expr' Φ (TPair (TChan s) (TChan (dual s))) ENew
  send : ∀ { t s Φ₁ Φ₂ ε₁ ε₂ }
       → (sp : Split Φ Φ₁ Φ₂)
       → (e₁ : Expr' Φ₁ (TChan (SSend t s)) ε₁)
       → (e₂ : Expr' Φ₂ t ε₂)
       → Expr' Φ (TChan s) (ESeq ε₁ (ESeq ε₂ (ESend t))) 
       -- want to know on which channel I'm sending: needs to be part of the type
  recv : ∀ { t s ε }
       → Expr' Φ (TChan (SRecv t s)) ε
       → Expr' Φ (TPair (TChan s) t) (ESeq ε (ERecv t))
  -- close : Expr Φ (TChan SEnd!) → Expr Φ TUnit
  -- wait  : Expr Φ (TChan SEnd?) → Expr Φ TUnit

