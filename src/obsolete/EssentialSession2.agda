module EssentialSession2 where

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


data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)


data PosNeg : Set where
  POS NEG POSNEG : PosNeg

-- types and session types
mutual
  -- keep track which ends of a channel a process is allowed to possess
  SCtx : Set
  SCtx = List (STy × PosNeg)

  data Ty (G : SCtx) : Set where
    TUnit : Ty G
    TInt : Ty G
    TPair : Ty G → Ty G → Ty G
    TChan : ∀ {pn} → (s : STy) → (s , pn) ∈ G → Ty G

  data STy : Set where
    SSend : ∀ {G} → Ty G → STy → STy
    SRecv : ∀ {G} → Ty G → STy → STy
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
data Lin (G : SCtx) : Ty G → Set where
  LChan : ∀ {s pf} → Lin G (TChan s pf)
  LPair1 : ∀ {t₁ t₂} → Lin G t₁ → Lin G (TPair t₁ t₂)
  LPair2 : ∀ {t₁ t₂} → Lin G t₂ → Lin G (TPair t₁ t₂)

data Unr (G : SCtx) : Ty G → Set where
  UUnit : Unr G TUnit
  UInt : Unr G TInt
  UPair : ∀ {t₁ t₂} → Unr G t₁ → Unr G t₂ → Unr G (TPair t₁ t₂)

-- lin and unr are mutually exclusive
lemma-lin-unr : ∀ {G t} → Lin G t → ¬ Unr G t
lemma-lin-unr LChan ()
lemma-lin-unr (LPair1 lint) (UPair x x₁) = lemma-lin-unr lint x
lemma-lin-unr (LPair2 lint) (UPair x x₁) = lemma-lin-unr lint x₁

lemma-unr-lin : ∀ {G t} → Unr G t → ¬ Lin G t
lemma-unr-lin UUnit ()
lemma-unr-lin UInt ()
lemma-unr-lin (UPair unr unr₁) (LPair1 lin) = lemma-unr-lin unr lin
lemma-unr-lin (UPair unr unr₁) (LPair2 lin) = lemma-unr-lin unr₁ lin

-- contexts for types and session types
TCtx : SCtx → Set
TCtx G = List (Ty G)


-- context splitting, respecting linearity
data Split (G : SCtx) : TCtx G → TCtx G → TCtx G → Set where
  [] : Split G [] [] []
  unr : ∀ {t Φ Φ₁ Φ₂} → Unr G t → Split G Φ Φ₁ Φ₂ → Split G (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  linleft : ∀ {t Φ Φ₁ Φ₂} → Lin G t → Split G Φ Φ₁ Φ₂ → Split G (t ∷ Φ) (t ∷ Φ₁) Φ₂
  linrght : ∀ {t Φ Φ₁ Φ₂} → Lin G t → Split G Φ Φ₁ Φ₂ → Split G (t ∷ Φ) Φ₁ (t ∷ Φ₂)

splitting-preserves : ∀ {G t Φ Φ₁ Φ₂} → Split G Φ Φ₁ Φ₂ → t ∈ Φ → t ∈ Φ₁ ⊎ t ∈ Φ₂
splitting-preserves (unr x split) here = inj₁ here
splitting-preserves (unr x split) (there t∈Φ) = map there there (splitting-preserves split t∈Φ)
splitting-preserves (linleft x split) here = inj₁ here
splitting-preserves (linleft x split) (there t∈Φ) = map there id (splitting-preserves split t∈Φ)
splitting-preserves (linrght x split) here = inj₂ here
splitting-preserves (linrght x split) (there t∈Φ) = map id there (splitting-preserves split t∈Φ)

splitting-reflects-left : ∀ {G t Φ Φ₁ Φ₂} → Split G Φ Φ₁ Φ₂ → t ∈ Φ₁ → t ∈ Φ
splitting-reflects-left (unr x split) here = here
splitting-reflects-left (linleft x split) here = here
splitting-reflects-left (linrght x split) here = there (splitting-reflects-left split here)
splitting-reflects-left (unr x split) (there t∈Φ₁) = there (splitting-reflects-left split t∈Φ₁)
splitting-reflects-left (linleft x split) (there t∈Φ₁) = there (splitting-reflects-left split t∈Φ₁)
splitting-reflects-left (linrght x split) (there t∈Φ₁) = there (splitting-reflects-left split (there t∈Φ₁))


-- type indexed values
data Val (G : SCtx) : Ty G → Set where
  VUnit : Val G TUnit
  VInt  : ℕ → Val G TInt
  VPair : ∀ { t₁ t₂ } → Val G t₁ → Val G t₂ → Val G (TPair t₁ t₂)
  VChan : ∀ { s } → (b : Bool) → Val G (TChan (xdual b s) ?)

-- a channel is represented by a single entry in the session context
-- two channel endpoints belong to each channel, distinguished by a boolean flag
-- dependending on the flag value, the type of the endpoint corresponds either to session type in the context or to its dual
-- the run-time representation of a channel is unit

-- type indexed environments
data VEnv (G : SCtx) : TCtx G → Set where
  []  : VEnv G []
  _∷_ : ∀ { t Φ } (x : Val G t) (xs : VEnv G Φ) → VEnv G (t ∷ Φ)



-- split environment according to type context split
split-env : ∀ {G Φ Φ₁ Φ₂} → Split G Φ Φ₁ Φ₂ → VEnv G Φ → VEnv G Φ₁ × VEnv G Φ₂
split-env [] [] = [] , []
split-env (unr x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , (x ∷ ϱ₂)
split-env (linleft x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = (x ∷ ϱ₁) , ϱ₂
split-env (linrght x₁ sp) (x ∷ ϱ) with split-env sp ϱ
... | ϱ₁ , ϱ₂ = ϱ₁ , (x ∷ ϱ₂)

-- lookup an entry in a typed environemtn
lookupEnv : ∀ {G Φ t} → VEnv G Φ → t ∈ Φ → Val G t
lookupEnv (x ∷ ϱ) here = x
lookupEnv (x ∷ ϱ) (there x₁) = lookupEnv ϱ x₁


--------------------------------------------------------------------------------
-- experiment #2


-- SSplit G G₁ G₂
-- split G into G₁ and G₂
data SSplit : SCtx → SCtx → SCtx → Set where
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
data Val' (G : SCtx) : Ty G → Set where
  VUnit : Val' G TUnit
  VInt  : ℕ → Val' G TInt
  VPair : ∀ { t₁ t₂ } (v₁ : Val' G t₁) (v₂ : Val' G t₂) → Val' G (TPair t₁ t₂)
  VChan : ∀ {s pn} → (pf : (s , pn) ∈ G) → (b : Bool) → ValidEnd pn b
        → Val' G (TChan (xdual b s) ?)

-- type indexed environments
data VEnv' (G : SCtx) : TCtx G → Set where
  []  : VEnv' G []
  _∷_ : ∀ { t Φ } (x : Val' G t) (xs : VEnv' G Φ) → VEnv' G (t ∷ Φ)


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

data Result0 (G : SCtx) (A : Set) : Set where
  Return : (x : A) → Result0 G A

{-
bind0 : ∀ {Φ Φ₁ Φ₂ G₁ G2 G3 A B} 
      → Split Φ Φ₁ Φ₂
      → Mon Φ₁ G₁ G2 A 
      → (A -> Mon Φ₂ G2 G3 B)
      → Mon Φ G₁ G3 B
-}
bind0 : ∀ {G Φ Φ₁ Φ₂ A B} 
      → Split G Φ Φ₁ Φ₂
      → (VEnv' G Φ₁ → Result0 G A)
      → (A -> VEnv' G Φ₂ → Result0 G B)
      → (VEnv' G Φ → Result0 G B)
bind0 sp ma fab ϱ = {!!}


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


data Eff (G : SCtx) : Set where
  ENone : Eff G
  ESeq  : Eff G → Eff G → Eff G
  ENew  : Eff G
  EFork : Eff G → Eff G
  ESend : Ty G → Eff G
  ERecv : Ty G → Eff G

-- syntax of typed and effected expressions
data Expr' (G : SCtx) (Φ : TCtx G) : Ty G → Eff G → Set where
  var : ∀ { t } → t ∈ Φ → Expr' G Φ t ENone
  nat : ℕ → Expr' G Φ TInt ENone
  letx : ∀ { t₁ t₂ Φ₁ Φ₂ ε₁ ε₂ } 
       → (sp : Split G Φ Φ₁ Φ₂)
       → (e₁ : Expr' G Φ₁ t₁ ε₁) 
       → (e₂ : Expr' G (t₁ ∷ Φ₂) t₂ ε₂) 
       → Expr' G Φ t₂ (ESeq ε₁ ε₂)
  pair : ∀ { t₁ t₂ Φ₁ Φ₂ ε₁ ε₂ } 
       → (sp : Split G Φ Φ₁ Φ₂)
       → (e₁ : Expr' G Φ₁ t₁ ε₁)
       → (e₂ : Expr' G Φ₂ t₂ ε₂)
       → Expr' G Φ (TPair t₁ t₂) (ESeq ε₁ ε₂)
  letpair : ∀ { t t₁ t₂ Φ₁ Φ₂ ε₁ ε₂ }
       → (sp : Split G Φ Φ₁ Φ₂)
       → (e₁ : Expr' G Φ₁ (TPair t₁ t₂) ε₁)
       → (e₂ : Expr' G (t₁ ∷ t₂ ∷ Φ₂) t ε₁) 
       → Expr' G Φ t (ESeq ε₁ ε₂)
  fork : ∀ {ε}
       → Expr' G Φ TUnit ε
       → Expr' G Φ TUnit (EFork ε)
  new : (s : STy)
      → Expr' G Φ (TPair (TChan s ?) (TChan (dual s) ?)) ENew
  send : ∀ { t s Φ₁ Φ₂ ε₁ ε₂ }
       → (sp : Split G Φ Φ₁ Φ₂)
       → (e₁ : Expr' G Φ₁ (TChan (SSend t s) ?) ε₁)
       → (e₂ : Expr' G Φ₂ t ε₂)
       → Expr' G Φ (TChan s ?) (ESeq ε₁ (ESeq ε₂ (ESend t))) 
       -- want to know on which channel I'm sending: needs to be part of the type
  recv : ∀ { t s ε }
       → Expr' G Φ (TChan (SRecv t s) ?) ε
       → Expr' G Φ (TPair (TChan s) t) (ESeq ε (ERecv t))
  -- close : Expr Φ (TChan SEnd!) → Expr Φ TUnit
  -- wait  : Expr Φ (TChan SEnd?) → Expr Φ TUnit

