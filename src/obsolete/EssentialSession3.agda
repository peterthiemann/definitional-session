module EssentialSession3 where

open import Data.List
open import Data.Product

data _∈_ {a : Set} (x : a) : List a → Set where
  here  : ∀ { xs } → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → x ∈ xs → x ∈ (x₀ ∷ xs)


data PosNeg : Set where
  POS NEG POSNEG : PosNeg

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


data Channel : STy → Set where
  CSend : ∀ {s t} → Channel s → Channel (SSend t s)
  CRecv : ∀ {s t} → Channel s → Channel (SRecv t s)
  CEnd! : Channel SEnd!
  CEnd? : Channel SEnd?

-- keep track which ends of a channel a process is allowed to possess
SCtx : Set
SCtx = List (STy × PosNeg)

-- SSplit G G₁ G₂
-- split G into G₁ and G₂
data SSplit : SCtx → SCtx → SCtx → Set where
  ss-[]    : SSplit [] [] []
  ss-left  : ∀ {G G₁ G₂ sp} → SSplit G G₁ G₂ → SSplit (sp ∷ G) (sp ∷ G₁) G₂
  ss-right : ∀ {G G₁ G₂ sp} → SSplit G G₁ G₂ → SSplit (sp ∷ G) G₁ (sp ∷ G₂)
  ss-pn    : ∀ {G G₁ G₂ s} → SSplit G G₁ G₂ → SSplit ((s , POSNEG) ∷ G) ((s , POS) ∷ G₁) ((s , NEG) ∷ G₂)
  ss-np    : ∀ {G G₁ G₂ s} → SSplit G G₁ G₂ → SSplit ((s , POSNEG) ∷ G) ((s , NEG) ∷ G₁) ((s , POS) ∷ G₂)


data CEnv : (G : SCtx) → Set where
  [] : CEnv []
  _∷_ : ∀ {G} → (spn : STy × PosNeg) → (ψ : CEnv G) → CEnv (spn ∷ G)

data CSplit : (G : SCtx) (G₁ : SCtx) (G₂ : SCtx) (sp : SSplit G G₁ G₂)
               (ψ : CEnv G) (ψ₁ : CEnv G₁) (ψ₂ : CEnv G₂) → Set where

data TSend (t : Ty) : SCtx → SCtx → Set where
  SendPos : ∀ {s G} → TSend t ((SSend t s , POS) ∷ G) ((s , POS) ∷ G)
  SendNeg : ∀ {s G} → TSend t ((SRecv t s , NEG) ∷ G) ((s , NEG) ∷ G)
  SendDeeper : ∀ {G G' spn} → TSend t G G' → TSend t (spn ∷ G) (spn ∷ G')

data TRecv (t : Ty) : SCtx → SCtx → Set where
  RecvNeg : ∀ {s G} → TRecv t ((SSend t s , NEG) ∷ G) ((s , NEG) ∷ G)
  RecvPos : ∀ {s G} → TRecv t ((SRecv t s , POS) ∷ G) ((s , POS) ∷ G)
  RecvDeeper : ∀ {G G' spn} → TRecv t G G' → TRecv t (spn ∷ G) (spn ∷ G')

data Eff : SCtx → SCtx → Set where
  ENone : Eff [] []
  ESeq  : ∀ {G G₁ G₁' G₂ G₂'}
        → SSplit G G₁ G₂ 
        → Eff G₁ G₁'
        → Eff G₂ G₂'
        → Eff G G₂
  ENew  : (s : STy) → Eff [] [ s , POSNEG ]
  EFork : ∀ {G} → Eff G [] → Eff G []
  ESend : ∀ {t G G'} → TSend t G G' → Eff G G'
  ERecv : ∀ {t G G'} → TRecv t G G' → Eff G G'


data Expr : (G : SCtx) (G' : SCtx) → CEnv G → Ty → Eff G G' → Set where
  fork : ∀ {G ψ ε}
       → Expr G [] ψ TUnit ε
       → Expr G [] ψ TUnit (EFork ε)
  new  : ∀ {ψ}
       → (s : STy)
       → Expr [] [ s , POSNEG ] ψ (TPair (TChan s) (TChan (dual s))) (ENew s)
  send : ∀ {G₁ G₁' ψ₁ ε₁ G₂ G₂' ψ₂ ε₂ G G' ψ t s} { ts ss₂}
       → (ss : SSplit G G₁ G₂)
       → Expr G₁ G₁' ψ₁ (TChan (SSend t s)) ε₁
       → Expr G₂ G₂' ψ₂ t ε₂
       → Expr G G' ψ (TChan s)  (ESeq ss₂ (ESeq ss ε₁ ε₂)  (ESend ts))

data Val (G : SCtx) : Ty → Set where
  VChan : ∀ {s pn} → ( s , pn ) ∈ G → Val G (TChan s)

-- computation for type: Expr G Φ τ ε
-- Command ((ψ : CEnv G) → (ϱ : VEnv ψ Φ) → Σ CEnv λ ψ' → (Rel ε ψ ψ' × Val ψ τ))

data Command (A : Set) : Set where
  Return : (x : A) → Command A
