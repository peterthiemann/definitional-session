module Values where

open import Data.Bool
open import Data.List
open import Data.List.All
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global
open import Channel

mutual
-- a value indexed by a *relevant* session context, which is "used up" by the value
  data Val (G : SCtx) : Type → Set where
    VUnit : (inaG : Inactive G)
      → Val G TUnit
    VInt  : (i : ℕ)
      → (inaG : Inactive G)
      → Val G TInt
    VPair : ∀ {t₁ t₂ G₁ G₂}
      → (ss-GG₁G₂ : SSplit G G₁ G₂)
      → (v₁ : Val G₁ t₁)
      → (v₂ : Val G₂ t₂)
      → Val G (TPair t₁ t₂)
    VChan : ∀ {s}
      → (ce : ChannelEnd)
      → (cr : ChannelRef G ce s)
      → Val G (TChan s)
    VFun : ∀ {φ lu t₁ t₂}
      → (lu ≡ LL ⊎ All Unr φ)
      → (ϱ : VEnv G φ)
      → (e : Expr (t₁ ∷ φ) t₂)
      → Val G (TFun lu t₁ t₂)

  -- type environment-indexed value environment
  -- session context G describes the entire environment, it splits over all (channel) values
  data VEnv (G : SCtx) : TCtx → Set where
    vnil : (ina : Inactive G) → VEnv G []
    vcons : ∀{t φ G₁ G₂} → (ssp : SSplit G G₁ G₂) → (v : Val G₁ t) → (ϱ : VEnv G₂ φ) → VEnv G (t ∷ φ)

unrestricted-val :  ∀ {t G} → Unr t → Val G t → Inactive G
unrestricted-venv : ∀ {φ G} → All Unr φ → VEnv G φ → Inactive G

unrestricted-val UUnit (VUnit x) = x
unrestricted-val UInt (VInt i x) = x
unrestricted-val (UPair unrt unrt₁) (VPair x v v₁) =
  ssplit-inactive x (unrestricted-val unrt v) (unrestricted-val unrt₁ v₁)
unrestricted-val {TFun UU t₁ t₂} UFun (VFun (inj₁ ()) ϱ e)
unrestricted-val {TFun UU t₁ t₂} UFun (VFun (inj₂ unr-φ) ϱ e) = unrestricted-venv unr-φ ϱ 

unrestricted-venv unr-φ (vnil ina) = ina
unrestricted-venv (px ∷ unr-φ) (vcons ssp v ϱ) =
  ssplit-inactive ssp (unrestricted-val px v) (unrestricted-venv unr-φ ϱ)

-- access a value in an indexed environment
access : ∀ {φ t} {G : SCtx} → VEnv G φ → t ∈ φ → ∃ λ G₁ → ∃ λ G₂ → Inactive G₂ × SSplit G G₁ G₂ × Val G₁ t
access (vcons ssp v ϱ) (here allUnr) =  _ , _ , unrestricted-venv allUnr ϱ , ssp , v
access (vcons ssp x₀ ϱ) (there unrX₀ x) with access ϱ x
access (vcons ssp x₀ ϱ) (there unrX₀ x) | G₁ , G₂ , inaG₂ , ssp12 , v with ssplit-compose4 ssp ssp12
... | Gi , ssp1 , ssp2 = G₁ , Gi , ssplit-inactive ssp2 (unrestricted-val unrX₀ x₀) inaG₂ , ssp1 , v

-- coerce a value to a supertype
coerce : ∀ {G t t'} → Val G t → SubT t t' → Val G t'
coerce (VUnit inaG) sub-unit = VUnit inaG
coerce (VInt i inaG) sub-int = VInt i inaG
coerce (VPair ss-GG₁G₂ v v₁) (sub-pair t≤t' t≤t'') = VPair ss-GG₁G₂ (coerce v t≤t') (coerce v₁ t≤t'')
coerce (VChan b vcr) (sub-chan s≲s') = VChan b (vcr-coerce vcr s≲s')
coerce (VFun lu ϱ e) (sub-fun t≤t' t≤t'') = VFun lu ϱ (expr-coerce e t≤t'' t≤t')

rewrite-ssplit : ∀ {G G' G₁ G₂} → G ≡ G' → SSplit G G₁ G₂ → SSplit G' G₁ G₂
rewrite-ssplit p ssp rewrite p = ssp

rewrite-ssplit1 : ∀ {G G₁ G₁' G₂} → G₁ ≡ G₁' → SSplit G G₁ G₂ → SSplit G G₁' G₂
rewrite-ssplit1 p ssp rewrite p = ssp

-- split environment according to type context split
split-env : ∀ {Φ Φ₁ Φ₂} {G : SCtx}
  → Split Φ Φ₁ Φ₂
  → VEnv G Φ
  → Σ (SCtx × SCtx) λ { (G₁ , G₂) → SSplit G G₁ G₂ × VEnv G₁ Φ₁ × VEnv G₂ Φ₂ }
split-env{G = G} [] (vnil ina) =  (G , G) , inactive-ssplit-trivial ina , vnil ina , vnil ina
split-env (dupl unrt sp) (vcons ssp v ϱ) with split-env sp ϱ | unrestricted-val unrt v
split-env (dupl unrt sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' | unr-v rewrite inactive-left-ssplit ssp unr-v with ssplit-compose4 ssp ssp12 | ssplit-compose3 ssp ssp12
... | Gi , ssp-GG1Gi , ssp-GiG1G2' | Gi-1 , ssp-GGiG2' , ssp-GiG1G1' =
  let p₁ = (inactive-left-ssplit ssp-GiG1G1' unr-v) in
  let p₂ = (inactive-left-ssplit ssp-GiG1G2' unr-v) in
  (G₁' , G₂') ,  ssp12 , vcons (rewrite-ssplit p₁ ssp-GiG1G1') v ϱ₁' , vcons (rewrite-ssplit p₂ ssp-GiG1G2') v ϱ₂' 
split-env (drop px sp) (vcons ssp v ϱ) 
  rewrite inactive-left-ssplit ssp (unrestricted-val px v)
  = split-env sp ϱ
split-env (left sp) (vcons ssp v ϱ) with split-env sp ϱ
split-env{G = G} (left sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' with ssplit-compose3 ssp ssp12
... | Gi , ssp-GiG2' , ssp-GiG1G1' = (Gi , G₂') , ssp-GiG2' , vcons ssp-GiG1G1' v ϱ₁' , ϱ₂'
split-env (rght sp) (vcons ssp v ϱ) with split-env sp ϱ
split-env (rght sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' with ssplit-compose4 ssp ssp12
...| Gi , ssp-GG1'Gi , ssp-GiG1G2' = (G₁' , Gi) , ssp-GG1'Gi , ϱ₁' , vcons ssp-GiG1G2' v ϱ₂' 

