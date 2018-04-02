module EssentialSession7 where

open import Data.Bool
open import Data.Empty
-- open import Data.Fin hiding (_+_ ; _≤_)
open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Maybe hiding (All)
open import Data.Nat
open import Data.Product
open import Data.Unit hiding (_≤_)
-- open import Data.Vec hiding ( _∈_ ; _>>=_)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing

open import Global

-- expressions
data Expr : (φ : TCtx) → Ty → Set where
  var : ∀ {t φ}
      → (x : t ∈ φ)
      → Expr φ t

  nat : ∀ {φ}
      → (unr-φ : All Unr φ)
      → (i : ℕ)
      → Expr φ TInt

  letbind : ∀ {φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (e₁ : Expr φ₁ t₁)
    → (e₂ : Expr (t₁ ∷ φ₂) t₂)
    → Expr φ t₂

  pair : ∀ {φ φ₁ φ₂ t₁ t₂}
    → (sp : Split φ φ₁ φ₂)
    → (x₁ : t₁ ∈ φ₁)
    → (x₂ : t₂ ∈ φ₂)
    → Expr φ (TPair t₁ t₂)

  letpair : ∀ {φ φ₁ φ₂ t₁ t₂ t}
    → (sp : Split φ φ₁ φ₂)
    → (p : TPair t₁ t₂ ∈ φ₁)
    → (e : Expr (t₁ ∷ t₂ ∷ φ₂) t)
    → Expr φ t

  fork : ∀ { φ}
    → (e : Expr φ TUnit)
    → Expr φ TUnit

  new : ∀ {φ}
      → (unr-φ : All Unr φ)
      → (s : STy)
      → Expr φ (TPair (TChan s) (TChan (dual s)))
{-
  -- takes only variables to avoid extraneous effects
  send : ∀ {φ φ₁ φ₂ s t}
      → (sp : Split φ φ₁ φ₂)
      → (ch : (TChan (SSend t s)) ∈ φ₁)
      → (vv : t ∈ φ₂)
      → Expr φ (TChan s)
  -- takes only variables to avoid extraneous effects
  recv : ∀ {φ s t}
      → (ch : (TChan (SRecv t s)) ∈ φ)
      → Expr φ (TPair (TChan s) t)
-}
  close : ∀ { φ}
      → (ch : TChan SEnd! ∈ φ)
      → Expr φ TUnit

  wait : ∀ { φ}
      → (ch : TChan SEnd? ∈ φ)
      → Expr φ TUnit

lift-expr : ∀ {φ t tᵤ} → Unr tᵤ → Expr φ t → Expr (tᵤ ∷ φ) t
lift-expr unrtu (var x) = var (there unrtu x)
lift-expr unrtu (nat unr-φ i) = nat (unrtu ∷ unr-φ) i
lift-expr unrtu (letbind sp e e₁) = letbind (left sp) (lift-expr unrtu e) e₁
lift-expr unrtu (pair sp x₁ x₂) = pair (rght sp) x₁ (there unrtu x₂)
lift-expr unrtu (letpair sp p e) = letpair (left sp) (there unrtu p) e
lift-expr unrtu (fork e) = lift-expr unrtu e
lift-expr unrtu (new unr-φ s) = new (unrtu ∷ unr-φ) s
lift-expr unrtu (close ch) = close (there unrtu ch)
lift-expr unrtu (wait ch) = wait (there unrtu ch)

-- the main part of a channel endpoint value is a valid channel reference
-- the boolean determines whether it's the front end or the back end of the channel
-- enforces that the session context has only one channel
data ValidChannelRef : (G : SCtx) (b : Bool) (s : STy) → Set where
  here-pos : ∀ {s} {G : SCtx}
    → (ina-G : Inactive G)
    → ValidChannelRef (just (s , POS) ∷ G) true s
  here-neg : ∀ {s} {G : SCtx}
    → (ina-G : Inactive G)
    → ValidChannelRef (just (s , NEG) ∷ G) false (dual s)
  there : ∀ {b s} {G : SCtx}
    → (vcr : ValidChannelRef G b s)
    → ValidChannelRef (nothing ∷ G) b s

-- a value indexed by a *relevant* session context, which is "used up" by the value
data Val (G : SCtx) : Ty → Set where
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
    → (b : Bool)
    → (vcr : ValidChannelRef G b s)
    → Val G (TChan s)

unrestricted-val :  ∀ {t G} → Unr t → Val G t → Inactive G
unrestricted-val UUnit (VUnit x) = x
unrestricted-val UInt (VInt i x) = x
unrestricted-val (UPair unrt unrt₁) (VPair x v v₁) =
  ssplit-inactive x (unrestricted-val unrt v) (unrestricted-val unrt₁ v₁)

-- type environment-indexed value environment
-- session context G describes the entire environment, it splits over all (channel) values
data VEnv (G : SCtx) : TCtx → Set where
  vnil : (ina : Inactive G) → VEnv G []
  vcons : ∀{t φ G₁ G₂} → (ssp : SSplit G G₁ G₂) → (v : Val G₁ t) → (ϱ : VEnv G₂ φ) → VEnv G (t ∷ φ)

unrestricted-venv : ∀ {φ G} → All Unr φ → VEnv G φ → Inactive G
unrestricted-venv unr-φ (vnil ina) = ina
unrestricted-venv (px ∷ unr-φ) (vcons ssp v ϱ) =
  ssplit-inactive ssp (unrestricted-val px v) (unrestricted-venv unr-φ ϱ)

-- access a value in an indexed environment
access : ∀ {φ t} {G : SCtx} → VEnv G φ → t ∈ φ → Σ SCtx λ G₁ → Σ SCtx λ G₂ → Inactive G₂ × SSplit G G₁ G₂ × Val G₁ t
access (vcons ssp v ϱ) (here allUnr) =  _ , _ , unrestricted-venv allUnr ϱ , ssp , v
access (vcons ssp x₀ ϱ) (there unrX₀ x) with access ϱ x
access (vcons ssp x₀ ϱ) (there unrX₀ x) | G₁ , G₂ , inaG₂ , ssp12 , v with ssplit-compose4 _ _ _ _ _ ssp ssp12
... | Gi , ssp1 , ssp2 = G₁ , Gi , ssplit-inactive ssp2 (unrestricted-val unrX₀ x₀) inaG₂ , ssp1 , v

-- non-empty list of value environments for use in a continuation closure
data CLEnv (G : SCtx) : List TCtx → Set where
  clnil : Inactive G → CLEnv G []
  clcons : ∀ {G₁ G₂ φ φ*}
    → (ssp : SSplit G G₁ G₂) (ϱ : VEnv G₁ φ) (ξ : CLEnv G₂ φ*)
    → CLEnv G (φ ∷ φ*)

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
split-env (unr unrt sp) (vcons ssp v ϱ) with split-env sp ϱ | unrestricted-val unrt v
split-env (unr unrt sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' | unr-v rewrite inactive-left-ssplit ssp unr-v with ssplit-compose4 _ _ _ _ _ ssp ssp12 | ssplit-compose3 _ _ _ _ _ ssp ssp12
... | Gi , ssp-GG1Gi , ssp-GiG1G2' | Gi-1 , ssp-GGiG2' , ssp-GiG1G1' =
  let p₁ = (inactive-left-ssplit ssp-GiG1G1' unr-v) in
  let p₂ = (inactive-left-ssplit ssp-GiG1G2' unr-v) in
  (G₁' , G₂') ,  ssp12 , vcons (rewrite-ssplit p₁ ssp-GiG1G1') v ϱ₁' , vcons (rewrite-ssplit p₂ ssp-GiG1G2') v ϱ₂' 
split-env (left sp) (vcons ssp v ϱ) with split-env sp ϱ
split-env{G = G} (left sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' with ssplit-compose3 _ _ _ _ _ ssp ssp12
... | Gi , ssp-GiG2' , ssp-GiG1G1' = (Gi , G₂') , ssp-GiG2' , vcons ssp-GiG1G1' v ϱ₁' , ϱ₂'
split-env (rght sp) (vcons ssp v ϱ) with split-env sp ϱ
split-env (rght sp) (vcons ssp v ϱ) | (G₁' , G₂') , ssp12 , ϱ₁' , ϱ₂' with ssplit-compose4 _ _ _ _ _ ssp ssp12
...| Gi , ssp-GG1'Gi , ssp-GiG1G2' = (G₁' , Gi) , ssp-GG1'Gi , ϱ₁' , vcons ssp-GiG1G2' v ϱ₂' 

data Fuel : Set where
  Empty : Fuel
  More  : Fuel → Fuel

mutual
  data Cont (G : SCtx) (φ : TCtx) (t : Ty) : Set where
    halt-cont :
      (un-φ : All Unr φ)
      → (un-t : Unr t)
      → (ϱ : VEnv G φ)
      → Cont G φ t
  {-
    cont : 
      (ϱ : VEnv G φ)
      → (c : ∀ {G' Gx} → SSplit G' Gx G → Val Gx t → VEnv G φ →  Command G')
      → Cont G φ t
  -}
    bind : ∀ { φ₁ φ₂ G₁ G₂ t₂}
      → (ts : Split φ φ₁ φ₂)
      → (ss : SSplit G G₁ G₂)
      → (e₂ : Expr (t ∷ φ₁) t₂)
      → (ϱ₂ : VEnv G₁ φ₁)
      → (κ₂ : Cont G₂ φ₂ t₂)
      → Cont G φ t

  data Command (G : SCtx) : Set where
{-
    Bind : ∀ {φ φ₁ φ₂ G₁ G₂ t₁ t₂}
      → (ts : Split φ φ₁ φ₂)
      → (ss : SSplit G G₁ G₂)
      → (v : Val G₁ t₁)
      → (e₂ : Expr (t₁ ∷ φ₁) t₂)
      → (ϱ₂ : VEnv G₂ φ₁)
      → (κ₂ : Cont G₂ φ₂ t₂)
      → Command G
-}

    Fork : ∀ {φ₁ φ₂ G₁ G₂}
      → (ss : SSplit G G₁ G₂)
      → (κ₁ : Cont G₁ φ₁ TUnit)
      → (κ₂ : Cont G₂ φ₂ TUnit)
      → Command G

    Stopped : ∀ {φ t G₁ G₂}
      → (ss : SSplit G G₁ G₂)
      → (v : Val G₁ t)
      → (κ : Cont G₂ φ t)
      → Command G

    Halt :
      Inactive G
      → Command G
    New : ∀ {φ}
      → (s : STy)
      → (κ : Cont G φ (TPair (TChan s) (TChan (dual s))))
      → Command G
    Close : ∀ {φ G₁ G₂}
      → (ss : SSplit G G₁ G₂)
      → (v : Val G₁ (TChan SEnd!))
      → (κ : Cont G₂ φ TUnit)
      → Command G
    Wait  : ∀ {φ G₁ G₂}
      → (ss : SSplit G G₁ G₂)
      → (v : Val G₁ (TChan SEnd?))
      → (κ : Cont G₂ φ TUnit)
      → Command G

-- 

rewrite-helper : ∀ {G G1 G2 G'' φ'} → Inactive G2 → SSplit G G1 G2 → SSplit G G G'' → VEnv G2 φ' → VEnv G'' φ'
rewrite-helper ina-G2 ssp-GG1G2 ssp-GGG'' ϱ with inactive-right-ssplit ssp-GG1G2 ina-G2
... | p with rewrite-ssplit1 (sym p) ssp-GG1G2
... | ssp rewrite ssplit-function2 ssp ssp-GGG'' = ϱ

-- apply a continuation
apply-cont : ∀ {G G₁ G₂ t φ} → Fuel → (ssp : SSplit G G₁ G₂) (κ : Cont G₂ φ t) → Val G₁ t → Command G

run : ∀ {φ φ₁ φ₂ t G G₁ G₂}
  → Fuel
  → Split φ φ₁ φ₂
  → SSplit G G₁ G₂
  → Expr φ₁ t
  → VEnv G₁ φ₁
  → Cont G₂ φ₂ t
  → Command G
run{G = G}{G₁ = G₁}{G₂ = G₂} f tsp ssp (var x) ϱ κ with access ϱ x
... | Gx , Gϱ , ina , ssp12 , v rewrite inactive-right-ssplit ssp12 ina = apply-cont f ssp κ v
run f tsp ssp (nat unr-φ i) ϱ κ =
  apply-cont f ssp κ (VInt i (unrestricted-venv unr-φ ϱ))
run{φ}{φ₁}{φ₂} f tsp ssp (letbind{.φ₁}{φ₁₁}{φ₁₂}{t₁}{t₂} sp e₁ e₂) ϱ κ₂ with split-env sp ϱ | split-rotate tsp sp
... | (G₁ , G₂) , ssp-G1G2 , ϱ₁ , ϱ₂ | φ' , tsp-φ' , φ'-tsp with ssplit-compose _ _ _ _ _ ssp ssp-G1G2
... | Gi , ssp-3i , ssp-42 =
  run f tsp-φ' ssp-3i e₁ ϱ₁
  (bind φ'-tsp ssp-42 e₂ ϱ₂ κ₂)
run f tsp ssp (pair sp x₁ x₂) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ with access ϱ₁ x₁ | access ϱ₂ x₂
... | Gv₁ , Gr₁ , ina-Gr₁ , ss-v1r1 , v₁ | Gv₂ , Gr₂ , ina-Gr₂ , ss-v2r2 , v₂ rewrite inactive-right-ssplit ss-v1r1 ina-Gr₁ | inactive-right-ssplit ss-v2r2 ina-Gr₂ =
  apply-cont f ssp κ (VPair ss-G1G1'G2' v₁ v₂)
run f tsp ssp (letpair sp p e) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ with access ϱ₁ p
run f tsp ssp (letpair sp p e) ϱ κ | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ | Gvp , Gr , ina-Gr , ss-vpr , VPair ss-GG₁G₂ v₁ v₂ with split-rotate tsp sp
... | φ' , ts-φφ1φ' , ts-φ'φ3φ4 rewrite inactive-right-ssplit ss-vpr ina-Gr with ssplit-compose _ _ _ _ _ ss-G1G1'G2' ss-GG₁G₂
... | Gi , ss-G3G1Gi , ss-G1G2G2' = run f (left (left ts-φ'φ3φ4)) ssp e (vcons ss-G3G1Gi v₁ (vcons ss-G1G2G2' v₂ ϱ₂)) κ 
run{φ}{φ₁}{G = G}{G₁ = G₁} f tsp ssp (fork e) ϱ κ with ssplit-refl-left G₁ | split-refl-left φ₁
... | Gi , ss-g1g1g2 | φ' , unr-φ' , sp-φφφ' with split-env sp-φφφ' ϱ
... | (Gp1 , Gp2) , ss-Gp , ϱ₁ , ϱ₂ with unrestricted-venv unr-φ' ϱ₂
... | ina-Gp2 with inactive-right-ssplit-transform ss-Gp ina-Gp2
... | ss-Gp' rewrite sym (ssplit-function2 ss-g1g1g2 ss-Gp') =
  Fork ssp (bind sp-φφφ' ss-g1g1g2 (lift-expr UUnit e) ϱ (halt-cont unr-φ' UUnit ϱ₂)) κ
run f tsp ssp (new unr-φ s) ϱ κ with unrestricted-venv unr-φ ϱ
... | ina rewrite inactive-left-ssplit ssp ina = New s κ
run f tsp ssp (close ch) ϱ κ with access ϱ ch
... | Gch , Gϱ , ina , ssp12 , vch with vch | inactive-right-ssplit ssp12 ina
run f tsp ssp (close ch) ϱ κ | Gch , Gϱ , ina , ssp12 , vch | vch' | refl = Close ssp vch' κ
run f tsp ssp (wait ch) ϱ κ with access ϱ ch
... | Gch , Gϱ , ina , ssp12 , vch with vch | inactive-right-ssplit ssp12 ina
... | vch' | refl = Wait ssp vch' κ


apply-cont f ssp (halt-cont un-φ un-t ϱ) v with unrestricted-venv un-φ ϱ | unrestricted-val un-t v
... | inG1 | inG2 = Halt (ssplit-inactive ssp inG2 inG1)
apply-cont (More f) ssp (bind ts ss e₂ ϱ₂ κ) v with ssplit-compose3 _ _ _ _ _ ssp ss
... | Gi , ss-GGiG4 , ss-GiG1G3 =
  run f (left ts) ss-GGiG4 e₂ (vcons ss-GiG1G3 v ϱ₂) κ
apply-cont Empty ssp (bind ts ss e₂ ϱ₂ κ) v =
  Stopped {!!} {!!} {!!}


-- lifting through a trivial extension

lift-val : ∀ {G t} → Val G t → Val (nothing ∷ G) t
lift-val (VUnit x) = VUnit (::-inactive _ x)
lift-val (VInt i x) = VInt i (::-inactive _ x)
lift-val (VPair x v v₁) = VPair (ss-both x) (lift-val v) (lift-val v₁)
lift-val (VChan b vcr) = VChan b (there vcr)

lift-venv : ∀ {G φ} → VEnv G φ → VEnv (nothing ∷ G) φ
lift-venv (vnil ina) = vnil (::-inactive _ ina)
lift-venv (vcons ssp v ϱ) = vcons (ss-both ssp) (lift-val v) (lift-venv ϱ)

lift-cont : ∀ {G t φ} → Cont G φ t → Cont (nothing ∷ G) φ t
lift-cont (halt-cont un-φ un-t ϱ) = halt-cont un-φ un-t (lift-venv ϱ)
lift-cont (bind ts ss e₂ ϱ₂ κ) = bind ts (ss-both ss) e₂ (lift-venv ϱ₂) (lift-cont κ)

lift-command : ∀ {G} → Command G → Command (nothing ∷ G)
lift-command (Fork ss κ₁ κ₂) = Fork (ss-both ss) (lift-cont κ₁) (lift-cont κ₂)
lift-command (Stopped ss v κ) = Stopped (ss-both ss) (lift-val v) (lift-cont κ)
lift-command (Halt x) = Halt (::-inactive _ x)
lift-command (New s κ) = New s (lift-cont κ)
lift-command (Close ss v κ) = Close (ss-both ss) (lift-val v) (lift-cont κ)
lift-command (Wait ss v κ) = Wait (ss-both ss) (lift-val v) (lift-cont κ)

-- threads
data ThreadPool (G : SCtx) : Set where
  tnil : (ina : Inactive G) → ThreadPool G
  tcons : ∀ {G₁ G₂} → (ss : SSplit G G₁ G₂) → (cmd : Command G₁) → (tp : ThreadPool G₂) → ThreadPool G

lift-threadpool : ∀ {G} → ThreadPool G → ThreadPool (nothing ∷ G)
lift-threadpool (tnil ina) = tnil (::-inactive _ ina)
lift-threadpool (tcons ss cmd tp) = tcons (ss-both ss) (lift-command cmd) (lift-threadpool tp)

-- find matching wait instruction in threadpool
vcr-match : ∀ {G G₁ G₂ b₁ b₂ s₁ s₂}
  → SSplit G G₁ G₂
  → ValidChannelRef G₁ b₁ s₁
  → ValidChannelRef G₂ b₂ s₂
  → Maybe (b₁ ≡ not b₂ × s₁ ≡ dual s₂)
vcr-match () (here-pos ina-G) (here-pos ina-G₁)
vcr-match (ss-posneg ss) (here-pos ina-G) (here-neg ina-G₁) = just (refl , sym (dual-involution _))
vcr-match (ss-left ss) (here-pos ina-G) (there vcr2) = nothing
vcr-match (ss-negpos ss) (here-neg ina-G) (here-pos ina-G₁) = just (refl , refl)
vcr-match (ss-left ss) (here-neg ina-G) (there vcr2) = nothing
vcr-match (ss-right ss) (there vcr1) (here-pos ina-G) = nothing
vcr-match (ss-right ss) (there vcr1) (here-neg ina-G) = nothing
vcr-match (ss-both ss) (there vcr1) (there vcr2) = vcr-match ss vcr1 vcr2

findMatchingWait : ∀ {G G₁ G₂}
  → SSplit G G₁ G₂
  → Val G₁ (TChan SEnd!)
  → ThreadPool G₂
  → Maybe (Σ SCtx λ G' → Val G' (TChan SEnd?))
findMatchingWait ss v (tnil ina) = nothing
findMatchingWait ss v (tcons ss₁ (Fork ss₂ x x₁) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
findMatchingWait ss v (tcons ss₁ (Fork ss₂ x x₁) tp) | G' , _ , ss' = findMatchingWait ss' v tp
findMatchingWait ss v (tcons ss₁ (Halt _) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
... | G' , _ , ss' = findMatchingWait ss' v tp
findMatchingWait ss v (tcons ss₁ (New s κ) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
... | G' , _ , ss' = findMatchingWait ss' v tp
findMatchingWait ss v (tcons ss₁ (Close ss-c v' κ) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
... | G' , _ , ss' = findMatchingWait ss' v tp
findMatchingWait ss (VChan b vcr) (tcons ss₁ (Wait ss-w (VChan b₁ vcr₁) κ) tp) with b xor b₁ | ssplit-compose2 _ _ _ _ _ ss ss₁
findMatchingWait ss (VChan b vcr) (tcons ss₁ (Wait ss-w (VChan b₁ vcr₁) κ) tp) | false | G' , _ , ss' = findMatchingWait ss' (VChan b vcr) tp
findMatchingWait ss (VChan b vcr) (tcons ss₁ (Wait ss-w (VChan b₁ vcr₁) κ) tp) | true | G' , ss'' , ss' with ssplit-compose3 _ _ _ _ _ ss ss₁
findMatchingWait ss (VChan b vcr) (tcons ss₁ (Wait ss-w (VChan b₁ vcr₁) κ) tp) | true | G' , ss'' , ss' | Gi , ssi4 , ssi13 with vcr-match {!!} vcr vcr₁
... | vcrm = just {!!}
findMatchingWait ss (VChan b vcr) (tcons ss₁ (Stopped _ _ _) tp) with ssplit-compose2 _ _ _ _ _ ss ss₁
... | G' , _ , ss' = findMatchingWait ss' (VChan b vcr) tp

-- thread scheduling
schedule : Fuel → (G : SCtx) → ThreadPool G → ⊤
schedule f G (tnil ina) = tt
schedule (More f) G (tcons ss (Fork{G₁ = G₁}{G₂ = G₂} ss₁ κ₁ κ₂) tp) with ssplit-compose _ _ _ _ _ ss ss₁
... | Gi , ss₁₃ , ss₂₄ with ssplit-refl-right G₁ | ssplit-refl-right G₂
... | Gunit , ss-G1GunitG1 | G2unit , ss-G2GuG2 =
  schedule f G
    (tcons ss₁₃ (apply-cont f ss-G1GunitG1 κ₁ (VUnit (ssplit-inactive-right ss-G1GunitG1)))
    (tcons ss₂₄ (apply-cont f ss-G2GuG2 κ₂ (VUnit (ssplit-inactive-right ss-G2GuG2))) tp))
schedule (More f) G (tcons ss (Stopped ss₁ v κ) tp) = {!!}
schedule (More f) G (tcons ss (Halt inaG) tp) with tp | inactive-left-ssplit ss inaG
schedule (More f) G (tcons ss (Halt inaG) tp) | tp' | refl = schedule f G tp'
schedule (More f) G (tcons{G₁} ss (New s κ) tp) with ssplit-refl-right G₁
... | Gi , ss-GiG1 with ssplit-inactive-right ss-GiG1
... | ina-Gi =
  schedule f (just (s , POSNEG) ∷ G)
    (tcons (ss-left ss)
           (apply-cont f (ss-left ss-GiG1) (lift-cont κ) (VPair (ss-posneg (inactive-ssplit-trivial ina-Gi)) (VChan true (here-pos ina-Gi)) (VChan false (here-neg ina-Gi))))
           (lift-threadpool tp))
schedule (More f) G (tcons ss (Close ss-vκ v κ) tp) = {!!}
schedule (More f) G (tcons ss (Wait ss-vκ v κ) tp) = {!!}
schedule Empty G (tcons _ _ _) = {!!}

-- start main thread
start : Fuel → Expr [] TUnit → ⊤
start f e =
  schedule f [] (tcons ss-[] (run f [] ss-[] e (vnil []-inactive) (halt-cont [] UUnit (vnil []-inactive))) (tnil []-inactive))
