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
open import Syntax
open import Global
open import Channel

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
unrestricted-val UFun _ = {!!}

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
    Send : ∀ {φ G₁ G₂ G₁₁ G₁₂ t s}
      → (ss : SSplit G G₁ G₂)
      → (ss-args : SSplit G₁ G₁₁ G₁₂)
      → (vch : Val G₁₁ (TChan (SSend t s)))
      → (v : Val G₁₂ t)
      → (κ : Cont G₂ φ (TChan s))
      → Command G
    Recv : ∀ {φ G₁ G₂ t s}
      → (ss : SSplit G G₁ G₂)
      → (vch : Val G₁ (TChan (SRecv t s)))
      → (κ : Cont G₂ φ (TPair (TChan s) t))
      → Command G
    Select : ∀ {φ G₁ G₂ s₁ s₂}
      → (ss : SSplit G G₁ G₂)
      → (lab : Selector)
      → (vch : Val G₁ (TChan (SIntern s₁ s₂)))
      → (κ : Cont G₂ φ (TChan (selection lab s₁ s₂)))
      → Command G
    Branch : ∀ {φ G₁ G₂ s₁ s₂}
      → (ss : SSplit G G₁ G₂)
      → (vch : Val G₁ (TChan (SExtern s₁ s₂)))
      → (dcont : (lab : Selector) → Cont G₂ φ (TChan (selection lab s₁ s₂)))
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
run f tsp ssp (send sp ch vv) ϱ κ with split-env sp ϱ
... | (G₁ , G₂) , ss-gg , ϱ₁ , ϱ₂ with access ϱ₁ ch
... | G₃ , G₄ , ina-G₄ , ss-g1g3g4 , vch with access ϱ₂ vv
... | G₅ , G₆ , ina-G₆ , ss-g2g5g6 , vvv with ssplit-join ss-gg ss-g1g3g4 ss-g2g5g6
... | G₁' , G₂' , ss-g1'g2' , ss-g3g5 , ss-g4g6 rewrite sym (inactive-right-ssplit ss-g1g3g4 ina-G₄) | sym (inactive-right-ssplit ss-g2g5g6 ina-G₆) = Send ssp ss-gg vch vvv κ
run f tsp ssp (recv ch) ϱ κ with access ϱ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch rewrite inactive-right-ssplit ss-vi ina-G₂ = Recv ssp vch κ
run f tsp ssp (select lab ch) ϱ κ with access ϱ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch rewrite inactive-right-ssplit ss-vi ina-G₂ = Select ssp lab vch κ
run f tsp ssp (branch{s₁}{s₂} sp ch e-left e-rght) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ with access ϱ₁ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch with ssplit-compose _ _ _ _ _ ssp ss-G1G1'G2'
... | Gi , ss-G-G1'Gi , ss-Gi-G2'-G2 with split-rotate tsp sp
... | φ' , sp-φφ1φ' , sp-φ'φ3φ4 with inactive-right-ssplit ss-vi ina-G₂
... | refl = Branch ss-G-G1'Gi vch dcont
  where
    dcont : (lab : Selector) → Cont Gi _ (TChan (selection lab s₁ s₂))
    dcont Left = bind sp-φ'φ3φ4 ss-Gi-G2'-G2 e-left ϱ₂ κ
    dcont Right = bind sp-φ'φ3φ4 ss-Gi-G2'-G2 e-rght ϱ₂ κ
run f tsp ssp (ulambda sp unr-φ ebody) ϱ κ = {!!}
run f tsp ssp (llambda sp unr-φ₂ ebody) ϱ κ = {!!}
run f tsp ssp (app sp efun earg) ϱ κ = {!!}

apply-cont f ssp (halt-cont un-φ un-t ϱ) v with unrestricted-venv un-φ ϱ | unrestricted-val un-t v
... | inG1 | inG2 = Halt (ssplit-inactive ssp inG2 inG1)
apply-cont (More f) ssp (bind ts ss e₂ ϱ₂ κ) v with ssplit-compose3 _ _ _ _ _ ssp ss
... | Gi , ss-GGiG4 , ss-GiG1G3 =
  run f (left ts) ss-GGiG4 e₂ (vcons ss-GiG1G3 v ϱ₂) κ
apply-cont Empty ssp (bind ts ss e₂ ϱ₂ κ) v =
  Stopped ssp v (bind ts ss e₂ ϱ₂ κ)

extract-inactive-from-cont : ∀ {G t φ} → Unr t → Cont G φ t → Σ SCtx λ G' → Inactive G' × SSplit G G' G
extract-inactive-from-cont{G} un-t κ = ssplit-refl-right-inactive G

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
lift-command (Send ss ss-args vch v κ) = Send (ss-both ss) (ss-both ss-args) (lift-val vch) (lift-val v) (lift-cont κ)
lift-command (Recv ss vch κ) = Recv (ss-both ss) (lift-val vch) (lift-cont κ)
lift-command (Select ss lab vch κ) = Select (ss-both ss) lab (lift-val vch) (lift-cont κ)
lift-command (Branch ss vch dcont) = Branch (ss-both ss) (lift-val vch) λ lab → lift-cont (dcont lab)
-- threads
data ThreadPool (G : SCtx) : Set where
  tnil : (ina : Inactive G) → ThreadPool G
  tcons : ∀ {G₁ G₂} → (ss : SSplit G G₁ G₂) → (cmd : Command G₁) → (tp : ThreadPool G₂) → ThreadPool G

-- tack a task to the end of a thread pool to implement round robin scheduling
tsnoc : ∀ {G Gpool Gcmd} → SSplit G Gcmd Gpool → ThreadPool Gpool → Command Gcmd → ThreadPool G
tsnoc ss (tnil ina) cmd = tcons ss cmd (tnil ina)
tsnoc ss (tcons ss₁ cmd₁ tp) cmd with ssplit-compose2 _ _ _ _ _ ss ss₁
... | Gi , ss-top , ss-rec = tcons (ssplit-sym ss-top) cmd₁ (tsnoc ss-rec tp cmd)

-- append thread pools
tappend : ∀ {G G1 G2} → SSplit G G1 G2 → ThreadPool G1 → ThreadPool G2 → ThreadPool G
tappend ss-top (tnil ina) tp2 rewrite inactive-left-ssplit ss-top ina = tp2
tappend ss-top (tcons ss cmd tp1) tp2 with ssplit-compose _ _ _ _ _ ss-top ss
... | Gi , ss-top' , ss-rec = tcons ss-top' cmd (tappend ss-rec tp1 tp2)

-- apply the inactive extension to a thread pool
lift-threadpool : ∀ {G} → ThreadPool G → ThreadPool (nothing ∷ G)
lift-threadpool (tnil ina) = tnil (::-inactive _ ina)
lift-threadpool (tcons ss cmd tp) = tcons (ss-both ss) (lift-command cmd) (lift-threadpool tp)

matchWaitAndGo : ∀ {G Gc Gc₁ Gc₂ Gtp Gtpwl Gtpacc φ}
  → SSplit G Gc Gtp
  -- close command
  → SSplit Gc Gc₁ Gc₂ × Val Gc₁ (TChan SEnd!) × Cont Gc₂ φ TUnit
  -- focused thread pool
  → SSplit Gtp Gtpwl Gtpacc → ThreadPool Gtpwl → ThreadPool Gtpacc
  → Maybe (Σ SCtx λ G' → ThreadPool G')
matchWaitAndGo ss-top cl-info ss-tp  (tnil ina) tp-acc = nothing
matchWaitAndGo ss-top cl-info ss-tp  (tcons ss (Fork ss₁ κ₁ κ₂) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (Fork ss₁ κ₁ κ₂) tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss (Stopped ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (Stopped ss₁ v κ) tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss (Halt x) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (Halt x) tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss (New s κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (New s κ) tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(Select ss-args lab vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(Branch _ _ _) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(Send _ ss-args vch v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(Recv _ vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss (Close ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (Close ss₁ v κ) tp-acc)
matchWaitAndGo ss-top (ss-cl , VChan cl-b cl-vcr , cl-κ) ss-tp (tcons ss (Wait ss₁ (VChan w-b w-vcr) κ) tp-wl) tp-acc with ssplit-compose6 ss ss₁
... | Gi , ss-g3gi , ss-g4g2 with ssplit-compose6 ss-tp ss-g3gi
... | Gi' , ss-g3gi' , ss-gtpacc with ssplit-join ss-top ss-cl ss-g3gi'
... | Gchannels , Gother , ss-top' , ss-channels , ss-others with vcr-match ss-channels cl-vcr w-vcr
matchWaitAndGo ss-top (ss-cl , VChan cl-b cl-vcr , cl-κ) ss-tp (tcons ss (Wait ss₁ (VChan w-b w-vcr) κ) tp-wl) tp-acc | Gi , ss-g3gi , ss-g4g2 | Gi' , ss-g3gi' , ss-gtpacc | Gchannels , Gother , ss-top' , ss-channels , ss-others | nothing with ssplit-compose5 ss-tp ss
... | _ , ss-tp' , ss' = matchWaitAndGo ss-top (ss-cl , VChan cl-b cl-vcr , cl-κ) ss-tp' tp-wl (tcons ss' (Wait ss₁ (VChan w-b w-vcr) κ) tp-acc)
matchWaitAndGo{Gc₂ = Gc₂} ss-top (ss-cl , VChan cl-b cl-vcr , cl-κ) ss-tp (tcons ss (Wait ss₁ (VChan w-b w-vcr) κ) tp-wl) tp-acc | Gi , ss-g3gi , ss-g4g2 | Gi' , ss-g3gi' , ss-gtpacc | Gchannels , Gother , ss-top' , ss-channels , ss-others | just x with ssplit-refl-right-inactive Gc₂
... | Gunit , ina-Gunit , ss-stopped with extract-inactive-from-cont UUnit κ
... | Gunit' , ina-Gunit' , ss-stopped' with ssplit-compose _ _ _ _ _ ss-gtpacc (ssplit-sym ss-g4g2)
... | Gi'' , ss-int , ss-g2gacc with ssplit-compose2 _ _ _ _ _ ss-others ss-int
... | Gi''' , ss-other , ss-outer-cons = just (Gother , tappend (ssplit-sym ss-other) tp-wl (tcons ss-outer-cons (Stopped ss-stopped (VUnit ina-Gunit) cl-κ) (tcons ss-g2gacc (Stopped ss-stopped' (VUnit ina-Gunit') κ) tp-acc)))

matchSendAndGo : ∀ {G Gc Gc₁ Gc₂ Gtp Gtpwl Gtpacc φ t s}
  → SSplit G Gc Gtp
  -- read command
  → SSplit Gc Gc₁ Gc₂ × Val Gc₁ (TChan (SRecv t s)) × Cont Gc₂ φ (TPair (TChan s) t)
  -- focused thread pool
  → SSplit Gtp Gtpwl Gtpacc → ThreadPool Gtpwl → ThreadPool Gtpacc
  → Maybe (Σ SCtx λ G' → ThreadPool G')
matchSendAndGo ss-top recv-info ss-tp (tnil ina) tp-acc = nothing
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Fork ss₁ κ₁ κ₂) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Stopped ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Halt x) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(New s κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Select ss-arg lab vch κ) tp-wl)  tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Branch _ _ _) tp-wl)  tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Close ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Wait ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Recv ss₁ vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info@(ss-rv , VChan b₁ vcr₁ , κ-rv) ss-tp (tcons ss cmd@(Send ss₁ ss-args (VChan b vcr) v κ) tp-wl) tp-acc with ssplit-compose6 ss₁ ss-args
... | Gi , ss-g1g11gi , ss-gig12g3 with ssplit-compose6 ss ss-g1g11gi
... | Gi' , ss-gtpwlg11g2 , ss-gi'gig2 with ssplit-compose6 ss-tp ss-gtpwlg11g2
... | Gi'' , ss-gtpg11gi'' , ss-gi''gi'gtpacc with ssplit-join ss-top ss-rv ss-gtpg11gi''
... | G₁' , G₂' , ss-gg1'g2' , ss-g1'gc1g11 , ss-g2'gc2gi'' with vcr-match-2-sr (ssplit2 ss-gg1'g2' ss-g1'gc1g11) vcr₁ vcr
... | just (refl {-t1≡t-} , ds1≡s , GG , GG1 , GG11 , G12 , ssplit2 ss-out1 ss-out2 , vcr-recv , vcr-send) with ssplit-compose _ _ _ _ _ ss-gi''gi'gtpacc ss-gi'gig2
... | GSi , ss-Gi''GiGi1 , ss-Gi1G2Gtpacc with ssplit-join ss-out1 ss-out2 ss-g2'gc2gi''
... | GG1' , GG2' , ss-GG-GG1'-GG2' , ss-GG1'-GG11-Gc2 , ss-GG2'-G12-Gi'' with ssplit-rotate ss-GG2'-G12-Gi'' ss-Gi''GiGi1 ss-gig12g3
... | Gi''+ , Gi+ , ss-GG2-G12-Gi''+ , ss-Gi''+Gi+Gsi , ss-Gi+-G12-G4 with ssplit-join ss-GG-GG1'-GG2' ss-GG1'-GG11-Gc2 ss-GG2-G12-Gi''+
... | GG1'' , GG2'' , ss-GG-GG1''-GG2'' , ss-GG1''-GG11-G12 , ss-GG2''-Gc2-Gi''+ with ssplit-compose3 _ _ _ _ _ ss-GG-GG1''-GG2'' ss-GG2''-Gc2-Gi''+
... | _ , ss-GG-Gii-Gi''+ , ss-Gii-GG1''-Gc2 = just (GG ,  (tcons ss-GG-Gii-Gi''+ (Stopped ss-Gii-GG1''-Gc2 (VPair ss-GG1''-GG11-G12 (VChan b₁ vcr-recv) v) κ-rv) (tcons ss-Gi''+Gi+Gsi (Stopped ss-Gi+-G12-G4 (VChan b vcr-send) κ) (tappend ss-Gi1G2Gtpacc tp-wl tp-acc))))
matchSendAndGo ss-top recv-info@(ss-rv , VChan b₁ vcr₁ , κ-rv) ss-tp (tcons ss cmd@(Send ss₁ ss-args (VChan b vcr) v κ) tp-wl) tp-acc | Gi , ss-g1g11gi , ss-gig12g3 | Gi' , ss-gtpwlg11g2 , ss-gi'gig2 | Gi'' , ss-gtpg11gi'' , ss-gi''gi'gtpacc | G₁' , G₂' , ss-gg1'g2' , ss-g1'gc1g11 , ss-g2'gc2gi'' | nothing with ssplit-compose5 ss-tp ss
... | Gi0 , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)

matchBranchAndGo : ∀ {G Gc Gc₁ Gc₂ Gtp Gtpwl Gtpacc φ s₁ s₂}
  → SSplit G Gc Gtp
  -- select command
  → (SSplit Gc Gc₁ Gc₂ × Σ Selector λ lab → Val Gc₁ (TChan (SIntern s₁ s₂)) × Cont Gc₂ φ (TChan (selection lab s₁ s₂)))
  -- focused thread pool
  → SSplit Gtp Gtpwl Gtpacc → ThreadPool Gtpwl → ThreadPool Gtpacc
  → Maybe (Σ SCtx λ G' → ThreadPool G')
matchBranchAndGo ss-top select-info ss-tp (tnil ina) tp-acc = nothing
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Fork ss₁ κ₁ κ₂) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Stopped ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Halt x) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(New s κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Close ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Wait ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Send ss₁ ss-args vch v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Recv ss₁ vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Select ss₁ lab vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top (ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss (Branch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc with ssplit-compose6 ss ss₁
... | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 with ssplit-compose6 ss-tp ss-gtpwl-g3-gi
... | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc with ssplit-join ss-top ss-vκ ss-gtp-g3-gi1
... | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 with vcr-match-2-sb (ssplit2 ss-g-gc'-gtp' ss-gc'-gc1-g1) vcr₁ vcr lab
matchBranchAndGo ss-top select-info@(ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss cmd@(Branch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 | nothing with ssplit-compose5 ss-tp ss
... | Gix , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top (ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss (Branch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 | just (ds3=s1 , ds4=s2 , GG , GG1 , GG11 , GG12 , ssplit2 ss1' ss2'  , vcr-sel , vcr-bra) with ssplit-compose _ _ _ _ _ ss-gi1-gi-gtpacc ss-gi-g4-g2
... | Gi2 , ss-gi1-g3-gi2 , ss-gi2-g2-gtpacc with ssplit-join ss1' ss2' ss-gtp'-gc2-gi1
... | GGG1 , GGG2 , ss-GG-ggg1-ggg2 , ss-ggg1-gc1-gc2 , ss-ggg2-g1-gi1 with ssplit-compose3 _ _ _ _ _ ss-ggg2-g1-gi1 ss-gi1-g3-gi2
... | Gi3 , ss-ggg2-gi3-gi2 , ss-gi3-gg12-g2 = just (GG , tcons ss-GG-ggg1-ggg2 (Stopped ss-ggg1-gc1-gc2 (VChan b₁ vcr-sel) κ) (tcons ss-ggg2-gi3-gi2 (Stopped ss-gi3-gg12-g2 (VChan b vcr-bra) (dcont lab)) (tappend ss-gi2-g2-gtpacc tp-wl tp-acc)))

data Outcome : Set where
  Terminated : Outcome
  OutOfFuel : ∀ {G} → ThreadPool G → Outcome

-- thread scheduling
schedule : Fuel → (G : SCtx) → ThreadPool G → Outcome
schedule f G (tnil ina) = Terminated
schedule (More f) G (tcons ss (Fork{G₁ = G₁}{G₂ = G₂} ss₁ κ₁ κ₂) tp) with ssplit-compose _ _ _ _ _ ss ss₁
... | Gi , ss₁₃ , ss₂₄ with ssplit-refl-right G₁ | ssplit-refl-right G₂
... | Gunit , ss-G1GunitG1 | G2unit , ss-G2GuG2 =
  schedule f G
    (tcons ss₁₃ (apply-cont f ss-G1GunitG1 κ₁ (VUnit (ssplit-inactive-right ss-G1GunitG1)))
    (tcons ss₂₄ (apply-cont f ss-G2GuG2 κ₂ (VUnit (ssplit-inactive-right ss-G2GuG2))) tp))
schedule (More f) G (tcons ss (Stopped ss₁ v κ) tp) =
  schedule f G (tsnoc ss tp (apply-cont f ss₁ κ v))
schedule (More f) G (tcons ss (Halt inaG) tp) with tp | inactive-left-ssplit ss inaG
schedule (More f) G (tcons ss (Halt inaG) tp) | tp' | refl = schedule f G tp'
schedule (More f) G (tcons{G₁} ss (New s κ) tp) with ssplit-refl-right G₁
... | Gi , ss-GiG1 with ssplit-inactive-right ss-GiG1
... | ina-Gi =
  schedule f (just (s , POSNEG) ∷ G)
    (tcons (ss-left ss)
           (apply-cont f (ss-left ss-GiG1) (lift-cont κ) (VPair (ss-posneg (inactive-ssplit-trivial ina-Gi)) (VChan true (here-pos ina-Gi)) (VChan false (here-neg ina-Gi))))
           (lift-threadpool tp))
schedule (More f) G (tcons{G₁}{G₂} ss (Close ss-vκ v κ) tp) with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' with matchWaitAndGo ss (ss-vκ , v , κ) ss-GG' tp (tnil ina-G')
schedule (More f) G (tcons {G₁} {G₂} ss (Close ss-vκ v κ) tp) | G' , ina-G' , ss-GG' | just (Gnext , tpnext) = schedule f Gnext tpnext
schedule (More f) G (tcons {G₁} {G₂} ss cmd@(Close ss-vκ v κ) tp) | G' , ina-G' , ss-GG' | nothing = schedule f G (tsnoc ss tp cmd)
schedule (More f) G (tcons ss cmd@(Wait ss-vκ v κ) tp) = schedule f G (tsnoc ss tp cmd)
schedule (More f) G (tcons ss cmd@(Send _ _ _ _ _) tp) = schedule f G (tsnoc ss tp cmd)
schedule (More f) G (tcons{G₁}{G₂} ss cmd@(Recv ss-vκ v κ) tp) with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' with matchSendAndGo ss (ss-vκ , v , κ) ss-GG' tp (tnil ina-G')
schedule (More f) G (tcons {G₁} {G₂} ss (Recv ss-vκ v κ) tp) | G' , ina-G' , ss-GG' | just (G-next , tp-next) = schedule f G-next tp-next
schedule (More f) G (tcons {G₁} {G₂} ss cmd@(Recv ss-vκ v κ) tp) | G' , ina-G' , ss-GG' | nothing = schedule f G (tsnoc ss tp cmd)
schedule (More f) G (tcons {G₁} {G₂} ss cmd@(Select ss-vκ lab vch κ) tp) with ssplit-refl-left-inactive G₂
... | G' , ina-G' , ss-GG' with matchBranchAndGo ss (ss-vκ , lab , vch , κ) ss-GG' tp (tnil ina-G')
schedule (More f) G (tcons {G₁} {G₂} ss (Select ss-vκ lab vch κ) tp) | G' , ina-G' , ss-GG' | just (G-next , tp-next) = schedule f G-next tp-next
schedule (More f) G (tcons {G₁} {G₂} ss cmd@(Select ss-vκ lab vch κ) tp) | G' , ina-G' , ss-GG' | nothing = schedule f G (tsnoc ss tp cmd)
schedule (More f) G (tcons ss cmd@(Branch ss-vκ vch dcont) tp) = schedule f G (tsnoc ss tp cmd)
schedule Empty G tp@(tcons _ _ _) = OutOfFuel tp

-- start main thread
start : Fuel → Expr [] TUnit → Outcome
start f e =
  schedule f [] (tcons ss-[] (run f [] ss-[] e (vnil []-inactive) (halt-cont [] UUnit (vnil []-inactive))) (tnil []-inactive))
