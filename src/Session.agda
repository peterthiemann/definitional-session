module Session where

open import Data.Bool
open import Data.Fin
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (_$_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global
open import Channel
open import Values


data Cont (G : SCtx) (φ : TCtx) : (t : Type) → Set where
  halt : ∀ {t} 
    → Inactive G 
    → (un-t : Unr t)
    → Cont G φ t

  bind : ∀ {φ₁ φ₂ G₁ G₂ t t₂}
    → (ts : Split φ φ₁ φ₂)
    → (ss : SSplit G G₁ G₂)
    → (e₂ : Expr (t ∷ φ₁) t₂)
    → (ϱ₂ : VEnv G₁ φ₁)
    → (κ₂ : Cont G₂ φ₂ t₂)
    → Cont G φ t

  bind-thunk : ∀ {φ₁ φ₂ G₁ G₂ t₂}
    → (ts : Split φ φ₁ φ₂)
    → (ss : SSplit G G₁ G₂)
    → (e₂ : Expr φ₁ t₂)
    → (ϱ₂ : VEnv G₁ φ₁)
    → (κ₂ : Cont G₂ φ₂ t₂)
    → Cont G φ TUnit

  subsume : ∀ {t t₁}
    → SubT t t₁
    → Cont G φ t₁
    → Cont G φ t

data Command (G : SCtx) : Set where

  Fork : ∀ {φ₁ φ₂ G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → (κ₁ : Cont G₁ φ₁ TUnit)
    → (κ₂ : Cont G₂ φ₂ TUnit)
    → Command G

  Ready : ∀ {φ t G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → (v : Val G₁ t)
    → (κ : Cont G₂ φ t)
    → Command G

  Halt : ∀ {t}
    → Inactive G
    → Unr t
    → Val G t
    → Command G
  New : ∀ {φ}
    → (s : SType)
    → (κ : Cont G φ (TPair (TChan (SType.force s)) (TChan (SType.force (dual s)))))
    → Command G
  Close : ∀ {φ G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → (v : Val G₁ (TChan send!))
    → (κ : Cont G₂ φ TUnit)
    → Command G
  Wait  : ∀ {φ G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → (v : Val G₁ (TChan send?))
    → (κ : Cont G₂ φ TUnit)
    → Command G
  Send : ∀ {φ G₁ G₂ G₁₁ G₁₂ t s}
    → (ss : SSplit G G₁ G₂)
    → (ss-args : SSplit G₁ G₁₁ G₁₂)
    → (vch : Val G₁₁ (TChan (Typing.send t s)))
    → (v : Val G₁₂ t)
    → (κ : Cont G₂ φ (TChan (SType.force s)))
    → Command G
  Recv : ∀ {φ G₁ G₂ t s}
    → (ss : SSplit G G₁ G₂)
    → (vch : Val G₁ (TChan (Typing.recv t s)))
    → (κ : Cont G₂ φ (TPair (TChan (SType.force s)) t))
    → Command G
  Select : ∀ {φ G₁ G₂ s₁ s₂}
    → (ss : SSplit G G₁ G₂)
    → (lab : Selector)
    → (vch : Val G₁ (TChan (sintern s₁ s₂)))
    → (κ : Cont G₂ φ (TChan (selection lab (SType.force s₁) (SType.force s₂))))
    → Command G
  Branch : ∀ {φ G₁ G₂ s₁ s₂}
    → (ss : SSplit G G₁ G₂)
    → (vch : Val G₁ (TChan (sextern s₁ s₂)))
    → (dcont : (lab : Selector) → Cont G₂ φ (TChan (selection lab (SType.force s₁) (SType.force s₂))))
    → Command G
  NSelect : ∀ {φ G₁ G₂ m alt}
    → (ss : SSplit G G₁ G₂)
    → (lab : Fin m)
    → (vch : Val G₁ (TChan (sintN m alt)))
    → (κ : Cont G₂ φ (TChan (SType.force (alt lab))))
    → Command G
  NBranch : ∀ {φ G₁ G₂ m alt}
    → (ss : SSplit G G₁ G₂)
    → (vch : Val G₁ (TChan (sextN m alt)))
    → (dcont : (lab : Fin m) → Cont G₂ φ (TChan (SType.force (alt lab))))
    → Command G
      
-- 

rewrite-helper : ∀ {G G1 G2 G'' φ'} → Inactive G2 → SSplit G G1 G2 → SSplit G G G'' → VEnv G2 φ' → VEnv G'' φ'
rewrite-helper ina-G2 ssp-GG1G2 ssp-GGG'' ϱ with inactive-right-ssplit ssp-GG1G2 ina-G2
... | p with rewrite-ssplit1 (sym p) ssp-GG1G2
... | ssp rewrite ssplit-function2 ssp ssp-GGG'' = ϱ

-- interpret an expression
run : ∀ {φ φ₁ φ₂ t G G₁ G₂}
  → Split φ φ₁ φ₂
  → SSplit G G₁ G₂
  → Expr φ₁ t
  → VEnv G₁ φ₁
  → Cont G₂ φ₂ t
  → Command G

run{G = G}{G₁ = G₁}{G₂ = G₂} tsp ssp (var x) ϱ κ with access ϱ x
... | Gx , Gϱ , ina , ssp12 , v rewrite inactive-right-ssplit ssp12 ina =
  Ready ssp v κ
run tsp ssp (nat unr-φ i) ϱ κ =
  Ready ssp (VInt i (unrestricted-venv unr-φ ϱ)) κ
run tsp ssp (unit unr-φ) ϱ κ =
  Ready ssp (VUnit (unrestricted-venv unr-φ ϱ)) κ
run{φ}{φ₁}{φ₂} tsp ssp (letbind{φ₁₁}{φ₁₂}{t₁}{t₂} sp e₁ e₂) ϱ κ₂ with split-env sp ϱ | split-rotate tsp sp
... | (G₁ , G₂) , ssp-G1G2 , ϱ₁ , ϱ₂ | φ' , tsp-φ' , φ'-tsp with ssplit-compose ssp ssp-G1G2
... | Gi , ssp-3i , ssp-42 =
  run tsp-φ' ssp-3i e₁ ϱ₁
  (bind φ'-tsp ssp-42 e₂ ϱ₂ κ₂)
run tsp ssp (pair sp x₁ x₂) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ with access ϱ₁ x₁ | access ϱ₂ x₂
... | Gv₁ , Gr₁ , ina-Gr₁ , ss-v1r1 , v₁ | Gv₂ , Gr₂ , ina-Gr₂ , ss-v2r2 , v₂ rewrite inactive-right-ssplit ss-v1r1 ina-Gr₁ | inactive-right-ssplit ss-v2r2 ina-Gr₂ =
  Ready ssp (VPair ss-G1G1'G2' v₁ v₂) κ
run tsp ssp (letpair sp p e) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ with access ϱ₁ p
run tsp ssp (letpair sp p e) ϱ κ | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ | Gvp , Gr , ina-Gr , ss-vpr , VPair ss-GG₁G₂ v₁ v₂ with split-rotate tsp sp
... | φ' , ts-φφ1φ' , ts-φ'φ3φ4 rewrite inactive-right-ssplit ss-vpr ina-Gr with ssplit-compose ss-G1G1'G2' ss-GG₁G₂
... | Gi , ss-G3G1Gi , ss-G1G2G2' = run (left (left ts-φ'φ3φ4)) ssp e (vcons ss-G3G1Gi v₁ (vcons ss-G1G2G2' v₂ ϱ₂)) κ 
run{φ}{φ₁}{G = G}{G₁ = G₁} tsp ssp (fork e) ϱ κ with ssplit-refl-left G₁ | split-refl-left φ₁
... | Gi , ss-g1g1g2 | φ' , unr-φ' , sp-φφφ' with split-env sp-φφφ' ϱ
... | (Gp1 , Gp2) , ss-Gp , ϱ₁ , ϱ₂ with unrestricted-venv unr-φ' ϱ₂
... | ina-Gp2 with inactive-right-ssplit-transform ss-Gp ina-Gp2
... | ss-Gp' rewrite sym (ssplit-function2 ss-g1g1g2 ss-Gp') =
  Fork ssp (bind-thunk sp-φφφ' ss-g1g1g2 e ϱ (halt ina-Gp2 UUnit)) κ
run tsp ssp (new unr-φ s) ϱ κ with unrestricted-venv unr-φ ϱ
... | ina rewrite inactive-left-ssplit ssp ina = New s κ
run tsp ssp (close ch) ϱ κ with access ϱ ch
... | Gch , Gϱ , ina , ssp12 , vch with vch | inactive-right-ssplit ssp12 ina
run tsp ssp (close ch) ϱ κ | Gch , Gϱ , ina , ssp12 , vch | vch' | refl = Close ssp vch' κ
run tsp ssp (wait ch) ϱ κ with access ϱ ch
... | Gch , Gϱ , ina , ssp12 , vch with vch | inactive-right-ssplit ssp12 ina
... | vch' | refl = Wait ssp vch' κ
run tsp ssp (Expr.send sp ch vv) ϱ κ with split-env sp ϱ
... | (G₁ , G₂) , ss-gg , ϱ₁ , ϱ₂ with access ϱ₁ ch
... | G₃ , G₄ , ina-G₄ , ss-g1g3g4 , vch with access ϱ₂ vv
... | G₅ , G₆ , ina-G₆ , ss-g2g5g6 , vvv with ssplit-join ss-gg ss-g1g3g4 ss-g2g5g6
... | G₁' , G₂' , ss-g1'g2' , ss-g3g5 , ss-g4g6 rewrite sym (inactive-right-ssplit ss-g1g3g4 ina-G₄) | sym (inactive-right-ssplit ss-g2g5g6 ina-G₆) = Send ssp ss-gg vch vvv κ
run tsp ssp (Expr.recv ch) ϱ κ with access ϱ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch rewrite inactive-right-ssplit ss-vi ina-G₂ = Recv ssp vch κ
run tsp ssp (nselect lab ch) ϱ κ with access ϱ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch rewrite inactive-right-ssplit ss-vi ina-G₂ = NSelect ssp lab vch κ
run tsp ssp (nbranch{m}{alt} sp ch ealts) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ with access ϱ₁ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch with ssplit-compose ssp ss-G1G1'G2'
... | Gi , ss-G-G1'Gi , ss-Gi-G2'-G2 with split-rotate tsp sp
... | φ' , sp-φφ1φ' , sp-φ'φ3φ4 with inactive-right-ssplit ss-vi ina-G₂
... | refl = NBranch ss-G-G1'Gi vch dcont
  where
    dcont : (lab : Fin m) → Cont Gi _ (TChan (SType.force (alt lab)))
    dcont lab = bind sp-φ'φ3φ4 ss-Gi-G2'-G2 (ealts lab) ϱ₂ κ
run tsp ssp (select lab ch) ϱ κ with access ϱ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch rewrite inactive-right-ssplit ss-vi ina-G₂ = Select ssp lab vch κ
run tsp ssp (branch{s₁}{s₂} sp ch e-left e-rght) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-G1G1'G2' , ϱ₁ , ϱ₂ with access ϱ₁ ch
... | G₁ , G₂ , ina-G₂ , ss-vi , vch with ssplit-compose ssp ss-G1G1'G2'
... | Gi , ss-G-G1'Gi , ss-Gi-G2'-G2 with split-rotate tsp sp
... | φ' , sp-φφ1φ' , sp-φ'φ3φ4 with inactive-right-ssplit ss-vi ina-G₂
... | refl = Branch ss-G-G1'Gi vch dcont
  where
    dcont : (lab : Selector) → Cont Gi _ (TChan (selection lab (SType.force s₁) (SType.force s₂)))
    dcont Left = bind sp-φ'φ3φ4 ss-Gi-G2'-G2 e-left ϱ₂ κ
    dcont Right = bind sp-φ'φ3φ4 ss-Gi-G2'-G2 e-rght ϱ₂ κ
run tsp ssp (ulambda sp unr-φ unr-φ₃ ebody) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-g1-g1'-g2' , ϱ₁ , ϱ₂ with unrestricted-venv unr-φ₃ ϱ₂
... | ina-G2' with inactive-right-ssplit ss-g1-g1'-g2' ina-G2'
... | refl = Ready ssp (VFun (inj₂ unr-φ) ϱ₁ ebody) κ
run tsp ssp (llambda sp unr-φ₂ ebody) ϱ κ with split-env sp ϱ
... | (G₁' , G₂') , ss-g1-g1'-g2' , ϱ₁ , ϱ₂ with unrestricted-venv unr-φ₂ ϱ₂
... | ina-G2' with inactive-right-ssplit ss-g1-g1'-g2' ina-G2'
... | refl = Ready ssp (VFun (inj₁ refl) ϱ₁ ebody) κ
run{φ}{φ₁}{φ₂} tsp ssp e@(rec unr-φ ebody) ϱ κ with unrestricted-venv unr-φ ϱ
... | ina-G2' with inactive-right-ssplit (ssplit-sym ssp) ina-G2'
... | refl = Ready ssp (VFun (inj₂ unr-φ) ϱ (unr-subst UFun (rght (split-all-unr unr-φ)) unr-φ e ebody)) κ
run tsp ssp (app sp efun earg) ϱ κ with split-env sp ϱ
... | (G₁ , G₂) , ss-gg , ϱ₁ , ϱ₂ with access ϱ₁ efun
... | G₃ , G₄ , ina-G₄ , ss-g1g3g4 , vfun with access ϱ₂ earg
run{φ}{φ₁}{φ₂} tsp ssp (app sp efun earg) ϱ κ | (G₁ , G₂) , ss-gg , ϱ₁ , ϱ₂ | G₃ , G₄ , ina-G₄ , ss-g1g3g4 , VFun{φ'} x ϱ₃ e | G₅ , G₆ , ina-G₆ , ss-g2g5g6 , varg with ssplit-compose4 ss-gg ss-g2g5g6
... | Gi , ss-g1-g5-gi , ss-gi-g1-g6 with ssplit-compose ssp ss-g1-g5-gi
... | Gi₁ , ss-g-g5-gi1 , ss-gi1-gi-g2 with inactive-right-ssplit ss-g1g3g4 ina-G₄
... | refl with inactive-right-ssplit ss-gi-g1-g6 ina-G₆
... | refl with split-from-disjoint φ' φ₂
... | φ₀ , sp' = Ready ss-g-g5-gi1 varg (bind sp' ss-gi1-gi-g2 e ϱ₃ κ)
run tsp ssp (subsume e t≤t') ϱ κ =
  run tsp ssp e ϱ (subsume t≤t' κ)

-- apply a continuation
apply-cont : ∀ {G G₁ G₂ t φ}
  → (ssp : SSplit G G₁ G₂)
  → (κ : Cont G₂ φ t)
  → Val G₁ t
  → Command G
apply-cont ssp (halt inG un-t) v with unrestricted-val un-t v
... | inG2 with inactive-right-ssplit ssp inG
... | refl = Halt (ssplit-inactive ssp inG2 inG) un-t v
apply-cont ssp (bind ts ss e₂ ϱ₂ κ) v with ssplit-compose3 ssp ss
... | Gi , ss-GGiG4 , ss-GiG1G3 =
  run (left ts) ss-GGiG4 e₂ (vcons ss-GiG1G3 v ϱ₂) κ
apply-cont ssp (bind-thunk ts ss e₂ ϱ₂ κ) v with unrestricted-val UUnit v
... | inG1 with inactive-left-ssplit ssp inG1
... | refl =
  run ts ss e₂ ϱ₂ κ
apply-cont ssp (subsume t≤t' κ) v =
  apply-cont ssp κ (coerce v t≤t')

extract-inactive-from-cont : ∀ {G t φ} → Unr t → Cont G φ t → ∃ λ G' → Inactive G' × SSplit G G' G
extract-inactive-from-cont{G} un-t κ = ssplit-refl-right-inactive G

-- lifting through a trivial extension

lift-val : ∀ {G t} → Val G t → Val (nothing ∷ G) t
lift-venv : ∀ {G φ} → VEnv G φ → VEnv (nothing ∷ G) φ

lift-val (VUnit x) = VUnit (::-inactive x)
lift-val (VInt i x) = VInt i (::-inactive x)
lift-val (VPair x v v₁) = VPair (ss-both x) (lift-val v) (lift-val v₁)
lift-val (VChan b vcr) = VChan b (there vcr)
lift-val (VFun lu ϱ e) = VFun lu (lift-venv ϱ) e

lift-venv (vnil ina) = vnil (::-inactive ina)
lift-venv (vcons ssp v ϱ) = vcons (ss-both ssp) (lift-val v) (lift-venv ϱ)

lift-cont : ∀ {G t φ} → Cont G φ t → Cont (nothing ∷ G) φ t
lift-cont (halt inG un-t) = halt (::-inactive inG) un-t
lift-cont (bind ts ss e₂ ϱ₂ κ) = bind ts (ss-both ss) e₂ (lift-venv ϱ₂) (lift-cont κ)
lift-cont (bind-thunk ts ss e₂ ϱ₂ κ) = bind-thunk ts (ss-both ss) e₂ (lift-venv ϱ₂) (lift-cont κ)
lift-cont (subsume t≤t' κ) = subsume t≤t' (lift-cont κ)

lift-command : ∀ {G} → Command G → Command (nothing ∷ G)
lift-command (Fork ss κ₁ κ₂) = Fork (ss-both ss) (lift-cont κ₁) (lift-cont κ₂)
lift-command (Ready ss v κ) = Ready (ss-both ss) (lift-val v) (lift-cont κ)
lift-command (Halt x unr-t v) = Halt (::-inactive x) unr-t (lift-val v)
lift-command (New s κ) = New s (lift-cont κ)
lift-command (Close ss v κ) = Close (ss-both ss) (lift-val v) (lift-cont κ)
lift-command (Wait ss v κ) = Wait (ss-both ss) (lift-val v) (lift-cont κ)
lift-command (Send ss ss-args vch v κ) = Send (ss-both ss) (ss-both ss-args) (lift-val vch) (lift-val v) (lift-cont κ)
lift-command (Recv ss vch κ) = Recv (ss-both ss) (lift-val vch) (lift-cont κ)
lift-command (Select ss lab vch κ) = Select (ss-both ss) lab (lift-val vch) (lift-cont κ)
lift-command (Branch ss vch dcont) = Branch (ss-both ss) (lift-val vch) λ lab → lift-cont (dcont lab)
lift-command (NSelect ss lab vch κ) = NSelect (ss-both ss) lab (lift-val vch) (lift-cont κ)
lift-command (NBranch ss vch dcont) = NBranch (ss-both ss) (lift-val vch) λ lab → lift-cont (dcont lab)
-- threads
data ThreadPool (G : SCtx) : Set where
  tnil : (ina : Inactive G) → ThreadPool G
  tcons : ∀ {G₁ G₂} → (ss : SSplit G G₁ G₂) → (cmd : Command G₁) → (tp : ThreadPool G₂) → ThreadPool G

-- tack a task to the end of a thread pool to implement round robin scheduling
tsnoc : ∀ {G Gpool Gcmd} → SSplit G Gcmd Gpool → ThreadPool Gpool → Command Gcmd → ThreadPool G
tsnoc ss (tnil ina) cmd = tcons ss cmd (tnil ina)
tsnoc ss (tcons ss₁ cmd₁ tp) cmd with ssplit-compose2 ss ss₁
... | Gi , ss-top , ss-rec = tcons (ssplit-sym ss-top) cmd₁ (tsnoc ss-rec tp cmd)

-- append thread pools
tappend : ∀ {G G1 G2} → SSplit G G1 G2 → ThreadPool G1 → ThreadPool G2 → ThreadPool G
tappend ss-top (tnil ina) tp2 rewrite inactive-left-ssplit ss-top ina = tp2
tappend ss-top (tcons ss cmd tp1) tp2 with ssplit-compose ss-top ss
... | Gi , ss-top' , ss-rec = tcons ss-top' cmd (tappend ss-rec tp1 tp2)

-- apply the inactive extension to a thread pool
lift-threadpool : ∀ {G} → ThreadPool G → ThreadPool (nothing ∷ G)
lift-threadpool (tnil ina) = tnil (::-inactive ina)
lift-threadpool (tcons ss cmd tp) = tcons (ss-both ss) (lift-command cmd) (lift-threadpool tp)

matchWaitAndGo : ∀ {G Gc Gc₁ Gc₂ Gtp Gtpwl Gtpacc φ}
  → SSplit G Gc Gtp
  -- close command
  → SSplit Gc Gc₁ Gc₂ × Val Gc₁ (TChan send!) × Cont Gc₂ φ TUnit
  -- focused thread pool
  → SSplit Gtp Gtpwl Gtpacc → ThreadPool Gtpwl → ThreadPool Gtpacc
  → Maybe (∃ λ G' → ThreadPool G')
matchWaitAndGo ss-top cl-info ss-tp  (tnil ina) tp-acc = nothing
matchWaitAndGo ss-top cl-info ss-tp  (tcons ss (Fork ss₁ κ₁ κ₂) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (Fork ss₁ κ₁ κ₂) tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss (Ready ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (Ready ss₁ v κ) tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(Halt x _ _) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss (New s κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' (New s κ) tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(NSelect ss-args lab vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(Select ss-args lab vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' =
  matchWaitAndGo ss-top cl-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchWaitAndGo ss-top cl-info ss-tp (tcons ss cmd@(NBranch _ _ _) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
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
... | Gunit' , ina-Gunit' , ss-stopped' with ssplit-compose ss-gtpacc (ssplit-sym ss-g4g2)
... | Gi'' , ss-int , ss-g2gacc with ssplit-compose2 ss-others ss-int
... | Gi''' , ss-other , ss-outer-cons = just (Gother , tappend (ssplit-sym ss-other) tp-wl (tcons ss-outer-cons (Ready ss-stopped (VUnit ina-Gunit) cl-κ) (tcons ss-g2gacc (Ready ss-stopped' (VUnit ina-Gunit') κ) tp-acc)))

matchSendAndGo : ∀ {G Gc Gc₁ Gc₂ Gtp Gtpwl Gtpacc φ t s}
  → SSplit G Gc Gtp
  -- read command
  → SSplit Gc Gc₁ Gc₂ × Val Gc₁ (TChan (Typing.recv t s)) × Cont Gc₂ φ (TPair (TChan (SType.force s)) t)
  -- focused thread pool
  → SSplit Gtp Gtpwl Gtpacc → ThreadPool Gtpwl → ThreadPool Gtpacc
  → Maybe (∃ λ G' → ThreadPool G')
matchSendAndGo ss-top recv-info ss-tp (tnil ina) tp-acc = nothing
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Fork ss₁ κ₁ κ₂) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Ready ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Halt _ _ _) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(New s κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(NSelect ss-arg lab vch κ) tp-wl)  tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(Select ss-arg lab vch κ) tp-wl)  tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchSendAndGo ss-top recv-info ss-tp (tcons ss cmd@(NBranch _ _ _) tp-wl)  tp-acc with ssplit-compose5 ss-tp ss
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
... | just (t≤t1 , ds1≡s , GG , GG1 , GG11 , G12 , ssplit2 ss-out1 ss-out2 , vcr-recv , vcr-send) with ssplit-compose ss-gi''gi'gtpacc ss-gi'gig2
... | GSi , ss-Gi''GiGi1 , ss-Gi1G2Gtpacc with ssplit-join ss-out1 ss-out2 ss-g2'gc2gi''
... | GG1' , GG2' , ss-GG-GG1'-GG2' , ss-GG1'-GG11-Gc2 , ss-GG2'-G12-Gi'' with ssplit-rotate ss-GG2'-G12-Gi'' ss-Gi''GiGi1 ss-gig12g3
... | Gi''+ , Gi+ , ss-GG2-G12-Gi''+ , ss-Gi''+Gi+Gsi , ss-Gi+-G12-G4 with ssplit-join ss-GG-GG1'-GG2' ss-GG1'-GG11-Gc2 ss-GG2-G12-Gi''+
... | GG1'' , GG2'' , ss-GG-GG1''-GG2'' , ss-GG1''-GG11-G12 , ss-GG2''-Gc2-Gi''+ with ssplit-compose3 ss-GG-GG1''-GG2'' ss-GG2''-Gc2-Gi''+
... | _ , ss-GG-Gii-Gi''+ , ss-Gii-GG1''-Gc2 = just (GG ,  (tcons ss-GG-Gii-Gi''+ (Ready ss-Gii-GG1''-Gc2 (VPair ss-GG1''-GG11-G12 (VChan b₁ vcr-recv) (coerce v t≤t1)) κ-rv {-κ-rv-}) (tcons ss-Gi''+Gi+Gsi (Ready ss-Gi+-G12-G4 (VChan b vcr-send) κ) (tappend ss-Gi1G2Gtpacc tp-wl tp-acc))))
matchSendAndGo ss-top recv-info@(ss-rv , VChan b₁ vcr₁ , κ-rv) ss-tp (tcons ss cmd@(Send ss₁ ss-args (VChan b vcr) v κ) tp-wl) tp-acc | Gi , ss-g1g11gi , ss-gig12g3 | Gi' , ss-gtpwlg11g2 , ss-gi'gig2 | Gi'' , ss-gtpg11gi'' , ss-gi''gi'gtpacc | G₁' , G₂' , ss-gg1'g2' , ss-g1'gc1g11 , ss-g2'gc2gi'' | nothing with ssplit-compose5 ss-tp ss
... | Gi0 , ss-tp' , ss' = matchSendAndGo ss-top recv-info ss-tp' tp-wl (tcons ss' cmd tp-acc)

matchBranchAndGo : ∀ {G Gc Gc₁ Gc₂ Gtp Gtpwl Gtpacc φ s₁ s₂}
  → SSplit G Gc Gtp
  -- select command
  → (SSplit Gc Gc₁ Gc₂ × ∃ λ lab → Val Gc₁ (TChan (sintern s₁ s₂)) × Cont Gc₂ φ (TChan (selection lab (SType.force s₁) (SType.force s₂))))
  -- focused thread pool
  → SSplit Gtp Gtpwl Gtpacc → ThreadPool Gtpwl → ThreadPool Gtpacc
  → Maybe (∃ λ G' → ThreadPool G')
matchBranchAndGo ss-top select-info ss-tp (tnil ina) tp-acc = nothing
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Fork ss₁ κ₁ κ₂) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Ready ss₁ v κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Halt _ _ _) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
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
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(NSelect ss₁ lab vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(NBranch _ _ _) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top select-info ss-tp (tcons ss cmd@(Select ss₁ lab vch κ) tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top (ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss (Branch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc with ssplit-compose6 ss ss₁
... | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 with ssplit-compose6 ss-tp ss-gtpwl-g3-gi
... | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc with ssplit-join ss-top ss-vκ ss-gtp-g3-gi1
... | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 with vcr-match-2-sb (ssplit2 ss-g-gc'-gtp' ss-gc'-gc1-g1) vcr₁ vcr lab
matchBranchAndGo ss-top select-info@(ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss cmd@(Branch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 | nothing with ssplit-compose5 ss-tp ss
... | Gix , ss-tp' , ss' = matchBranchAndGo ss-top select-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchBranchAndGo ss-top (ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss (Branch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 | just (ds3=s1 , ds4=s2 , GG , GG1 , GG11 , GG12 , ssplit2 ss1' ss2'  , vcr-sel , vcr-bra) with ssplit-compose ss-gi1-gi-gtpacc ss-gi-g4-g2
... | Gi2 , ss-gi1-g3-gi2 , ss-gi2-g2-gtpacc with ssplit-join ss1' ss2' ss-gtp'-gc2-gi1
... | GGG1 , GGG2 , ss-GG-ggg1-ggg2 , ss-ggg1-gc1-gc2 , ss-ggg2-g1-gi1 with ssplit-compose3 ss-ggg2-g1-gi1 ss-gi1-g3-gi2
... | Gi3 , ss-ggg2-gi3-gi2 , ss-gi3-gg12-g2 = just (GG , tcons ss-GG-ggg1-ggg2 (Ready ss-ggg1-gc1-gc2 (VChan b₁ vcr-sel) κ) (tcons ss-ggg2-gi3-gi2 (Ready ss-gi3-gg12-g2 (VChan b vcr-bra) (dcont lab)) (tappend ss-gi2-g2-gtpacc tp-wl tp-acc)))

matchNBranchAndGo : ∀ {G Gc Gc₁ Gc₂ Gtp Gtpwl Gtpacc φ m alt}
  → SSplit G Gc Gtp
  -- select command
  → (SSplit Gc Gc₁ Gc₂ × Σ (Fin m) λ lab → Val Gc₁ (TChan (sintN m alt)) × Cont Gc₂ φ (TChan (SType.force (alt lab))))
  -- focused thread pool
  → SSplit Gtp Gtpwl Gtpacc → ThreadPool Gtpwl → ThreadPool Gtpacc
  → Maybe (∃ λ G' → ThreadPool G')
matchNBranchAndGo ss-top nselect-info ss-tp (tnil ina) tp-acc = nothing
matchNBranchAndGo ss-top (ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss cmd@(NBranch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc with ssplit-compose6 ss ss₁
... | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 with ssplit-compose6 ss-tp ss-gtpwl-g3-gi
... | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc with ssplit-join ss-top ss-vκ ss-gtp-g3-gi1
... | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 with vcr-match-2-nsb (ssplit2 ss-g-gc'-gtp' ss-gc'-gc1-g1) vcr₁ vcr lab
matchNBranchAndGo ss-top nselect-info@(ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss cmd@(NBranch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 | nothing with ssplit-compose5 ss-tp ss
... | Gix , ss-tp' , ss' = matchNBranchAndGo ss-top nselect-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
matchNBranchAndGo ss-top (ss-vκ , lab , VChan b₁ vcr₁ , κ) ss-tp (tcons ss (NBranch ss₁ (VChan b vcr) dcont) tp-wl) tp-acc | Gi , ss-gtpwl-g3-gi , ss-gi-g4-g2 | Gi1 , ss-gtp-g3-gi1 , ss-gi1-gi-gtpacc | Gc' , Gtp' , ss-g-gc'-gtp' , ss-gc'-gc1-g1 , ss-gtp'-gc2-gi1 | just (m1≤m , ds3=s1 , GG , GG1 , GG11 , GG12 , ssplit2 ss1' ss2'  , vcr-sel , vcr-bra) with ssplit-compose ss-gi1-gi-gtpacc ss-gi-g4-g2
... | Gi2 , ss-gi1-g3-gi2 , ss-gi2-g2-gtpacc with ssplit-join ss1' ss2' ss-gtp'-gc2-gi1
... | GGG1 , GGG2 , ss-GG-ggg1-ggg2 , ss-ggg1-gc1-gc2 , ss-ggg2-g1-gi1 with ssplit-compose3 ss-ggg2-g1-gi1 ss-gi1-g3-gi2
... | Gi3 , ss-ggg2-gi3-gi2 , ss-gi3-gg12-g2 = just (GG , tcons ss-GG-ggg1-ggg2 (Ready ss-ggg1-gc1-gc2 (VChan b₁ vcr-sel) κ) (tcons ss-ggg2-gi3-gi2 (Ready ss-gi3-gg12-g2 (VChan b vcr-bra) (dcont (inject≤ lab m1≤m))) (tappend ss-gi2-g2-gtpacc tp-wl tp-acc)))
matchNBranchAndGo ss-top nselect-info ss-tp (tcons ss cmd tp-wl) tp-acc with ssplit-compose5 ss-tp ss
... | Gi , ss-tp' , ss' = matchNBranchAndGo ss-top nselect-info ss-tp' tp-wl (tcons ss' cmd tp-acc)
