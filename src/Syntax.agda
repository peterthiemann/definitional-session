module Syntax where

open import Data.Fin
open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Nat
open import Data.Product

open import Typing

-- expressions
data Expr : (Φ : TCtx) → Type → Set where
  var : ∀ {t Φ}
      → (x : t ∈ Φ)
      → Expr Φ t

  nat : ∀ {Φ}
      → (unr-Φ : All Unr Φ)
      → (i : ℕ)
      → Expr Φ TInt

  unit : ∀ {Φ}
      → (unr-Φ : All Unr Φ)
      → Expr Φ TUnit

  letbind : ∀ {Φ Φ₁ Φ₂ t₁ t₂}
    → (sp : Split Φ Φ₁ Φ₂)
    → (e₁ : Expr Φ₁ t₁)
    → (e₂ : Expr (t₁ ∷ Φ₂) t₂)
    → Expr Φ t₂

  pair : ∀ {Φ Φ₁ Φ₂ t₁ t₂}
    → (sp : Split Φ Φ₁ Φ₂)
    → (x₁ : t₁ ∈ Φ₁)
    → (x₂ : t₂ ∈ Φ₂)
    → Expr Φ (TPair t₁ t₂)

  letpair : ∀ {Φ Φ₁ Φ₂ t₁ t₂ t}
    → (sp : Split Φ Φ₁ Φ₂)
    → (p : TPair t₁ t₂ ∈ Φ₁)
    → (e : Expr (t₁ ∷ t₂ ∷ Φ₂) t)
    → Expr Φ t

  fork : ∀ { Φ}
    → (e : Expr Φ TUnit)
    → Expr Φ TUnit

  new : ∀ {Φ}
      → (unr-Φ : All Unr Φ)
      → (s : SType)
      → Expr Φ (TPair (TChan (SType.force s)) (TChan (SType.force (dual s))))

  -- takes only variables to avoid extraneous effects
  send : ∀ {Φ Φ₁ Φ₂ s t}
      → (sp : Split Φ Φ₁ Φ₂)
      → (ch : (TChan (send t s)) ∈ Φ₁)
      → (vv : t ∈ Φ₂)
      → Expr Φ (TChan (SType.force s))
  -- takes only variables to avoid extraneous effects
  recv : ∀ {Φ s t}
      → (ch : (TChan (recv t s)) ∈ Φ)
      → Expr Φ (TPair (TChan (SType.force s)) t)

  close : ∀ { Φ}
      → (ch : TChan send! ∈ Φ)
      → Expr Φ TUnit

  wait : ∀ { Φ}
      → (ch : TChan send? ∈ Φ)
      → Expr Φ TUnit

  select : ∀ {s₁ s₂ Φ}
      → (lab : Selector)
      → (ch : TChan (sintern s₁ s₂) ∈ Φ)
      → Expr Φ (TChan (selection lab (SType.force s₁) (SType.force s₂)))

  branch : ∀ {s₁ s₂ Φ Φ₁ Φ₂ t}
      → (sp : Split Φ Φ₁ Φ₂)
      → (ch : TChan (sextern s₁ s₂) ∈ Φ₁)
      → (eleft : Expr (TChan (SType.force s₁) ∷ Φ₂) t)
      → (erght : Expr (TChan (SType.force s₂) ∷ Φ₂) t)
      → Expr Φ t

  nselect : ∀ {m alt Φ}
      → (lab : Fin m)
      → (ch : TChan (sintN m alt) ∈ Φ)
      → Expr Φ (TChan (SType.force (alt lab)))

  nbranch : ∀ {m alt Φ Φ₁ Φ₂ t}
      → (sp : Split Φ Φ₁ Φ₂)
      → (ch : TChan (sextN m alt) ∈ Φ₁)
      → (ealts : (i : Fin m) → Expr (TChan (SType.force (alt i)) ∷ Φ₂) t)
      → Expr Φ t

  ulambda : ∀ {Φ Φ₁ Φ₂ t₁ t₂}
      → (sp : Split Φ Φ₁ Φ₂)
      → (unr-Φ₁ : All Unr Φ₁)
      → (unr-Φ₂ : All Unr Φ₂)
      → (ebody : Expr (t₁ ∷ Φ₁) t₂)
      → Expr Φ (TFun UU t₁ t₂)

  llambda : ∀ {Φ Φ₁ Φ₂ t₁ t₂}
      → (sp : Split Φ Φ₁ Φ₂)
      → (unr-Φ₂ : All Unr Φ₂)
      → (ebody : Expr (t₁ ∷ Φ₁) t₂)
      → Expr Φ (TFun LL t₁ t₂)

  app : ∀ {Φ Φ₁ Φ₂ lu t₁ t₂}
      → (sp : Split Φ Φ₁ Φ₂)
      → (xfun : TFun lu t₁ t₂ ∈ Φ₁)
      → (xarg : t₁ ∈ Φ₂)
      → Expr Φ t₂

  rec : ∀ {Φ t₁ t₂}
      → (unr-Φ : All Unr Φ)
      → let t = TFun UU t₁ t₂ in
        (ebody : Expr (t ∷ t₁ ∷ Φ) t₂)
      → Expr Φ t

unr-weaken-var : ∀ {Φ Φ₁ Φ₂ t} → Split Φ Φ₁ Φ₂ → All Unr Φ₂ → t ∈ Φ₁ → t ∈ Φ
unr-weaken-var [] un-Φ₂ ()
unr-weaken-var (unr x₁ sp) (_ ∷ un-Φ₂) (here x) = here (split-unr sp x un-Φ₂)
unr-weaken-var (unr x₁ sp) un-Φ₂ (there x x₂) = unr-weaken-var (rght sp) un-Φ₂ x₂
unr-weaken-var {t = _} (left sp) un-Φ₂ (here x) = here (split-unr sp x un-Φ₂)
unr-weaken-var {t = t} (left sp) un-Φ₂ (there x x₁) = there x (unr-weaken-var sp un-Φ₂ x₁)
unr-weaken-var {t = t} (rght sp) (unr-t ∷ un-Φ₂) (here x) = there unr-t (unr-weaken-var sp un-Φ₂ (here x))
unr-weaken-var {t = t} (rght sp) (unr-t ∷ un-Φ₂) (there x x₁) = there unr-t (unr-weaken-var sp un-Φ₂ (there x x₁))

unr-weaken : ∀ {Φ Φ₁ Φ₂ t} → Split Φ Φ₁ Φ₂ → All Unr Φ₂ → Expr Φ₁ t → Expr Φ t
unr-weaken sp un-Φ₂ (var x) = var (unr-weaken-var sp un-Φ₂ x)
unr-weaken sp un-Φ₂ (nat unr-Φ i) = letbind sp (nat unr-Φ i) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (unit unr-Φ) = letbind sp (unit unr-Φ) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (letbind sp₁ e e₁) = letbind sp (letbind sp₁ e e₁) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (pair sp₁ x₁ x₂) = letbind sp (pair sp₁ x₁ x₂) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (letpair sp₁ p e) = letbind sp (letpair sp₁ p e) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (fork e) = unr-weaken sp un-Φ₂ e
unr-weaken sp un-Φ₂ (new unr-Φ s) = letbind sp (new unr-Φ s) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (send sp₁ ch vv) = letbind sp (send sp₁ ch vv) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (recv ch) = letbind sp (recv ch) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (close ch) = letbind sp (close ch) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (wait ch) = letbind sp (wait ch) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (nselect lab ch) = letbind sp (nselect lab ch) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (nbranch sp₁ ch ealts) = letbind sp (nbranch sp₁ ch ealts) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (select lab ch) = letbind sp (select lab ch) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (branch sp₁ ch e e₁) with split-rotate sp sp₁
... | Φ' , sp-ΦΦ₃Φ' , sp-Φ'Φ₄Φ₂ = branch sp-ΦΦ₃Φ' ch (unr-weaken (left sp-Φ'Φ₄Φ₂) un-Φ₂ e) (unr-weaken (left sp-Φ'Φ₄Φ₂) un-Φ₂ e₁)
unr-weaken sp un-Φ₂ (ulambda sp₁ unr-Φ₁ unr-Φ₂ e) = ulambda sp (split-unr sp₁ unr-Φ₁ unr-Φ₂) un-Φ₂ (unr-weaken (left sp₁) unr-Φ₂ e)
unr-weaken sp un-Φ₂ (llambda sp₁ unr-Φ₂ e) = llambda sp un-Φ₂ (unr-weaken (left sp₁) unr-Φ₂ e)
unr-weaken sp un-Φ₂ (app sp₁ xfun xarg) = letbind sp (app sp₁ xfun xarg) (var (here un-Φ₂))
unr-weaken sp un-Φ₂ (rec unr-Φ e) = rec (split-unr sp unr-Φ un-Φ₂) (unr-weaken (left (left sp)) un-Φ₂ e)


lift-expr : ∀ {Φ t tᵤ} → Unr tᵤ → Expr Φ t → Expr (tᵤ ∷ Φ) t
lift-expr unrtu (var x) = var (there unrtu x)
lift-expr unrtu (nat unr-Φ i) = nat (unrtu ∷ unr-Φ) i
lift-expr unrtu (unit unr-Φ) = unit (unrtu ∷ unr-Φ)
lift-expr unrtu (letbind sp e e₁) = letbind (left sp) (lift-expr unrtu e) e₁
lift-expr unrtu (pair sp x₁ x₂) = pair (rght sp) x₁ (there unrtu x₂)
lift-expr unrtu (letpair sp p e) = letpair (left sp) (there unrtu p) e
lift-expr unrtu (fork e) = lift-expr unrtu e
lift-expr unrtu (new unr-Φ s) = new (unrtu ∷ unr-Φ) s
lift-expr unrtu (close ch) = close (there unrtu ch)
lift-expr unrtu (wait ch) = wait (there unrtu ch)
lift-expr unrtu (send sp ch vv) = send (rght sp) ch (there unrtu vv)
lift-expr unrtu (recv ch) = recv (there unrtu ch)
lift-expr unrtu (nselect lab ch) = nselect lab (there unrtu ch)
lift-expr unrtu (nbranch sp ch ealts) = nbranch (left sp) (there unrtu ch) ealts
lift-expr unrtu (select lab ch) = select lab (there unrtu ch)
lift-expr unrtu (branch sp ch x₁ x₂) = branch (left sp) (there unrtu ch) x₁ x₂
lift-expr unrtu (ulambda sp unr-Φ unr-Φ₂ ebody) = ulambda (rght sp) unr-Φ (unrtu ∷ unr-Φ₂) ebody
lift-expr unrtu (llambda sp unr-Φ₂ ebody) = llambda (rght sp) (unrtu ∷ unr-Φ₂) ebody
lift-expr unrtu (app sp xfun xarg) = app (rght sp) xfun (there unrtu xarg)
lift-expr{Φ} unrtu (rec unr-Φ ebody) = letbind (left (split-all-right Φ)) (var (here [])) (rec (unrtu ∷ unr-Φ) (unr-weaken (left (left (rght (split-all-left Φ)))) (unrtu ∷ []) ebody))

unr-subst : ∀ {Φ Φ₁ Φ₂ tᵤ t} → Unr tᵤ → Split Φ Φ₁ Φ₂ → All Unr Φ₁ → Expr Φ₁ tᵤ → Expr (tᵤ ∷ Φ₂) t → Expr Φ t
unr-subst unrtu sp unr-Φ₁ etu (var (here x)) = unr-weaken sp x etu
unr-subst unrtu sp unr-Φ₁ etu (var (there x x₁)) = var (unr-weaken-var (split-sym sp) unr-Φ₁ x₁)
unr-subst unrtu sp unr-Φ₁ etu (nat (unr-tu ∷ unr-Φ) i) = nat (split-unr sp unr-Φ₁ unr-Φ) i
unr-subst unrtu sp unr-Φ₁ etu (unit (_ ∷ unr-Φ)) = unit (split-unr sp unr-Φ₁ unr-Φ)
unr-subst unrtu sp unr-Φ₁ etu (letbind sp₁ e e₁) = letbind sp etu (letbind sp₁ e e₁)
unr-subst unrtu sp unr-Φ₁ etu (pair sp₁ x₁ x₂) = letbind sp etu (pair sp₁ x₁ x₂)
unr-subst unrtu sp unr-Φ₁ etu (letpair sp₁ p e) = letbind sp etu (letpair sp₁ p e)
unr-subst unrtu sp unr-Φ₁ etu (fork e) = unr-subst unrtu sp unr-Φ₁ etu e
unr-subst unrtu sp unr-Φ₁ etu (new unr-Φ s) = letbind sp etu (new unr-Φ s)
unr-subst unrtu sp unr-Φ₁ etu (send sp₁ ch vv) = letbind sp etu (send sp₁ ch vv)
unr-subst unrtu sp unr-Φ₁ etu (recv ch) = letbind sp etu (recv ch)
unr-subst unrtu sp unr-Φ₁ etu (close ch) = letbind sp etu (close ch)
unr-subst unrtu sp unr-Φ₁ etu (wait ch) = letbind sp etu (wait ch)
unr-subst unrtu sp unr-Φ₁ etu (nselect lab ch) = letbind sp etu (nselect lab ch)
unr-subst unrtu sp unr-Φ₁ etu (nbranch sp₁ ch ealts) = letbind sp etu (nbranch sp₁ ch ealts)
unr-subst unrtu sp unr-Φ₁ etu (select lab ch) = letbind sp etu (select lab ch)
unr-subst unrtu sp unr-Φ₁ etu (branch sp₁ ch e e₁) = letbind sp etu (branch sp₁ ch e e₁)
unr-subst unrtu sp unr-Φ₁ etu (ulambda sp₁ unr-Φ₂ unr-Φ₃ e) = letbind sp etu (ulambda sp₁ unr-Φ₂ unr-Φ₃ e)
unr-subst unrtu sp unr-Φ₁ etu (llambda sp₁ unr-Φ₂ e) = letbind sp etu (llambda sp₁ unr-Φ₂ e)
unr-subst unrtu sp unr-Φ₁ etu (app sp₁ xfun xarg) = letbind sp etu (app sp₁ xfun xarg)
unr-subst unrtu sp unr-Φ₁ etu (rec unr-Φ e) = letbind sp etu (rec unr-Φ e)
