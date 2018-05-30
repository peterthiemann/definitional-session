module Syntax where

open import Data.Fin
open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Nat
open import Data.Product

open import Typing

-- expressions
data Expr : (φ : List Type) → Type → Set where
  var : ∀ {t φ}
      → (x : t ∈ φ)
      → Expr φ t

  nat : ∀ {φ}
      → (unr-φ : All Unr φ)
      → (i : ℕ)
      → Expr φ TInt

  unit : ∀ {φ}
      → (unr-φ : All Unr φ)
      → Expr φ TUnit

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
      → (s : Session)
      → Expr φ (TPair (TChan (Session.force s)) (TChan (Session.force (dual s))))

  -- takes only variables to avoid extraneous effects
  send : ∀ {φ φ₁ φ₂ s t}
      → (sp : Split φ φ₁ φ₂)
      → (ch : (TChan (send t s)) ∈ φ₁)
      → (vv : t ∈ φ₂)
      → Expr φ (TChan (Session.force s))
  -- takes only variables to avoid extraneous effects
  recv : ∀ {φ s t}
      → (ch : (TChan (recv t s)) ∈ φ)
      → Expr φ (TPair (TChan (Session.force s)) t)

  close : ∀ { φ}
      → (ch : TChan send! ∈ φ)
      → Expr φ TUnit

  wait : ∀ { φ}
      → (ch : TChan send? ∈ φ)
      → Expr φ TUnit

  select : ∀ {s₁ s₂ φ}
      → (lab : Selector)
      → (ch : TChan (sintern s₁ s₂) ∈ φ)
      → Expr φ (TChan (selection lab (Session.force s₁) (Session.force s₂)))

  branch : ∀ {s₁ s₂ φ φ₁ φ₂ t}
      → (sp : Split φ φ₁ φ₂)
      → (ch : TChan (sextern s₁ s₂) ∈ φ₁)
      → (eleft : Expr (TChan (Session.force s₁) ∷ φ₂) t)
      → (erght : Expr (TChan (Session.force s₂) ∷ φ₂) t)
      → Expr φ t

  nselect : ∀ {m alt φ}
      → (lab : Fin m)
      → (ch : TChan (sintN m alt) ∈ φ)
      → Expr φ (TChan (Session.force (alt lab)))

  nbranch : ∀ {m alt φ φ₁ φ₂ t}
      → (sp : Split φ φ₁ φ₂)
      → (ch : TChan (sextN m alt) ∈ φ₁)
      → (ealts : (i : Fin m) → Expr (TChan (Session.force (alt i)) ∷ φ₂) t)
      → Expr φ t

  ulambda : ∀ {φ φ₁ φ₂ t₁ t₂}
      → (sp : Split φ φ₁ φ₂)
      → (unr-φ₁ : All Unr φ₁)
      → (unr-φ₂ : All Unr φ₂)
      → (ebody : Expr (t₁ ∷ φ₁) t₂)
      → Expr φ (TFun UU t₁ t₂)

  llambda : ∀ {φ φ₁ φ₂ t₁ t₂}
      → (sp : Split φ φ₁ φ₂)
      → (unr-φ₂ : All Unr φ₂)
      → (ebody : Expr (t₁ ∷ φ₁) t₂)
      → Expr φ (TFun LL t₁ t₂)

  app : ∀ {φ φ₁ φ₂ lu t₁ t₂}
      → (sp : Split φ φ₁ φ₂)
      → (xfun : TFun lu t₁ t₂ ∈ φ₁)
      → (xarg : t₁ ∈ φ₂)
      → Expr φ t₂

  rec : ∀ {φ t₁ t₂}
      → (unr-φ : All Unr φ)
      → let t = TFun UU t₁ t₂ in
        (ebody : Expr (t ∷ t₁ ∷ φ) t₂)
      → Expr φ t

unr-weaken-var : ∀ {φ φ₁ φ₂ t} → Split φ φ₁ φ₂ → All Unr φ₂ → t ∈ φ₁ → t ∈ φ
unr-weaken-var [] un-φ₂ ()
unr-weaken-var (unr x₁ sp) (_ ∷ un-φ₂) (here x) = here (split-unr sp x un-φ₂)
unr-weaken-var (unr x₁ sp) un-φ₂ (there x x₂) = unr-weaken-var (rght sp) un-φ₂ x₂
unr-weaken-var {t = _} (left sp) un-φ₂ (here x) = here (split-unr sp x un-φ₂)
unr-weaken-var {t = t} (left sp) un-φ₂ (there x x₁) = there x (unr-weaken-var sp un-φ₂ x₁)
unr-weaken-var {t = t} (rght sp) (unr-t ∷ un-φ₂) (here x) = there unr-t (unr-weaken-var sp un-φ₂ (here x))
unr-weaken-var {t = t} (rght sp) (unr-t ∷ un-φ₂) (there x x₁) = there unr-t (unr-weaken-var sp un-φ₂ (there x x₁))

unr-weaken : ∀ {φ φ₁ φ₂ t} → Split φ φ₁ φ₂ → All Unr φ₂ → Expr φ₁ t → Expr φ t
unr-weaken sp un-φ₂ (var x) = var (unr-weaken-var sp un-φ₂ x)
unr-weaken sp un-φ₂ (nat unr-φ i) = letbind sp (nat unr-φ i) (var (here un-φ₂))
unr-weaken sp un-φ₂ (unit unr-φ) = letbind sp (unit unr-φ) (var (here un-φ₂))
unr-weaken sp un-φ₂ (letbind sp₁ e e₁) = letbind sp (letbind sp₁ e e₁) (var (here un-φ₂))
unr-weaken sp un-φ₂ (pair sp₁ x₁ x₂) = letbind sp (pair sp₁ x₁ x₂) (var (here un-φ₂))
unr-weaken sp un-φ₂ (letpair sp₁ p e) = letbind sp (letpair sp₁ p e) (var (here un-φ₂))
unr-weaken sp un-φ₂ (fork e) = unr-weaken sp un-φ₂ e
unr-weaken sp un-φ₂ (new unr-φ s) = letbind sp (new unr-φ s) (var (here un-φ₂))
unr-weaken sp un-φ₂ (send sp₁ ch vv) = letbind sp (send sp₁ ch vv) (var (here un-φ₂))
unr-weaken sp un-φ₂ (recv ch) = letbind sp (recv ch) (var (here un-φ₂))
unr-weaken sp un-φ₂ (close ch) = letbind sp (close ch) (var (here un-φ₂))
unr-weaken sp un-φ₂ (wait ch) = letbind sp (wait ch) (var (here un-φ₂))
unr-weaken sp un-φ₂ (nselect lab ch) = letbind sp (nselect lab ch) (var (here un-φ₂))
unr-weaken sp un-φ₂ (nbranch sp₁ ch ealts) = letbind sp (nbranch sp₁ ch ealts) (var (here un-φ₂))
unr-weaken sp un-φ₂ (select lab ch) = letbind sp (select lab ch) (var (here un-φ₂))
unr-weaken sp un-φ₂ (branch sp₁ ch e e₁) with split-rotate sp sp₁
... | φ' , sp-φφ₃φ' , sp-φ'φ₄φ₂ = branch sp-φφ₃φ' ch (unr-weaken (left sp-φ'φ₄φ₂) un-φ₂ e) (unr-weaken (left sp-φ'φ₄φ₂) un-φ₂ e₁)
unr-weaken sp un-φ₂ (ulambda sp₁ unr-φ₁ unr-φ₂ e) = ulambda sp (split-unr sp₁ unr-φ₁ unr-φ₂) un-φ₂ (unr-weaken (left sp₁) unr-φ₂ e)
unr-weaken sp un-φ₂ (llambda sp₁ unr-φ₂ e) = llambda sp un-φ₂ (unr-weaken (left sp₁) unr-φ₂ e)
unr-weaken sp un-φ₂ (app sp₁ xfun xarg) = letbind sp (app sp₁ xfun xarg) (var (here un-φ₂))
unr-weaken sp un-φ₂ (rec unr-φ e) = rec (split-unr sp unr-φ un-φ₂) (unr-weaken (left (left sp)) un-φ₂ e)


lift-expr : ∀ {φ t tᵤ} → Unr tᵤ → Expr φ t → Expr (tᵤ ∷ φ) t
lift-expr unrtu (var x) = var (there unrtu x)
lift-expr unrtu (nat unr-φ i) = nat (unrtu ∷ unr-φ) i
lift-expr unrtu (unit unr-φ) = unit (unrtu ∷ unr-φ)
lift-expr unrtu (letbind sp e e₁) = letbind (left sp) (lift-expr unrtu e) e₁
lift-expr unrtu (pair sp x₁ x₂) = pair (rght sp) x₁ (there unrtu x₂)
lift-expr unrtu (letpair sp p e) = letpair (left sp) (there unrtu p) e
lift-expr unrtu (fork e) = lift-expr unrtu e
lift-expr unrtu (new unr-φ s) = new (unrtu ∷ unr-φ) s
lift-expr unrtu (close ch) = close (there unrtu ch)
lift-expr unrtu (wait ch) = wait (there unrtu ch)
lift-expr unrtu (send sp ch vv) = send (rght sp) ch (there unrtu vv)
lift-expr unrtu (recv ch) = recv (there unrtu ch)
lift-expr unrtu (nselect lab ch) = nselect lab (there unrtu ch)
lift-expr unrtu (nbranch sp ch ealts) = nbranch (left sp) (there unrtu ch) ealts
lift-expr unrtu (select lab ch) = select lab (there unrtu ch)
lift-expr unrtu (branch sp ch x₁ x₂) = branch (left sp) (there unrtu ch) x₁ x₂
lift-expr unrtu (ulambda sp unr-φ unr-φ₂ ebody) = ulambda (rght sp) unr-φ (unrtu ∷ unr-φ₂) ebody
lift-expr unrtu (llambda sp unr-φ₂ ebody) = llambda (rght sp) (unrtu ∷ unr-φ₂) ebody
lift-expr unrtu (app sp xfun xarg) = app (rght sp) xfun (there unrtu xarg)
lift-expr{φ} unrtu (rec unr-φ ebody) = letbind (left (split-all-right φ)) (var (here [])) (rec (unrtu ∷ unr-φ) (unr-weaken (left (left (rght (split-all-left φ)))) (unrtu ∷ []) ebody))

unr-subst : ∀ {φ φ₁ φ₂ tᵤ t} → Unr tᵤ → Split φ φ₁ φ₂ → All Unr φ₁ → Expr φ₁ tᵤ → Expr (tᵤ ∷ φ₂) t → Expr φ t
unr-subst unrtu sp unr-φ₁ etu (var (here x)) = unr-weaken sp x etu
unr-subst unrtu sp unr-φ₁ etu (var (there x x₁)) = var (unr-weaken-var (split-sym sp) unr-φ₁ x₁)
unr-subst unrtu sp unr-φ₁ etu (nat (unr-tu ∷ unr-φ) i) = nat (split-unr sp unr-φ₁ unr-φ) i
unr-subst unrtu sp unr-φ₁ etu (unit (_ ∷ unr-φ)) = unit (split-unr sp unr-φ₁ unr-φ)
unr-subst unrtu sp unr-φ₁ etu (letbind sp₁ e e₁) = letbind sp etu (letbind sp₁ e e₁)
unr-subst unrtu sp unr-φ₁ etu (pair sp₁ x₁ x₂) = letbind sp etu (pair sp₁ x₁ x₂)
unr-subst unrtu sp unr-φ₁ etu (letpair sp₁ p e) = letbind sp etu (letpair sp₁ p e)
unr-subst unrtu sp unr-φ₁ etu (fork e) = unr-subst unrtu sp unr-φ₁ etu e
unr-subst unrtu sp unr-φ₁ etu (new unr-φ s) = letbind sp etu (new unr-φ s)
unr-subst unrtu sp unr-φ₁ etu (send sp₁ ch vv) = letbind sp etu (send sp₁ ch vv)
unr-subst unrtu sp unr-φ₁ etu (recv ch) = letbind sp etu (recv ch)
unr-subst unrtu sp unr-φ₁ etu (close ch) = letbind sp etu (close ch)
unr-subst unrtu sp unr-φ₁ etu (wait ch) = letbind sp etu (wait ch)
unr-subst unrtu sp unr-φ₁ etu (nselect lab ch) = letbind sp etu (nselect lab ch)
unr-subst unrtu sp unr-φ₁ etu (nbranch sp₁ ch ealts) = letbind sp etu (nbranch sp₁ ch ealts)
unr-subst unrtu sp unr-φ₁ etu (select lab ch) = letbind sp etu (select lab ch)
unr-subst unrtu sp unr-φ₁ etu (branch sp₁ ch e e₁) = letbind sp etu (branch sp₁ ch e e₁)
unr-subst unrtu sp unr-φ₁ etu (ulambda sp₁ unr-φ₂ unr-φ₃ e) = letbind sp etu (ulambda sp₁ unr-φ₂ unr-φ₃ e)
unr-subst unrtu sp unr-φ₁ etu (llambda sp₁ unr-φ₂ e) = letbind sp etu (llambda sp₁ unr-φ₂ e)
unr-subst unrtu sp unr-φ₁ etu (app sp₁ xfun xarg) = letbind sp etu (app sp₁ xfun xarg)
unr-subst unrtu sp unr-φ₁ etu (rec unr-φ e) = letbind sp etu (rec unr-φ e)
