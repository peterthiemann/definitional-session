module DSession where

open import Data.Bool
open import Data.Fin
open import Data.Empty
open import Data.List
open import Data.List.All
open import Data.Maybe hiding (All)
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

-- this is really just a Kleisli arrow
data Cont (G : SCtx) (φ : TCtx) (t : Type) : Type → Set where
  ident :
    (ina-G : Inactive G)
    → (unr-φ : All Unr φ)
    → Cont G φ t t

  bind : ∀ {φ₁ φ₂ G₁ G₂ t₂ t₃}
    → (ts : Split φ φ₁ φ₂)
    → (ss : SSplit G G₁ G₂)
    → (e₂ : Expr (t ∷ φ₁) t₂)
    → (ϱ₂ : VEnv G₁ φ₁)
    → (κ₂ : Cont G₂ φ₂ t₂ t₃)
    → Cont G φ t t₃

  subsume : ∀ {t₁ t₂}
    → (t≤t1 : SubT t t₁)
    → (κ : Cont G φ t₁ t₂)
    → Cont G φ t t₂

compose : ∀ {G G₁ G₂ φ φ₁ φ₂ t₁ t₂ t₃}
  → Split φ φ₁ φ₂
  → SSplit G G₁ G₂
  → Cont G₁ φ₁ t₁ t₂
  → Cont G₂ φ₂ t₂ t₃
  → Cont G φ t₁ t₃
compose ss ssp (ident ina-G unr-φ) (ident ina-G₁ unr-φ₁) =
  ident (ssplit-inactive ssp ina-G ina-G₁) (split-unr ss unr-φ unr-φ₁)
compose ss ssp (ident ina-G unr-φ) (bind ts ss₁ e₂ ϱ₂ κ₂) = bind {!!} {!!} e₂ ϱ₂ κ₂
compose ss ssp (ident ina-G unr-φ) (subsume t≤t1 κ₂)
  with inactive-left-ssplit ssp ina-G
... | refl
  = subsume t≤t1 {!!}
compose ss ssp (bind ts ss₁ e₂ ϱ₂ κ₁) (ident ina-G unr-φ) = {!!}
compose ss ssp (bind ts ss₁ e₂ ϱ₂ κ₁) (bind ts₁ ss₂ e₃ ϱ₃ κ₂) = {!!}
compose ss ssp (bind ts ss₁ e₂ ϱ₂ κ₁) (subsume t≤t1 κ₂) = {!!}
compose ss ssp (subsume t≤t1 κ₁) (ident ina-G unr-φ) = {!!}
compose ss ssp (subsume t≤t1 κ₁) (bind ts ss₁ e₂ ϱ₂ κ₂) = {!!}
compose ss ssp (subsume t≤t1 κ₁) (subsume t≤t2 κ₂) = {!!}

-- command is a monad
data Command (G : SCtx) (t : Type) : Set where

  Return : (v : Val G t)
    → Command G t

  Fork : ∀ {φ₁ φ₂ G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → (κ₁ : Cont G₁ φ₁ TUnit TUnit)
    → (κ₂ : Cont G₂ φ₂ TUnit t)
    → Command G t

  New : ∀ {φ}
    → (s : SType)
    → (κ : Cont G φ (TPair (TChan (SType.force s)) (TChan (SType.force (dual s)))) t)
    → Command G t

  Close : ∀ {φ G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → (v : Val G₁ (TChan send!))
    → (κ : Cont G₂ φ TUnit t)
    → Command G t

  Wait  : ∀ {φ G₁ G₂}
    → (ss : SSplit G G₁ G₂)
    → (v : Val G₁ (TChan send?))
    → (κ : Cont G₂ φ TUnit t)
    → Command G t

  Send : ∀ {φ G₁ G₂ G₁₁ G₁₂ tv s}
    → (ss : SSplit G G₁ G₂)
    → (ss-args : SSplit G₁ G₁₁ G₁₂)
    → (vch : Val G₁₁ (TChan (send tv s)))
    → (v : Val G₁₂ tv)
    → (κ : Cont G₂ φ (TChan (SType.force s)) t)
    → Command G t
    
  Recv : ∀ {φ G₁ G₂ tv s}
    → (ss : SSplit G G₁ G₂)
    → (vch : Val G₁ (TChan (recv tv s)))
    → (κ : Cont G₂ φ (TPair (TChan (SType.force s)) tv) t)
    → Command G t

  Select : ∀ {φ G₁ G₂ s₁ s₂}
    → (ss : SSplit G G₁ G₂)
    → (lab : Selector)
    → (vch : Val G₁ (TChan (sintern s₁ s₂)))
    → (κ : Cont G₂ φ (TChan (selection lab (SType.force s₁) (SType.force s₂))) t)
    → Command G t

  Branch : ∀ {φ G₁ G₂ s₁ s₂}
    → (ss : SSplit G G₁ G₂)
    → (vch : Val G₁ (TChan (sextern s₁ s₂)))
    → (dcont : (lab : Selector) → Cont G₂ φ (TChan (selection lab (SType.force s₁) (SType.force s₂))) t)
    → Command G t

  NSelect : ∀ {φ G₁ G₂ m alt}
    → (ss : SSplit G G₁ G₂)
    → (lab : Fin m)
    → (vch : Val G₁ (TChan (sintN m alt)))
    → (κ : Cont G₂ φ (TChan (SType.force (alt lab))) t)
    → Command G t

  NBranch : ∀ {φ G₁ G₂ m alt}
    → (ss : SSplit G G₁ G₂)
    → (vch : Val G₁ (TChan (sextN m alt)))
    → (dcont : (lab : Fin m) → Cont G₂ φ (TChan (SType.force (alt lab))) t)
    → Command G t

-- cont G = ∀ G' → G ≤ G' → SSplit G' Gval Gcont → Val Gval t → 

data _≼_ G : SCtx → Set where
  ≼-rfl : G ≼ G
  ≼-ext : ∀ {G'} → G ≼ G' → G ≼ (nothing ∷ G')

{-
mbindf : ∀ {Gin G1in G2in G1out G2out t t'} → SSplit Gin G1in G2in
  → Command G1in G1out t
  → (∀ G2in' G1out' G2out' → G2in ≼ G2in' → G1out ≼ G1out' → G2out ≼ G2out'
    → Val G1out' t → Command G2in' G2out' t')
  → Command Gin G2out t'
mbindf = {!!}
-}

mbind : ∀ {G G₁ G₂ Φ t t'} → SSplit G G₁ G₂ → Command G₁ t → Cont G₂ Φ t t' → Command G t'
mbind ssp (Return v) (ident x x₁)
  with inactive-right-ssplit ssp x
... | refl
  = Return v
mbind ssp (Return v) (bind ts ss e₂ ϱ₂ cont) = {!!}
mbind ssp (Return v) (subsume t≤t1 cont) = {!!}
mbind ssp (Fork ss κ₁ κ₂) cont = Fork {!!} κ₁ {!!}
mbind ssp (New s κ) cont = {!!}
mbind ssp (Close ss v κ) cont = {!!}
mbind ssp (Wait ss v κ) cont = {!!}
mbind ssp (Send ss ss-args vch v κ) cont = {!!}
mbind ssp (Recv ss vch κ) cont = {!!}
mbind ssp (Select ss lab vch κ) cont = {!!}
mbind ssp (Branch ss vch dcont) cont = {!!}
mbind ssp (NSelect ss lab vch κ) cont = {!!}
mbind ssp (NBranch ss vch dcont) cont = {!!}
