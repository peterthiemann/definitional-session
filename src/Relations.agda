{-# OPTIONS --copatterns #-}
module Relations where

-- open import Agda.Builtin.Size

open import Data.Fin hiding (_≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Typing

{-
mutual

  data Delay {a} (A : Set a) (i : Size) : Set a where
    now   : A          → Delay A i
    later : Delay′ A i → Delay A i

  record Delay′ {a} (A : Set a) (i : Size) : Set a where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Delay A j

open Delay′ public
-}

-- coinductive view on session types
-- following "Interactive Programming in Agda"
-- http://www.cse.chalmers.se/~abela/ooAgda.pdf
mutual
  data Type : Set where
    TUnit TInt : Type
    TPair : Type → Type → Type
    TChan : Session → Type
    TFun  : LU → Type → Type → Type
  
  data SessionF (S : Set) : Set where
    send recv : (t : Type) → (s : S) → SessionF S
    sintern sextern : (s1 : S) (s2 : S) → SessionF S
    sintN sextN : (m : ℕ) (alt : Fin m → S) → SessionF S
    send! send? : SessionF S

  record Session : Set where
    coinductive 
    constructor delay
    field force : SessionF Session

open Session

inType : Ty → Type
inSession : STy₀ 0 → Session

inType TUnit = TUnit
inType TInt = TInt
inType (TPair t t₁) = TPair (inType t) (inType t₁)
inType (TChan x) = TChan (inSession (S1 x))
inType (TFun x t t₁) = TFun x (inType t) (inType t₁)

force (inSession s0) with unroll s0
force (inSession s0) | SSend t s = send (inType t) (inSession s)
force (inSession s0) | SRecv t s = recv (inType t) (inSession s)
force (inSession s0) | SIntern s₁ s₂ = sintern (inSession s₁) (inSession s₂)
force (inSession s0) | SExtern s₁ s₂ = sextern (inSession s₁) (inSession s₂)
force (inSession s0) | SIntN m alt = sintN m λ x → inSession (alt x)
force (inSession s0) | SExtN m alt = sextN m λ x → inSession (alt x)
force (inSession s0) | SEnd! = send!
force (inSession s0) | SEnd? = send?

-- session type equivalence
data EquivF (R : Session → Session → Set) : SessionF Session → SessionF Session → Set where
  eq-send : ∀ {s1 s1'} → (t : Type) → R s1 s1' → EquivF R (send t s1) (send t s1')
  eq-recv : ∀ {s1 s1'} → (t : Type) → R s1 s1' → EquivF R (recv t s1) (recv t s1')
  eq-sintern : ∀ {s1 s1' s2 s2'} → R s1 s1' → R s2 s2' → EquivF R (sintern s1 s2) (sintern s1' s2')
  eq-sextern : ∀ {s1 s1' s2 s2'} → R s1 s1' → R s2 s2' → EquivF R (sextern s1 s2) (sextern s1' s2')
  eq-sintN : ∀ {m alt alt'} → ((i : Fin m) → R (alt i) (alt' i)) → EquivF R (sintN m alt) (sintN m alt')
  eq-sextN : ∀ {m alt alt'} → ((i : Fin m) → R (alt i) (alt' i)) → EquivF R (sextN m alt) (sextN m alt')
  eq-send! : EquivF R send! send!
  eq-send? : EquivF R send? send?

record Equiv (s1 : Session) (s2 : Session) : Set where
  coinductive
  field force : EquivF Equiv (force s1) (force s2)

open Equiv

-- equivalence is reflexive
equivF-refl : ∀ s → EquivF Equiv s s
equiv-refl : ∀ s → Equiv s s

force (equiv-refl s) = equivF-refl (force s)

equivF-refl (send t s) = eq-send t (equiv-refl s)
equivF-refl (recv t s) = eq-recv t (equiv-refl s)
equivF-refl (sintern s1 s2) = eq-sintern (equiv-refl s1) (equiv-refl s2)
equivF-refl (sextern s1 s2) = eq-sextern (equiv-refl s1) (equiv-refl s2)
equivF-refl (sintN m alt) = eq-sintN λ i → equiv-refl (alt i)
equivF-refl (sextN m alt) = eq-sextN λ i → equiv-refl (alt i)
equivF-refl send! = eq-send!
equivF-refl send? = eq-send?

-- equivalence is symmetric
equivF-sym : ∀ s1 s2 → EquivF Equiv s1 s2 → EquivF Equiv s2 s1
equiv-sym : ∀ s1 s2 → Equiv s1 s2 → Equiv s2 s1

force (equiv-sym s1 s2 s1~s2) = equivF-sym (force s1) (force s2) (force s1~s2)

equivF-sym (send .t s1) (send .t s2) (eq-send t x) = eq-send t (equiv-sym s1 s2 x)
equivF-sym (recv .t s1) (recv .t s2) (eq-recv t x) = eq-recv t (equiv-sym s1 s2 x)
equivF-sym (sintern s s₁) (sintern s' s₁') (eq-sintern x x₁) = eq-sintern (equiv-sym s s' x) (equiv-sym s₁ s₁' x₁)
equivF-sym (sextern s s₁) (sextern s' s₁') (eq-sextern x x₁) = eq-sextern (equiv-sym s s' x) (equiv-sym s₁ s₁' x₁)
equivF-sym (sintN _ alt) (sintN _ alt') (eq-sintN x) = eq-sintN λ i → equiv-sym (alt i) (alt' i) (x i)
equivF-sym (sextN _ alt) (sextN _ alt') (eq-sextN x) = eq-sextN λ i → equiv-sym (alt i) (alt' i) (x i)
equivF-sym .send! .send! eq-send! = eq-send!
equivF-sym .send? .send? eq-send? = eq-send?

-- equivalence is transitive
equivF-trans : ∀ s1 s2 s3 → EquivF Equiv s1 s2 → EquivF Equiv s2 s3 → EquivF Equiv s1 s3
equiv-trans : ∀ s1 s2 s3 → Equiv s1 s2 → Equiv s2 s3 → Equiv s1 s3

force (equiv-trans s1 s2 s3 s1~s2 s2~s3) = equivF-trans (force s1) (force s2) (force s3) (force s1~s2) (force s2~s3)

equivF-trans (send .t _) (send .t _) (send .t _) (eq-send t x) (eq-send .t x₁) = eq-send t (equiv-trans _ _ _ x x₁)
equivF-trans .(recv t _) .(recv t _) .(recv t _) (eq-recv t x) (eq-recv .t x₁) = eq-recv t (equiv-trans _ _ _ x x₁)
equivF-trans .(sintern _ _) .(sintern _ _) .(sintern _ _) (eq-sintern x x₁) (eq-sintern x₂ x₃) = eq-sintern (equiv-trans _ _ _ x x₂) (equiv-trans _ _ _ x₁ x₃)
equivF-trans .(sextern _ _) .(sextern _ _) .(sextern _ _) (eq-sextern x x₁) (eq-sextern x₂ x₃) = eq-sextern (equiv-trans _ _ _ x x₂) (equiv-trans _ _ _ x₁ x₃)
equivF-trans .(sintN _ _) .(sintN _ _) .(sintN _ _) (eq-sintN x) (eq-sintN x₁) = eq-sintN λ i → equiv-trans _ _ _ (x i) (x₁ i)
equivF-trans .(sextN _ _) .(sextN _ _) .(sextN _ _) (eq-sextN x) (eq-sextN x₁) = eq-sextN λ i → equiv-trans _ _ _ (x i) (x₁ i)
equivF-trans .send! .send! .send! eq-send! eq-send! = eq-send!
equivF-trans .send? .send? .send? eq-send? eq-send? = eq-send?

mutual
  -- subtyping
  data SubT : Type → Type → Set where
    sub-unit : SubT TUnit TUnit
    sub-int  : SubT TInt TInt
    sub-pair : ∀ {t₁ t₂ t₁' t₂'} → SubT t₁ t₁' → SubT t₂ t₂' → SubT (TPair t₁ t₂) (TPair t₁' t₂')
    sub-fun  : ∀ {t₁ t₂ t₁' t₂' lu} → SubT t₁' t₁ → SubT t₂ t₂' → SubT (TFun lu t₁ t₂) (TFun lu t₁' t₂')
    sub-chan : ∀ {s s'} → Sub s s' → SubT (TChan s) (TChan s')

  -- session type subtyping
  data SubF (R : Session → Session → Set) : SessionF Session → SessionF Session → Set where
    sub-send : ∀ {s1 s1'} → (t t' : Type) → SubT t' t → R s1 s1' → SubF R (send t s1) (send t' s1')
    sub-recv : ∀ {s1 s1'} → (t t' : Type) → SubT t t' → R s1 s1' → SubF R (recv t s1) (recv t' s1')
    sub-sintern : ∀ {s1 s1' s2 s2'} → R s1 s1' → R s2 s2' → SubF R (sintern s1 s2) (sintern s1' s2')
    sub-sextern : ∀ {s1 s1' s2 s2'} → R s1 s1' → R s2 s2' → SubF R (sextern s1 s2) (sextern s1' s2')
    sub-sintN : ∀ {m m' alt alt'} → (m'≤m : m' ≤ m) → ((i : Fin m') → R (alt (inject≤ i m'≤m)) (alt' i)) → SubF R (sintN m alt) (sintN m' alt')
    sub-sextN : ∀ {m m' alt alt'} → (m≤m' : m ≤ m') → ((i : Fin m) → R (alt i) (alt' (inject≤ i m≤m'))) → SubF R (sextN m alt) (sextN m' alt')
    sub-send! : SubF R send! send!
    sub-send? : SubF R send? send?

  record Sub (s1 : Session) (s2 : Session) : Set where
    coinductive
    field force : SubF Sub (force s1) (force s2)

open Sub

inject-refl : ∀ {m} → (i : Fin m) → inject≤ i ≤-refl ≡ i
inject-refl zero = refl
inject-refl (suc i) = cong suc (inject-refl i)

inject-trans : ∀ {m m' m''} → (m'≤m : m' ≤ m) → (m''≤m' : m'' ≤ m') → (i : Fin m'')
  → (inject≤ (inject≤ i m''≤m') m'≤m) ≡ (inject≤ i (≤-trans m''≤m' m'≤m))
inject-trans z≤n z≤n ()
inject-trans (s≤s m'≤m) z≤n ()
inject-trans (s≤s m'≤m) (s≤s m''≤m') zero = refl
inject-trans (s≤s m'≤m) (s≤s m''≤m') (suc i) = cong suc (inject-trans m'≤m m''≤m' i)

-- subtyping is reflexive
subt-refl : ∀ t → SubT t t
subF-refl : ∀ s → SubF Sub s s
sub-refl : ∀ s → Sub s s

force (sub-refl s) = subF-refl (force s)

subF-refl (send t s) = sub-send t t (subt-refl t) (sub-refl s)
subF-refl (recv t s) = sub-recv t t (subt-refl t) (sub-refl s)
subF-refl (sintern s1 s2) = sub-sintern (sub-refl s1) (sub-refl s2)
subF-refl (sextern s1 s2) = sub-sextern (sub-refl s1) (sub-refl s2)
subF-refl (sintN m alt) = sub-sintN ≤-refl auxInt
  where
    auxInt : (i : Fin m) → Sub (alt (inject≤ i ≤-refl)) (alt i)
    auxInt i rewrite inject-refl i = sub-refl (alt i)
subF-refl (sextN m alt) = sub-sextN ≤-refl auxExt
  where
    auxExt : (i : Fin m) → Sub (alt i) (alt (inject≤ i ≤-refl))
    auxExt i rewrite inject-refl i = sub-refl (alt i)
subF-refl send! = sub-send!
subF-refl send? = sub-send?

subt-refl TUnit = sub-unit
subt-refl TInt = sub-int
subt-refl (TPair t t₁) = sub-pair (subt-refl t) (subt-refl t₁)
subt-refl (TChan s) = sub-chan (sub-refl s)
subt-refl (TFun x t t₁) = sub-fun (subt-refl t) (subt-refl t₁)

-- subtyping is transitive
subt-trans : ∀ {t1 t2 t3} → SubT t1 t2 → SubT t2 t3 → SubT t1 t3
sub-trans : ∀ {s1 s2 s3} → Sub s1 s2 → Sub s2 s3 → Sub s1 s3
subF-trans : ∀ {s1 s2 s3} → SubF Sub s1 s2 → SubF Sub s2 s3 → SubF Sub s1 s3

subt-trans sub-unit sub-unit = sub-unit
subt-trans sub-int sub-int = sub-int
subt-trans (sub-pair t1<:t2 t1<:t3) (sub-pair t2<:t3 t2<:t4) = sub-pair (subt-trans t1<:t2 t2<:t3) (subt-trans t1<:t3 t2<:t4)
subt-trans (sub-fun t1<:t2 t1<:t3) (sub-fun t2<:t3 t2<:t4) = sub-fun (subt-trans t2<:t3 t1<:t2) (subt-trans t1<:t3 t2<:t4)
subt-trans (sub-chan s1<:s2) (sub-chan s2<:s3) = sub-chan (sub-trans s1<:s2 s2<:s3)

force (sub-trans s1<:s2 s2<:s3) = subF-trans (force s1<:s2) (force s2<:s3)

subF-trans (sub-send t t' x x₁) (sub-send .t' t'' x₂ x₃) = sub-send t t'' (subt-trans x₂ x) (sub-trans x₁ x₃)
subF-trans (sub-recv t t' x x₁) (sub-recv .t' t'' x₂ x₃) = sub-recv t t'' (subt-trans x x₂) (sub-trans x₁ x₃)
subF-trans (sub-sintern x x₁) (sub-sintern x₂ x₃) = sub-sintern (sub-trans x x₂) (sub-trans x₁ x₃)
subF-trans (sub-sextern x x₁) (sub-sextern x₂ x₃) = sub-sextern (sub-trans x x₂) (sub-trans x₁ x₃)
subF-trans {sintN m alt}{sintN m' alt'}{sintN m'' alt''} (sub-sintN m'≤m palt) (sub-sintN m''≤m' palt') =
  sub-sintN (≤-trans m''≤m' m'≤m) λ i → sub-trans (auxInt i) (palt' i)
  where
    auxInt : (i : Fin m'') → Sub (alt (inject≤ i (≤-trans m''≤m' m'≤m))) (alt' (inject≤ i m''≤m'))
    auxInt i with palt (inject≤ i m''≤m')
    ... | r rewrite (inject-trans  m'≤m m''≤m' i) = r
subF-trans {sextN m alt}{sextN m' alt'}{sextN m'' alt''} (sub-sextN m≤m' palt) (sub-sextN m'≤m'' palt') =
  sub-sextN (≤-trans m≤m' m'≤m'') λ i → sub-trans (palt i) {!!}
  where
    auxExt : (i : Fin m) → Sub (alt' (inject≤ i m≤m')) (alt'' (inject≤ i (≤-trans m≤m' m'≤m'')))
    auxExt i with palt' (inject≤ i m≤m')
    ... | r rewrite (inject-trans m'≤m'' m≤m' i) = r
subF-trans sub-send! sub-send! = sub-send!
subF-trans sub-send? sub-send? = sub-send?
