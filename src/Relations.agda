module Relations where

open import Data.Fin hiding (_≤_)
open import Data.List
open import Data.List.All
open import Data.Maybe hiding (All)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Relation.Binary.PropositionalEquality

-- linearity indicator
data LU : Set where
  LL UU : LU

-- coinductive view on session types
-- following "Interactive Programming in Agda"
-- http://www.cse.chalmers.se/~abela/ooAgda.pdf
mutual
  data Type : Set where
    TUnit TInt : Type
    TPair : Type → Type → Type
    TChan : SessionF Session → Type
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

_≈_ = Equiv
_≈'_ = EquivF Equiv

-- equivalence is reflexive
equivF-refl : ∀ s → s ≈' s
equiv-refl : ∀ s → s ≈ s

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

eqF-sym : ∀ {s1 s2} → s1 ≈' s2 → s2 ≈' s1
eq-sym : ∀ {s1 s2} → s1 ≈ s2 → s2 ≈ s1

eqF-sym (eq-send t x) = eq-send t (eq-sym x)
eqF-sym (eq-recv t x) = eq-recv t (eq-sym x)
eqF-sym (eq-sintern x x₁) = eq-sintern (eq-sym x) (eq-sym x₁)
eqF-sym (eq-sextern x x₁) = eq-sextern (eq-sym x) (eq-sym x₁)
eqF-sym (eq-sintN x) = eq-sintN λ i → eq-sym (x i)
eqF-sym (eq-sextN x) = eq-sextN λ i → eq-sym (x i)
eqF-sym eq-send! = eq-send!
eqF-sym eq-send? = eq-send?

force (eq-sym s1~s2) = eqF-sym (force s1~s2)

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

-- dual
dual : Session → Session
dualF : SessionF Session → SessionF Session

force (dual s) = dualF (force s)

dualF (send t s) = recv t (dual s)
dualF (recv t s) = send t (dual s)
dualF (sintern s1 s2) = sextern (dual s1) (dual s2)
dualF (sextern s1 s2) = sintern (dual s1) (dual s2)
dualF (sintN m alt) = sextN m λ i → dual (alt i)
dualF (sextN m alt) = sintN m λ i → dual (alt i)
dualF send! = send?
dualF send? = send!

-- properties

dual-involution : (s : Session) → s ≈ dual (dual s)
dual-involutionF : (s : SessionF Session) → s ≈' dualF (dualF s)

force (dual-involution s) = dual-involutionF (force s)

dual-involutionF (send t s) = eq-send t (dual-involution s)
dual-involutionF (recv t s) = eq-recv t (dual-involution s)
dual-involutionF (sintern s1 s2) = eq-sintern (dual-involution s1) (dual-involution s2)
dual-involutionF (sextern s1 s2) = eq-sextern (dual-involution s1) (dual-involution s2)
dual-involutionF (sintN m alt) = eq-sintN λ i → dual-involution (alt i)
dual-involutionF (sextN m alt) = eq-sextN λ i → dual-involution (alt i)
dual-involutionF send! = eq-send!
dual-involutionF send? = eq-send?



mutual
  -- subtyping
  data SubT : Type → Type → Set where
    sub-unit : SubT TUnit TUnit
    sub-int  : SubT TInt TInt
    sub-pair : ∀ {t₁ t₂ t₁' t₂'} → SubT t₁ t₁' → SubT t₂ t₂' → SubT (TPair t₁ t₂) (TPair t₁' t₂')
    sub-fun  : ∀ {t₁ t₂ t₁' t₂' lu} → SubT t₁' t₁ → SubT t₂ t₂' → SubT (TFun lu t₁ t₂) (TFun lu t₁' t₂')
    sub-chan : ∀ {s s'} → SubF Sub s s' → SubT (TChan s) (TChan s')

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
subt-refl (TChan s) = sub-chan (subF-refl s)
subt-refl (TFun x t t₁) = sub-fun (subt-refl t) (subt-refl t₁)

-- subtyping is transitive
subt-trans : ∀ {t1 t2 t3} → SubT t1 t2 → SubT t2 t3 → SubT t1 t3
sub-trans : ∀ {s1 s2 s3} → Sub s1 s2 → Sub s2 s3 → Sub s1 s3
subF-trans : ∀ {s1 s2 s3} → SubF Sub s1 s2 → SubF Sub s2 s3 → SubF Sub s1 s3

subt-trans sub-unit sub-unit = sub-unit
subt-trans sub-int sub-int = sub-int
subt-trans (sub-pair t1<:t2 t1<:t3) (sub-pair t2<:t3 t2<:t4) = sub-pair (subt-trans t1<:t2 t2<:t3) (subt-trans t1<:t3 t2<:t4)
subt-trans (sub-fun t1<:t2 t1<:t3) (sub-fun t2<:t3 t2<:t4) = sub-fun (subt-trans t2<:t3 t1<:t2) (subt-trans t1<:t3 t2<:t4)
subt-trans (sub-chan s1<:s2) (sub-chan s2<:s3) = sub-chan (subF-trans s1<:s2 s2<:s3)

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
  sub-sextN (≤-trans m≤m' m'≤m'') λ i → sub-trans (palt i) (auxExt i)
  where
    auxExt : (i : Fin m) → Sub (alt' (inject≤ i m≤m')) (alt'' (inject≤ i (≤-trans m≤m' m'≤m'')))
    auxExt i with palt' (inject≤ i m≤m')
    ... | r rewrite (inject-trans m'≤m'' m≤m' i) = r
subF-trans sub-send! sub-send! = sub-send!
subF-trans sub-send? sub-send? = sub-send?

-- unrestricted
data Unr : Type → Set where
  UUnit : Unr TUnit
  UInt : Unr TInt
  UPair : ∀ {t₁ t₂} → Unr t₁ → Unr t₂ → Unr (TPair t₁ t₂)
  UFun :  ∀ {t₁ t₂} → Unr (TFun UU t₁ t₂)

classify-type : (t : Type) → Maybe (Unr t)
classify-type TUnit = just UUnit
classify-type TInt = just UInt
classify-type (TPair t₁ t₂) with classify-type t₁ | classify-type t₂
classify-type (TPair t₁ t₂) | just x | just x₁ = just (UPair x x₁)
classify-type (TPair t₁ t₂) | just x | nothing = nothing
classify-type (TPair t₁ t₂) | nothing | just x = nothing
classify-type (TPair t₁ t₂) | nothing | nothing = nothing
classify-type (TChan x) = nothing
classify-type (TFun LL t₁ t₂) = nothing
classify-type (TFun UU t₁ t₂) = just UFun



TCtx = List Type

-- context splitting, respecting linearity
data Split : TCtx → TCtx → TCtx → Set where
  [] : Split [] [] []
  unr : ∀ {t Φ Φ₁ Φ₂} → Unr t → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) (t ∷ Φ₂)
  left : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) (t ∷ Φ₁) Φ₂
  rght : ∀ {t Φ Φ₁ Φ₂} → Split Φ Φ₁ Φ₂ → Split (t ∷ Φ) Φ₁ (t ∷ Φ₂)

-- split is symmetric
split-sym : ∀ {φ φ₁ φ₂} → Split φ φ₁ φ₂ → Split φ φ₂ φ₁
split-sym [] = []
split-sym (unr x sp) = unr x (split-sym sp)
split-sym (left sp) = rght (split-sym sp)
split-sym (rght sp) = left (split-sym sp)

split-unr : ∀ {φ φ₁ φ₂} → (sp : Split φ φ₁ φ₂) → All Unr φ₁ → All Unr φ₂ → All Unr φ
split-unr [] [] [] = []
split-unr (unr x sp) (px ∷ unr1) (px₁ ∷ unr2) = px ∷ split-unr sp unr1 unr2
split-unr (left sp) (px ∷ unr1) unr2 = px ∷ split-unr sp unr1 unr2
split-unr (rght sp) unr1 (px ∷ unr2) = px ∷ split-unr sp unr1 unr2

split-all-left : (φ : TCtx) → Split φ φ []
split-all-left [] = []
split-all-left (x ∷ φ) = left (split-all-left φ)

split-all-right : (φ : TCtx) → Split φ [] φ
split-all-right [] = []
split-all-right (x ∷ φ) = rght (split-all-right φ)

-- split the unrestricted part from a typing context
split-refl-left : (φ : TCtx) → Σ TCtx λ φ' → All Unr φ' × Split φ φ φ'
split-refl-left [] = [] , [] , []
split-refl-left (t ∷ φ) with split-refl-left φ | classify-type t
split-refl-left (t ∷ φ) | φ' , unr-φ' , sp' | nothing = φ' , unr-φ' , left sp'
split-refl-left (t ∷ φ) | φ' , unr-φ' , sp' | just y = t ∷ φ' , y ∷ unr-φ' , unr y sp'

split-all-unr : ∀ {φ} → All Unr φ → Split φ φ φ
split-all-unr [] = []
split-all-unr (px ∷ un-φ) = unr px (split-all-unr un-φ)

split-from-disjoint : (φ₁ φ₂ : TCtx) → Σ TCtx λ φ → Split φ φ₁ φ₂
split-from-disjoint [] φ₂ = φ₂ , split-all-right φ₂
split-from-disjoint (t ∷ φ₁) φ₂ with split-from-disjoint φ₁ φ₂
... | φ' , sp = t ∷ φ' , left sp

-- reorganize splits
split-rotate : ∀ {φ φ₁ φ₂ φ₁₁ φ₁₂}
  → Split φ φ₁ φ₂ → Split φ₁ φ₁₁ φ₁₂ → Σ TCtx λ φ' → Split φ φ₁₁ φ' × Split φ' φ₁₂ φ₂
split-rotate [] [] = [] , [] , []
split-rotate (unr x sp12) (unr x₁ sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , unr x₁ sp-φ' , unr x₁ φ'-sp
split-rotate (unr x sp12) (left sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , unr x sp-φ' , rght φ'-sp
split-rotate (unr x sp12) (rght sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , rght sp-φ' , unr x φ'-sp
split-rotate (left sp12) (unr x₁ sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , unr x₁ sp-φ' , left φ'-sp
split-rotate (left sp12) (left sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = φ' , left sp-φ' , φ'-sp
split-rotate (left sp12) (rght sp1112) with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , rght sp-φ' , left φ'-sp
split-rotate (rght sp12) sp1112 with split-rotate sp12 sp1112
... | φ' , sp-φ' , φ'-sp = _ ∷ φ' , rght sp-φ' , rght φ'-sp



-- extract from type context where all other entries are unrestricted
data _∈_ (x : Type) : List Type → Set where
  here  : ∀ { xs } → All Unr xs → x ∈ (x ∷ xs)
  there : ∀ { x₀ xs } → Unr x₀ → x ∈ xs → x ∈ (x₀ ∷ xs)

-- left and right branching
data Selector : Set where
  Left Right : Selector

selection : ∀ {A : Set} → Selector → A → A → A
selection Left x y = x
selection Right x y = y
