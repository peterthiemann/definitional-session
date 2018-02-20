{-# OPTIONS --allow-unsolved-metas #-}
module Lemmas where

open import Data.Fin hiding (_+_ ; _≤_)
open import Data.List
open import Data.Nat
open import Relation.Binary.PropositionalEquality


-- about Fin and Nat

finnonempty : ∀ {n} (k : Fin n) → n > 0
finnonempty zero = s≤s z≤n
finnonempty (suc k) = s≤s z≤n

m+sn=sm+n : (m n : ℕ) → m + suc n ≡ suc m + n
m+sn=sm+n zero n = refl
m+sn=sm+n (suc m) n = cong suc (m+sn=sm+n m n)

n+0=n : (n : ℕ) → n + 0 ≡ n
n+0=n zero = refl
n+0=n (suc n) = cong suc (n+0=n n)

n+toNzero=n : ∀ {k} → (n : ℕ) → n + toℕ (zero{k}) ≡ n
n+toNzero=n zero = refl
n+toNzero=n {k} (suc n) = cong suc (n+toNzero=n {k} n)

minusplus : (n : ℕ) (k : Fin n) → n ∸ toℕ k + toℕ k ≡ n
minusplus zero ()
minusplus (suc n) zero rewrite n+0=n n = refl
minusplus (suc n) (suc k) rewrite m+sn=sm+n (n ∸ toℕ k) (toℕ k) = cong suc (minusplus n k)

convert : (n : ℕ) (k : Fin (suc n)) → Fin (suc n ∸ toℕ k + toℕ k) ≡ Fin (suc n)
convert n k rewrite minusplus (suc n) k = refl

coerce : ∀ {A B : Set} → A ≡ B → A → B
coerce refl x = x

-- type conversion problem #2

invert : ∀ {n} (k : Fin n) → Fin n
invert {zero} ()
invert {suc n} k = let r = inject+ (toℕ k) (n ℕ- k) in coerce (convert n k) r 

m+n-m=n : (m n : ℕ) → m ≤ n → m + (n ∸ m) ≡ n
m+n-m=n zero n z≤n = refl
m+n-m=n (suc m) (suc n) (s≤s p) = cong suc (m+n-m=n m n p)

n-m+m=n : (m n : ℕ) → m ≤ n → (n ∸ m) + m ≡ n
n-m+m=n zero zero z≤n = refl
n-m+m=n zero (suc n) z≤n = cong suc (n-m+m=n zero n z≤n)
n-m+m=n (suc m) zero ()
n-m+m=n (suc m) (suc n) (s≤s p) rewrite m+sn=sm+n (n ∸ m) m = cong suc (n-m+m=n m n p)

convert2 : ∀ {n₁ n₂} → {F : ℕ → Set} → n₁ ≤ n₂ → F (n₂ ∸ n₁ + n₁) ≡ F n₂
convert2 {n₁} {n₂} p rewrite n-m+m=n n₁ n₂ p = refl


ccsz : (n : ℕ) → (coerce (convert (suc n) zero) (suc (inject+ 0 (fromℕ n)))) ≡ suc (coerce (convert n zero) (inject+ 0 (fromℕ n)))
ccsz zero = refl
ccsz (suc n) = {!!}

n=n+0 : (n : ℕ) → n ≡ n + 0
n=n+0 zero = refl
n=n+0 (suc n) = cong suc (n=n+0 n)

m=n=>finm=finn : ∀ {m n : ℕ} → m ≡ n → Fin m ≡ Fin n
m=n=>finm=finn refl = refl

finn=n+0 : (n : ℕ) → Fin n ≡ Fin (n + 0)
finn=n+0 n = m=n=>finm=finn (n=n+0 n)

finn+0=n : (n : ℕ) → Fin (n + 0) ≡ Fin n
finn+0=n n = m=n=>finm=finn (n+0=n n)

n+k=k+n : (n k : ℕ) → n + k ≡ k + n
n+k=k+n zero k = sym (n+0=n k)
n+k=k+n (suc n) k rewrite m+sn=sm+n k n = sym (cong suc (sym (n+k=k+n n k)))

finn+k=fink+n : (n k : ℕ) → Fin (n + k) ≡ Fin (k + n)
finn+k=fink+n n k = m=n=>finm=finn (n+k=k+n n k)

finnn : (n : ℕ) → coerce (finn=n+0 (suc n)) zero ≡ zero
finnn zero with finn=n+0 1
finnn zero | refl = refl
finnn (suc n) with finn=n+0 (suc (suc n))
finnn (suc n) | p = {!!}


inject+0n : ∀ {n : ℕ} (fn : Fin n) → inject+ 0 fn ≡ coerce (finn=n+0 n) fn
inject+0n zero = {!refl!}
inject+0n (suc fn) = {!!}

--- does it matter, btw?
inv-inj : ∀ {n} → (k : Fin n) → toℕ (invert (inject₁ k)) ≡ suc (toℕ (inject₁ (invert k)))
inv-inj zero = {!!}
inv-inj (suc k) = {!!}

-- more fin injections
finnk=>finkn : ∀ {n : ℕ} (k : ℕ) → Fin (n + k) → Fin (k + n)
finnk=>finkn {n} k j rewrite n+k=k+n n k = j

≤-refl : ∀ n → n ≤ n
≤-refl zero = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

≤-trans : ∀ {k l m} → k ≤ l → l ≤ m → k ≤ m
≤-trans z≤n z≤n = z≤n
≤-trans z≤n (s≤s l≤m) = z≤n
≤-trans (s≤s k≤l) (s≤s l≤m) = s≤s (≤-trans k≤l l≤m)

n<=k+n : ∀ {n} k → n ≤ k + n
n<=k+n zero = ≤-refl _
n<=k+n {zero} (suc k) = z≤n
n<=k+n {suc n} (suc k) rewrite m+sn=sm+n k n = let p = n<=k+n {n} (suc k) in s≤s p

injectk+ : ∀ {n} k → Fin n → Fin (k + n)
injectk+ {n} k j = inject≤ j (n<=k+n {n} k)
