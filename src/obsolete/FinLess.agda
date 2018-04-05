module FinLess where

open import Data.Nat
open import Data.Product

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans z≤n z≤n = z≤n
≤-trans z≤n (s≤s n≤o) = z≤n
≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)

n<sn : ∀ {n} → n < suc n
n<sn = s≤s ≤-refl

n≤sn : ∀ {n} → n ≤ suc n
n≤sn {zero} = z≤n
n≤sn {suc n} = s≤s n≤sn
{-
n-m≤n : (n m : ℕ) → suc m ≤ n → n ∸ m ≤ n
n-m≤n .(suc _) zero (s≤s p) = ≤-refl
n-m≤n (suc n) (suc m) (s≤s p) = ≤-trans (n-m≤n n m p) n≤sn
-}
m≤n=>m<sn : ∀ {m n} → m ≤ n → m < suc n
m≤n=>m<sn z≤n = s≤s z≤n
m≤n=>m<sn (s≤s p) = s≤s (m≤n=>m<sn p)

k<n=>k≤n : ∀ {k n} → k < n → k ≤ n
k<n=>k≤n (s≤s p) = ≤-trans p n≤sn

lemma-invert : (n m : ℕ) → m < n → (n ∸ 1 ∸ m) < n
lemma-invert (suc n) .0 (s≤s z≤n) = n<sn
lemma-invert (suc (suc n)) (suc m) (s≤s (s≤s p)) = s≤s (k<n=>k≤n (lemma-invert (suc n) m (s≤s p)))

-- inversion function with explicit proof that result is in range
invert≤ : ∀ (n m : ℕ) → m < n → Σ ℕ λ m' → m' < n
invert≤ n m m<n =  n ∸ 1 ∸ m , lemma-invert n m m<n
