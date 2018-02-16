module Lemmas where

open import Data.Fin hiding (_+_)
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

invert : ∀ {n} (k : Fin n) → Fin n
invert {zero} ()
invert {suc n} k = let r = inject+ (toℕ k) (n ℕ- k) in coerce (convert n k) r 

