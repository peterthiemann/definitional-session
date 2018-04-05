module Snippet where

coerce : {A B : Set} → A ≡ B → A → B
coerce refl a = a

vec-cong : ∀ {m n} { A : Set} (x : A) → (xs : Vec A m) (ys : Vec A n) → xs ≅ ys → x ∷ xs ≅ x ∷ ys
vec-cong x xs ys p = {!p!}

appempty : ∀ {m} → (H : Vec STy m) → H ++ [] ≅ H
appempty [] = refl
appempty (x ∷ H) = {!!}
revapp : ∀ {m n} → (G : Vec STy n) → (H : Vec STy m) → reverse (H ++ G) ≅ reverse G ++ reverse H
revapp [] H = {!!}
revapp (x ∷ G) H = {!!}

liftVal'' : ∀ { n m t} →  (G : Vec STy n) (H : Vec STy m) → Val'' G t → Val'' (H ++ G) t
liftVal'' {n} {m} G H (VChan i) = VChan {!!}
