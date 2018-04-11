module Channel where

open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Product
-- open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Global


-- the main part of a channel endpoint value is a valid channel reference
-- the boolean determines whether it's the front end or the back end of the channel
-- enforces that the session context has only one channel
data ValidChannelRef : (G : SCtx) (b : Bool) (s : STy) → Set where
  here-pos : ∀ {s} {G : SCtx}
    → (ina-G : Inactive G)
    → ValidChannelRef (just (s , POS) ∷ G) true s
  here-neg : ∀ {s} {G : SCtx}
    → (ina-G : Inactive G)
    → ValidChannelRef (just (s , NEG) ∷ G) false (dual s)
  there : ∀ {b s} {G : SCtx}
    → (vcr : ValidChannelRef G b s)
    → ValidChannelRef (nothing ∷ G) b s

-- find matching wait instruction in thread pool
vcr-match : ∀ {G G₁ G₂ b₁ b₂ s₁ s₂}
  → SSplit G G₁ G₂
  → ValidChannelRef G₁ b₁ s₁
  → ValidChannelRef G₂ b₂ s₂
  → Maybe (b₁ ≡ not b₂ × s₁ ≡ dual s₂)
vcr-match () (here-pos ina-G) (here-pos ina-G₁)
vcr-match (ss-posneg ss) (here-pos ina-G) (here-neg ina-G₁) = just (refl , sym (dual-involution _))
vcr-match (ss-left ss) (here-pos ina-G) (there vcr2) = nothing
vcr-match (ss-negpos ss) (here-neg ina-G) (here-pos ina-G₁) = just (refl , refl)
vcr-match (ss-left ss) (here-neg ina-G) (there vcr2) = nothing
vcr-match (ss-right ss) (there vcr1) (here-pos ina-G) = nothing
vcr-match (ss-right ss) (there vcr1) (here-neg ina-G) = nothing
vcr-match (ss-both ss) (there vcr1) (there vcr2) = vcr-match ss vcr1 vcr2

vcr-there : ∀ {G' G₁' G₂' b₁ b₂ s₁ s₂}
  → SSplit G' G₁' G₂' × ValidChannelRef G₁' b₁ s₁ × ValidChannelRef G₂' b₂ s₂
  → SSplit (nothing ∷ G') (nothing ∷ G₁') (nothing ∷ G₂') × ValidChannelRef (nothing ∷ G₁') b₁ s₁ × ValidChannelRef (nothing ∷ G₂') b₂ s₂
vcr-there (ss , vcr1 , vcr2) = (ss-both ss) , ((there vcr1) , (there vcr2))

-- find matching send instruction in thread pool
vcr-match-sr : ∀ {G G₁ G₂ b₁ b₂ s₁ s₂ t₁ t₂}
  → SSplit G G₁ G₂
  → ValidChannelRef G₁ b₁ (SRecv t₁ s₁)
  → ValidChannelRef G₂ b₂ (SSend t₂ s₂)
  → Maybe (t₁ ≡ t₂ ×
          dual s₁ ≡ s₂ ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₂' →
          SSplit G' G₁' G₂' ×
          ValidChannelRef G₁' b₁ s₁ ×
          ValidChannelRef G₂' b₂ s₂)
vcr-match-sr ss-[] () vcr-send
vcr-match-sr (ss-both ss) (there vcr-recv) (there vcr-send) with vcr-match-sr ss vcr-recv vcr-send
vcr-match-sr (ss-both ss) (there vcr-recv) (there vcr-send) | just (t₁≡t₂ , s₁≡ds₂ , G , G₁ , G₂ , x) = just (t₁≡t₂ , s₁≡ds₂ , nothing ∷ G , nothing ∷ G₁ , nothing ∷ G₂ , vcr-there x)
vcr-match-sr (ss-both ss) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-sr (ss-left ss) vcr-recv vcr-send = nothing
vcr-match-sr (ss-right ss) vcr-recv vcr-send = nothing
vcr-match-sr {just (SRecv t s , POSNEG) ∷ G} {just _ ∷ G₁} {just _ ∷ G₂} (ss-posneg ss) (here-pos ina-G₁) (here-neg ina-G₂) =
  just (refl , refl , just (s , POSNEG) ∷ G , just (s , POS) ∷ G₁ , just (s , NEG) ∷ G₂ , ss-posneg ss , here-pos ina-G₁ , here-neg ina-G₂)
vcr-match-sr {just (SSend t s , POSNEG) ∷ G} {just _ ∷ G₁} {just _ ∷ G₂} (ss-negpos ss) (here-neg ina-G₁) (here-pos ina-G₂) =
  just (refl , dual-involution s , just (s , POSNEG) ∷ G , just (s , NEG) ∷ G₁ , just (s , POS) ∷ G₂ , ss-negpos ss , (here-neg ina-G₁) , here-pos ina-G₂)

{-
data SSplitPath' (G : SCtx) : (G' : SCtx) → Set where
  base : SSplitPath' G G
  step : ∀ {G₁ G₂ G'}
    → (ss : SSplit G G₁ G₂)
    → (path : SSplitPath' G₁ G')
    → SSplitPath' G G'

ssplitpath'-[] : ∀ { G'} → SSplitPath' [] G' → G' ≡ []
ssplitpath'-[] base = refl
ssplitpath'-[] (step ss-[] path) = ssplitpath'-[] path

ssplitpath'-:: : ∀ {x G G'}
  → SSplitPath' (x ∷ G) G'
  → Σ SEntry λ x' → Σ SCtx λ G'' → G' ≡ x' ∷ G''
ssplitpath'-:: base = _ , _ , refl
ssplitpath'-:: (step (ss-both ss) path) = ssplitpath'-:: path
ssplitpath'-:: (step (ss-left ss) path) = ssplitpath'-:: path
ssplitpath'-:: (step (ss-right ss) path) = ssplitpath'-:: path
ssplitpath'-:: (step (ss-posneg ss) path) = ssplitpath'-:: path
ssplitpath'-:: (step (ss-negpos ss) path) = ssplitpath'-:: path


data SSplitPath (G G₁ G₂ : SCtx) : Set where
  base :
    (ss : SSplit G G₁ G₂)
    → SSplitPath G G₁ G₂
  step : ∀ {G₁' G₂'}
    → (ss : SSplit G G₁' G₂')
    → (path : SSplitPath G₁' G₁ G₂)
    → SSplitPath G G₁ G₂

splitpath-impossible-1 : ∀ {x G G₁ G₂} → SSplitPath (x ∷ G) G₁ G₂ → ¬ (G₁ ≡ []) × ¬ (G₂ ≡ [])
splitpath-impossible-1 (base (ss-both ss)) = (λ ()) , (λ ())
splitpath-impossible-1 (base (ss-left ss)) = (λ ()) , (λ ())
splitpath-impossible-1 (base (ss-right ss)) = (λ ()) , (λ ())
splitpath-impossible-1 (base (ss-posneg ss)) = (λ ()) , (λ ())
splitpath-impossible-1 (base (ss-negpos ss)) = (λ ()) , (λ ())
splitpath-impossible-1 (step (ss-both ss) path) = splitpath-impossible-1 path
splitpath-impossible-1 (step (ss-left ss) path) = splitpath-impossible-1 path
splitpath-impossible-1 (step (ss-right ss) path) = splitpath-impossible-1 path
splitpath-impossible-1 (step (ss-posneg ss) path) = splitpath-impossible-1 path
splitpath-impossible-1 (step (ss-negpos ss) path) = splitpath-impossible-1 path

splitpath-[] : ∀ {G₁ G₂} → SSplitPath [] G₁ G₂ → G₁ ≡ [] × G₂ ≡ []
splitpath-[] (base ss-[]) = refl , refl
splitpath-[] (step ss-[] path) = splitpath-[] path

splitpath-nothing : ∀ {G G₁ G₂} → SSplitPath (nothing ∷ G) G₁ G₂
  → Σ SCtx λ G₁' → Σ SCtx λ G₂' → G₁ ≡ nothing ∷ G₁' × G₂ ≡ nothing ∷ G₂'
splitpath-nothing (base (ss-both ss)) = _ , _ , refl , refl
splitpath-nothing (step (ss-both ss) path) = splitpath-nothing path

splitpath-strip-nothing : ∀ {G G₁ G₂} 
  → SSplitPath (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂)
  → SSplitPath G G₁ G₂
splitpath-strip-nothing (base (ss-both ss)) = base ss
splitpath-strip-nothing (step (ss-both ss) path) = step ss (splitpath-strip-nothing path)

splitpath-add-nothing : ∀ {G G₁ G₂} 
  → SSplitPath G G₁ G₂
  → SSplitPath (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂)
splitpath-add-nothing (base ss) = base (ss-both ss)
splitpath-add-nothing (step ss path) = step (ss-both ss) (splitpath-add-nothing path)

  
vcr-match-path-sr : ∀ {G G₁ G₂ b₁ b₂ s₁ s₂ t₁ t₂}
  → SSplitPath G G₁ G₂
  → ValidChannelRef G₁ b₁ (SRecv t₁ s₁)
  → ValidChannelRef G₂ b₂ (SSend t₂ s₂)
  → Maybe (t₁ ≡ t₂ ×
          dual s₁ ≡ s₂ ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₂' →
          SSplitPath G' G₁' G₂' ×
          ValidChannelRef G₁' b₁ s₁ ×
          ValidChannelRef G₂' b₂ s₂)
vcr-match-path-sr {[]} path vcr-recv vcr-send with splitpath-[] path
vcr-match-path-sr {[]} path () vcr-send | refl , refl
vcr-match-path-sr {nothing ∷ G} path vcr-recv vcr-send with splitpath-nothing path
vcr-match-path-sr {nothing ∷ G} path (there vcr-recv) (there vcr-send) | G₁' , G₂' , refl , refl with vcr-match-path-sr (splitpath-strip-nothing path) vcr-recv vcr-send
vcr-match-path-sr {nothing ∷ G} path (there vcr-recv) (there vcr-send) | G₁' , G₂' , refl , refl | just (t1=t2 , ds1=s2 , GR , GR1 , GR2 , path' , vcr-recv' , vcr-send') = just (t1=t2 , ds1=s2 , nothing ∷ GR , nothing ∷ GR1 , nothing ∷ GR2 , splitpath-add-nothing path' , there vcr-recv' , there vcr-send')
vcr-match-path-sr {nothing ∷ G} path (there vcr-recv) (there vcr-send) | G₁' , G₂' , refl , refl | nothing = nothing
vcr-match-path-sr {just (.(SRecv _ _) , POS) ∷ G} (base (ss-left ss)) (here-pos ina-G) vcr-send = nothing
vcr-match-path-sr {just (.(SSend _ _) , POS) ∷ G} (base (ss-right ss)) vcr-recv (here-pos ina-G) = nothing
vcr-match-path-sr {just (s , POS) ∷ G} {[]} (step (ss-left ss) path) vcr-recv vcr-send = {!!}
vcr-match-path-sr {just (s , POS) ∷ G}{G₁}{G₂} (step (ss-left ss) path) vcr-recv vcr-send with splitpath-impossible-1 path
vcr-match-path-sr {just (s , POS) ∷ G} {[]} {G₂} (step (ss-left ss) path) vcr-recv vcr-send | proj₃ , proj₄ with proj₃ refl
vcr-match-path-sr {just (s , POS) ∷ G} {[]} {G₂} (step (ss-left ss) path) vcr-recv vcr-send | proj₃ , proj₄ | ()
vcr-match-path-sr {just (s , POS) ∷ G} {x ∷ G₁} {[]} (step (ss-left ss) path) vcr-recv vcr-send | proj₃ , proj₄ with proj₄ refl
vcr-match-path-sr {just (s , POS) ∷ G} {x ∷ G₁} {[]} (step (ss-left ss) path) vcr-recv vcr-send | proj₃ , proj₄ | ()
vcr-match-path-sr {just (s , POS) ∷ G} {x ∷ G₁} {x₁ ∷ G₂} (step (ss-left ss) path) vcr-recv vcr-send | res = {!!}
vcr-match-path-sr {just (s , POS) ∷ G}{G₁}{G₂} (step (ss-right ss) path) vcr-recv vcr-send with splitpath-impossible-1 path
vcr-match-path-sr {just (s , POS) ∷ G} {[]} {G₂} (step (ss-right ss) path) vcr-recv vcr-send | proj₃ , proj₄ with proj₃ refl
vcr-match-path-sr {just (s , POS) ∷ G} {[]} {G₂} (step (ss-right ss) path) vcr-recv vcr-send | proj₃ , proj₄ | ()
vcr-match-path-sr {just (s , POS) ∷ G} {x ∷ G₁} {[]} (step (ss-right ss) path) vcr-recv vcr-send | proj₃ , proj₄ with proj₄ refl
vcr-match-path-sr {just (s , POS) ∷ G} {x ∷ G₁} {[]} (step (ss-right ss) path) vcr-recv vcr-send | proj₃ , proj₄ | ()
vcr-match-path-sr {just (s , POS) ∷ G} {just x ∷ G₁} {x₁ ∷ G₂} (step (ss-right ss) path) vcr-recv vcr-send | proj₃ , proj₄ = {!!}
vcr-match-path-sr {just (s , POS) ∷ G} {nothing ∷ G₁} {x₁ ∷ G₂} (step (ss-right ss) path) vcr-recv vcr-send | proj₃ , proj₄ = {!!}
vcr-match-path-sr {just (s , NEG) ∷ G} path vcr-recv vcr-send = {!!}
vcr-match-path-sr {just (s , POSNEG) ∷ G} path vcr-recv vcr-send = {!!}
-}

-- ok. brute force for a fixed tree with three levels
data SSplit2 (G G₁ G₂ G₁₁ G₁₂ : SCtx) : Set where
  ssplit2 : 
    (ss1 : SSplit G G₁ G₂)
    → (ss2 : SSplit G₁ G₁₁ G₁₂)
    → SSplit2 G G₁ G₂ G₁₁ G₁₂

vcr-match-2-sr : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ s₁ s₂ t₁ t₂}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ValidChannelRef G₁₁ b₁ (SRecv t₁ s₁)
  → ValidChannelRef G₁₂ b₂ (SSend t₂ s₂)
  → Maybe (t₁ ≡ t₂ ×
          dual s₁ ≡ s₂ ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₁₁' → Σ SCtx λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ValidChannelRef G₁₁' b₁ s₁ ×
          ValidChannelRef G₁₂' b₂ s₂)
vcr-match-2-sr (ssplit2 ss-[] ss-[]) vcr-recv ()
vcr-match-2-sr (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) with vcr-match-2-sr (ssplit2 ss1 ss2) vcr-recv vcr-send
vcr-match-2-sr (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , GG' , GG1' , GG11' , GG12' , ssplit2 ss3 ss4 , vcr-recv' , vcr-send') = just (t1=t2 , ds1=s2 , _ , _ , _ , _ , ssplit2 (ss-both ss3) (ss-both ss4) ,  there vcr-recv' , there vcr-send')
vcr-match-2-sr (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-2-sr {G₁ = just (.(SRecv _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (SSend x s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (SRecv x s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (.(SSend _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) (here-pos ina-G) = nothing
vcr-match-2-sr {G₁ = just (SSend x s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SRecv x s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) (here-neg ina-G) = nothing
vcr-match-2-sr {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) = just (refl , (refl , (_ , _ , _ , _ , (ssplit2 (ss-left ss1) (ss-posneg ss2)) , ((here-pos ina-G) , (here-neg ina-G₁)))))
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G₁) (here-pos ina-G) = just (refl , dual-involution _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , (here-neg ina-G₁) , (here-pos ina-G))
vcr-match-2-sr (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) with vcr-match-2-sr (ssplit2 ss1 ss2) vcr-recv vcr-send
vcr-match-2-sr (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | just  (t1=t2 , ds1=s2 , GG' , GG1' , GG11' , GG12' , ssplit2 ss3 ss4 , vcr-recv' , vcr-send') = just (t1=t2 , ds1=s2 , _ , _ , _ , _ , ssplit2 (ss-right ss3) (ss-both ss4) , there vcr-recv' , there vcr-send')
vcr-match-2-sr (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-2-sr (ssplit2 (ss-posneg ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-send) = nothing
vcr-match-2-sr (ssplit2 (ss-posneg ss1) (ss-right ss2)) (there vcr-recv) (here-pos ina-G) = nothing
vcr-match-2-sr {G₁ = just (SSend x s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (SRecv x s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SSend x s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SRecv x s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) (here-neg ina-G) = nothing
vcr-match-2-sr {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()

-- -- ok. brute force for a fixed tree with three levels
-- data SSplit3 (G G₁ G₂ G₁₁ G₁₂ G₁₁₁ G₁₁₂ : SCtx) : Set where
--   ssplit3 : 
--     (ss1 : SSplit G G₁ G₂)
--     → (ss2 : SSplit G₁ G₁₁ G₁₂)
--     → (ss3 : SSplit G₁₁ G₁₁₁ G₁₁₂)
--     → SSplit3 G G₁ G₂ G₁₁ G₁₂ G₁₁₁ G₁₁₂

-- ss3-both : ∀ {G G₁ G₂ G₁₁ G₁₂ G₁₁₁ G₁₁₂}
--   → SSplit3 G G₁ G₂ G₁₁ G₁₂ G₁₁₁ G₁₁₂
--   → SSplit3 (nothing ∷ G) (nothing ∷ G₁) (nothing ∷  G₂) (nothing ∷  G₁₁) (nothing ∷  G₁₂) (nothing ∷  G₁₁₁) (nothing ∷  G₁₁₂)
-- ss3-both (ssplit3 ss1 ss2 ss3) = ssplit3 (ss-both ss1) (ss-both ss2) (ss-both ss3)

-- vcr-match-3-sr : ∀ {G G₁ G₂ G₁₁ G₁₂ G₁₁₁ G₁₁₂ b₁ b₂ s₁ s₂ t₁ t₂}
--   → SSplit3 G G₁ G₂ G₁₁ G₁₂ G₁₁₁ G₁₁₂
--   → ValidChannelRef G₁₁₁ b₁ (SRecv t₁ s₁)
--   → ValidChannelRef G₁₁₂ b₂ (SSend t₂ s₂)
--   → Maybe (t₁ ≡ t₂ ×
--           dual s₁ ≡ s₂ ×
--           Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₁₁' →
--           Σ SCtx λ G₁₁₁' → Σ SCtx λ G₁₁₂' →
--           SSplit3 G' G₁' G₂ G₁₁' G₁₂ G₁₁₁' G₁₁₂' ×
--           ValidChannelRef G₁₁₁' b₁ s₁ ×
--           ValidChannelRef G₁₁₂' b₂ s₂)
-- vcr-match-3-sr (ssplit3 ss-[] ss-[] ss-[]) () vcr-send
-- vcr-match-3-sr (ssplit3 (ss-both ss1) (ss-both ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) with vcr-match-3-sr (ssplit3 ss1 ss2 ss3) vcr-recv vcr-send
-- vcr-match-3-sr (ssplit3 (ss-both ss1) (ss-both ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , G' , G₁' , G₁₁' , G₁₁₁' , G₁₁₂' , ss3' , vcr-recv' , vcr-send') = just (t1=t2 , (ds1=s2 , (nothing ∷ G' , (nothing ∷ G₁') , ((nothing ∷ G₁₁') , ((nothing ∷ G₁₁₁') , ((nothing ∷ G₁₁₂') , (ss3-both ss3') , ((there vcr-recv') , (there vcr-send'))))))))
-- vcr-match-3-sr (ssplit3 (ss-both ss1) (ss-both ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | nothing = nothing
-- vcr-match-3-sr {G₁₁ = just (.(SRecv _ _) , POS) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-left ss3)) (here-pos ina-G) (there vcr-send) = nothing
-- vcr-match-3-sr {G₁₁ = just (SSend x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-left ss3)) (here-neg ina-G) (there vcr-send) = nothing
-- vcr-match-3-sr {G₁₁ = just (SRecv x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-left ss3)) () vcr-send
-- vcr-match-3-sr {G₁₁ = just (SEnd! , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-left ss3)) () vcr-send
-- vcr-match-3-sr {G₁₁ = just (SEnd? , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-left ss3)) () vcr-send
-- vcr-match-3-sr {G₁₁ = just (s , POSNEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-left ss3)) () vcr-send
-- vcr-match-3-sr {G₁₁ = just (.(SSend _ _) , POS) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) (here-pos ina-G) = nothing
-- vcr-match-3-sr {G₁₁ = just (SSend x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr {G₁₁ = just (SRecv x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) (here-neg ina-G) = nothing
-- vcr-match-3-sr {G₁₁ = just (SEnd! , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr {G₁₁ = just (SEnd? , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr {G₁₁ = just (s , POSNEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr (ssplit3 (ss-left ss1) (ss-left ss2) (ss-posneg ss3)) (here-pos ina-G) (here-neg ina-G₁) = just (refl , (refl , (_ , _ , (_ , (_ , (_ , ((ssplit3 (ss-left ss1) (ss-left ss2) (ss-posneg ss3)) , (here-pos ina-G) , (here-neg ina-G₁))))))))
-- vcr-match-3-sr {G₁₁ = just (SSend x s , POSNEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-negpos ss3)) (here-neg ina-G) (here-pos ina-G₁) = just (refl , ((dual-involution s) , _ , (_ , (_ , (_ , (_ , ((ssplit3 (ss-left ss1) (ss-left ss2) (ss-negpos ss3)) , (here-neg ina-G) , (here-pos ina-G₁))))))))
-- vcr-match-3-sr {G₁₁ = just (SRecv x s , POSNEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-negpos ss3)) () vcr-send
-- vcr-match-3-sr {G₁₁ = just (SEnd! , POSNEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-negpos ss3)) () vcr-send
-- vcr-match-3-sr {G₁₁ = just (SEnd? , POSNEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-left ss2) (ss-negpos ss3)) () vcr-send
-- vcr-match-3-sr (ssplit3 (ss-left ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) with vcr-match-3-sr (ssplit3 ss1 ss2 ss3) vcr-recv vcr-send
-- vcr-match-3-sr (ssplit3 (ss-left ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , G' , G₁' , G₁₁' , G₁₁₁' , G₁₁₂' , ssplit3 ss4 ss5 ss6 , vcr-recv' , vcr-send') = just (t1=t2 , (ds1=s2 , (_ , (_ , (_ , (_ , (_ , (ssplit3 (ss-left ss4) (ss-right ss5) (ss-both ss6) , there vcr-recv' , there vcr-send'))))))))
-- vcr-match-3-sr (ssplit3 (ss-left ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | nothing = nothing
-- vcr-match-3-sr (ssplit3 (ss-left ss1) (ss-posneg ss2) (ss-left ss3)) (here-pos ina-G) (there vcr-send) = nothing
-- vcr-match-3-sr (ssplit3 (ss-left ss1) (ss-posneg ss2) (ss-right ss3)) (there vcr-recv) (here-pos ina-G) = nothing
-- vcr-match-3-sr {G₁₁ = just (SSend x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-left ss3)) (here-neg ina-G) (there vcr-send) = nothing
-- vcr-match-3-sr {G₁₁ = just (SRecv x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-left ss3)) () (there vcr-send)
-- vcr-match-3-sr {G₁₁ = just (SEnd! , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-left ss3)) () (there vcr-send)
-- vcr-match-3-sr {G₁₁ = just (SEnd? , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-left ss3)) () (there vcr-send)
-- vcr-match-3-sr {G₁₁ = just (SSend x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr {G₁₁ = just (SRecv x s , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-right ss3)) (there vcr-recv) (here-neg ina-G) = nothing
-- vcr-match-3-sr {G₁₁ = just (SEnd! , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr {G₁₁ = just (SEnd? , NEG) ∷ G₁₁} (ssplit3 (ss-left ss1) (ss-negpos ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr (ssplit3 (ss-right ss1) (ss-both ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) with vcr-match-3-sr (ssplit3 ss1 ss2 ss3) vcr-recv vcr-send
-- vcr-match-3-sr (ssplit3 (ss-right ss1) (ss-both ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , G' , G₁' , G₁₁' , G₁₁₁' , G₁₁₂' , ssplit3 ss4 ss5 ss6 , vcr-recv' , vcr-send') = just (t1=t2 , (ds1=s2 , (_ , (_ , (_ , (_ , (_ , ((ssplit3 (ss-right ss4) (ss-both ss5) (ss-both ss6)) , (there vcr-recv' , there vcr-send')))))))))
-- vcr-match-3-sr (ssplit3 (ss-right ss1) (ss-both ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | nothing = nothing
-- vcr-match-3-sr (ssplit3 (ss-posneg ss1) (ss-left ss2) (ss-left ss3)) (here-pos ina-G) (there vcr-send) = nothing
-- vcr-match-3-sr (ssplit3 (ss-posneg ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) (here-pos ina-G) = nothing
-- vcr-match-3-sr (ssplit3 (ss-posneg ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) with vcr-match-3-sr (ssplit3 ss1 ss2 ss3) vcr-recv vcr-send
-- vcr-match-3-sr (ssplit3 (ss-posneg ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , G' , G₁' , G₁₁' , G₁₁₁' , G₁₁₂' , ssplit3 ss4 ss5 ss6 , vcr-recv' , vcr-send') = just (t1=t2 , (ds1=s2 , (_ , (_ , (_ , (_ , (_ , (ssplit3 (ss-posneg ss4) (ss-right ss5) (ss-both ss6) , there vcr-recv' , there vcr-send'))))))))
-- vcr-match-3-sr (ssplit3 (ss-posneg ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | nothing = nothing
-- vcr-match-3-sr {G₁₁ = just (SSend x s , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-left ss3)) (here-neg ina-G) (there vcr-send) = nothing
-- vcr-match-3-sr {G₁₁ = just (SRecv x s , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-left ss3)) () (there vcr-send)
-- vcr-match-3-sr {G₁₁ = just (SEnd! , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-left ss3)) () (there vcr-send)
-- vcr-match-3-sr {G₁₁ = just (SEnd? , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-left ss3)) () (there vcr-send)
-- vcr-match-3-sr {G₁₁ = just (SSend x s , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr {G₁₁ = just (SRecv x s , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) (here-neg ina-G) = nothing
-- vcr-match-3-sr {G₁₁ = just (SEnd! , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr {G₁₁ = just (SEnd? , NEG) ∷ G₁₁} (ssplit3 (ss-negpos ss1) (ss-left ss2) (ss-right ss3)) (there vcr-recv) ()
-- vcr-match-3-sr (ssplit3 (ss-negpos ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) with vcr-match-3-sr (ssplit3 ss1 ss2 ss3) vcr-recv vcr-send
-- vcr-match-3-sr (ssplit3 (ss-negpos ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , G' , G₁' , G₁₁' , G₁₁₁' , G₁₁₂' , ssplit3 ss4 ss5 ss6 , vcr-recv' , vcr-send') = just (t1=t2 , (ds1=s2 , (_ , (_ , (_ , (_ , (_ , (ssplit3 (ss-negpos ss4) (ss-right ss5) (ss-both ss6) , there vcr-recv' , there vcr-send'))))))))
-- vcr-match-3-sr (ssplit3 (ss-negpos ss1) (ss-right ss2) (ss-both ss3)) (there vcr-recv) (there vcr-send) | nothing = nothing
