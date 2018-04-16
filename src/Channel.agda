module Channel where

open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Product
-- open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Syntax
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
vcr-match-2-sr (ssplit2 ss-[] ss-[]) () vcr-send
vcr-match-2-sr (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) with vcr-match-2-sr (ssplit2 ss1 ss2) vcr-recv vcr-send
vcr-match-2-sr (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , GG' , GG1' , GG11' , GG12' , ssplit2 ss3 ss4 , vcr-recv' , vcr-send') = just (t1=t2 , ds1=s2 , _ , _ , _ , _ , ssplit2 (ss-both ss3) (ss-both ss4) ,  there vcr-recv' , there vcr-send')
vcr-match-2-sr (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-2-sr {G₁ = just (.(SRecv _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (.(SSend _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) (here-pos ina-G) = nothing
vcr-match-2-sr {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) (here-neg ina-G) = nothing
vcr-match-2-sr {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) = just (refl , (refl , (_ , _ , _ , _ , (ssplit2 (ss-left ss1) (ss-posneg ss2)) , ((here-pos ina-G) , (here-neg ina-G₁)))))
vcr-match-2-sr {G₁ = just (SSend t s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G) (here-pos ina-G₁) = just (refl , dual-involution _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , (here-neg ina-G) , (here-pos ina-G₁))
vcr-match-2-sr {G₁ = just (SRecv t s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SIntern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SExtern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SEnd! , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SEnd? , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-send
vcr-match-2-sr (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) with vcr-match-2-sr (ssplit2 ss1 ss2) vcr-recv vcr-send
vcr-match-2-sr (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | just  (t1=t2 , ds1=s2 , GG' , GG1' , GG11' , GG12' , ssplit2 ss3 ss4 , vcr-recv' , vcr-send') = just (t1=t2 , ds1=s2 , _ , _ , _ , _ , ssplit2 (ss-right ss3) (ss-both ss4) , there vcr-recv' , there vcr-send')
vcr-match-2-sr (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-2-sr (ssplit2 (ss-posneg ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-send) = nothing
vcr-match-2-sr (ssplit2 (ss-posneg ss1) (ss-right ss2)) (there vcr-recv) (here-pos ina-G) = nothing
vcr-match-2-sr {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-send
vcr-match-2-sr {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) (here-neg ina-G) = nothing
vcr-match-2-sr {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
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

vcr-match-2-sb : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ s₁₁ s₁₂ s₂₁ s₂₂}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ValidChannelRef G₁₁ b₁ (SIntern s₁₁ s₁₂)
  → ValidChannelRef G₁₂ b₂ (SExtern s₂₁ s₂₂)
  → (lab : Selector)
  → Maybe (dual s₁₁ ≡ s₂₁ ×
          dual s₁₂ ≡ s₂₂ ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₁₁' → Σ SCtx λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ValidChannelRef G₁₁' b₁ (selection lab s₁₁ s₁₂) ×
          ValidChannelRef G₁₂' b₂ (selection lab s₂₁ s₂₂))
vcr-match-2-sb (ssplit2 ss-[] ss-[]) () vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab with vcr-match-2-sb (ssplit2 ss1 ss2) vcr-int vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | just (ds11=s21 , ds12=s22 , G' , G₁' , G₁₁' , G₁₂' , ssplit2 ss1' ss2' , vcr-int' , vcr-ext') = just (ds11=s21 , ds12=s22 , _ , _ , _ , _ , ssplit2 (ss-both ss1') (ss-both ss2') , there vcr-int' , there vcr-ext')
vcr-match-2-sb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | nothing = nothing
vcr-match-2-sb {G₁ = just (.(SIntern _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (.(SExtern _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) (here-pos ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) (here-neg ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) Left = just (refl , refl , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-posneg ss2) , here-pos ina-G ,  here-neg ina-G₁)
vcr-match-2-sb (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) Right = just (refl , refl , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-posneg ss2) , here-pos ina-G ,  here-neg ina-G₁)
vcr-match-2-sb {G₁ = just (SSend t s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SRecv t s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SIntern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SExtern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G) (here-pos ina-G₁) Left = just (dual-involution _ , dual-involution _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , (here-neg ina-G) , here-pos ina-G₁)
vcr-match-2-sb {G₁ = just (SExtern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G) (here-pos ina-G₁) Right = just (dual-involution _ , dual-involution _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , (here-neg ina-G) , here-pos ina-G₁)
vcr-match-2-sb {G₁ = just (SEnd! , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SEnd? , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab with vcr-match-2-sb (ssplit2 ss1 ss2) vcr-int vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | just (ds11=s21 , ds12=s22 , G' , G₁' , G₁₁' , G₁₂' , ssplit2 ss1' ss2' , vcr-int' , vcr-ext') = just (ds11=s21 , (ds12=s22 , _ , _ , _ , _ , ssplit2 (ss-right ss1') (ss-both ss2') , there vcr-int' , there vcr-ext'))
vcr-match-2-sb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | nothing = nothing
vcr-match-2-sb (ssplit2 (ss-posneg ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb (ssplit2 (ss-posneg ss1) (ss-right ss2)) (there vcr-int) (here-pos ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (SSend t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SRecv t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SIntern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) (here-neg ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (SExtern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SEnd! , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (SEnd? , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
