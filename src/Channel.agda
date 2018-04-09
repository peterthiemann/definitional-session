module Channel where

open import Data.Bool
open import Data.List
open import Data.Maybe
open import Data.Product
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
