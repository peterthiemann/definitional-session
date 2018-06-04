module Channel where

open import Data.Bool
open import Data.Fin
open import Data.List hiding (map)
open import Data.Maybe
open import Data.Product hiding (map)
-- open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global


-- the main part of a channel endpoint value is a valid channel reference
-- the boolean determines whether it's the front end or the back end of the channel
-- enforces that the session context has only one channel
data ValidChannelRef : (G : SCtx) (b : Bool) (s : STypeF SType) → Set where
  here-pos : ∀ {s} {G : SCtx}
    → (ina-G : Inactive G)
    → ValidChannelRef (just (s , POS) ∷ G) true s
  here-neg : ∀ {s} {G : SCtx}
    → (ina-G : Inactive G)
    → ValidChannelRef (just (s , NEG) ∷ G) false (dualF s)
  there : ∀ {b s} {G : SCtx}
    → (vcr : ValidChannelRef G b s)
    → ValidChannelRef (nothing ∷ G) b s

-- find matching wait instruction in thread pool
vcr-match : ∀ {G G₁ G₂ b₁ b₂ s₁ s₂}
  → SSplit G G₁ G₂
  → ValidChannelRef G₁ b₁ s₁
  → ValidChannelRef G₂ b₂ s₂
  → Maybe (b₁ ≡ not b₂ × s₁ ≈' dualF s₂)
vcr-match () (here-pos ina-G) (here-pos ina-G₁)
vcr-match (ss-posneg ss) (here-pos ina-G) (here-neg ina-G₁) = just (refl , dual-involutionF _)
vcr-match (ss-left ss) (here-pos ina-G) (there vcr2) = nothing
vcr-match (ss-negpos ss) (here-neg ina-G) (here-pos ina-G₁) = just (refl , equivF-refl _)
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
  → ValidChannelRef G₁ b₁ (recv t₁ s₁)
  → ValidChannelRef G₂ b₂ (send t₂ s₂)
  → Maybe (t₁ ≡ t₂ × s₁ ≈ dual s₂ ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₂' →
          SSplit G' G₁' G₂' ×
          ValidChannelRef G₁' b₁ (SType.force s₁) ×
          ValidChannelRef G₂' b₂ (SType.force s₂))
vcr-match-sr ss-[] () vcr-send
vcr-match-sr (ss-both ss) (there vcr-recv) (there vcr-send) with vcr-match-sr ss vcr-recv vcr-send
vcr-match-sr (ss-both ss) (there vcr-recv) (there vcr-send) | just (t₁≡t₂ , s₁≡ds₂ , G , G₁ , G₂ , x) = just (t₁≡t₂ , s₁≡ds₂ , nothing ∷ G , nothing ∷ G₁ , nothing ∷ G₂ , vcr-there x)
vcr-match-sr (ss-both ss) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-sr (ss-left ss) vcr-recv vcr-send = nothing
vcr-match-sr (ss-right ss) vcr-recv vcr-send = nothing
vcr-match-sr {just (recv t s , POSNEG) ∷ G} {just _ ∷ G₁} {just _ ∷ G₂} (ss-posneg ss) (here-pos ina-G₁) (here-neg ina-G₂) =
  just (refl , dual-involution _ , just (_ , POSNEG) ∷ G , just (_ , POS) ∷ G₁ , just (_ , NEG) ∷ G₂ , ss-posneg ss , here-pos ina-G₁ , here-neg ina-G₂ )
vcr-match-sr {just (send t s , POSNEG) ∷ G} {just _ ∷ G₁} {just _ ∷ G₂} (ss-negpos ss) (here-neg ina-G₁) (here-pos ina-G₂) =
  just (refl , equiv-refl _ , just (_ , POSNEG) ∷ G , just (_ , NEG) ∷ G₁ , just (_ , POS) ∷ G₂ , ss-negpos ss , here-neg ina-G₁ , here-pos ina-G₂)


-- ok. brute force for a fixed tree with three levels
data SSplit2 (G G₁ G₂ G₁₁ G₁₂ : SCtx) : Set where
  ssplit2 : 
    (ss1 : SSplit G G₁ G₂)
    → (ss2 : SSplit G₁ G₁₁ G₁₂)
    → SSplit2 G G₁ G₂ G₁₁ G₁₂

vcr-match-2-sr : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ s₁ s₂ t₁ t₂}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ValidChannelRef G₁₁ b₁ (recv t₁ s₁)
  → ValidChannelRef G₁₂ b₂ (send t₂ s₂)
  → Maybe (t₁ ≡ t₂ × s₁ ≈ dual s₂ ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₁₁' → Σ SCtx λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ValidChannelRef G₁₁' b₁ (SType.force s₁) ×
          ValidChannelRef G₁₂' b₂ (SType.force s₂))
vcr-match-2-sr {G₁ = .[]} (ssplit2 ss-[] ss-[]) () vcr-send
vcr-match-2-sr {G₁ = .(nothing ∷ _)} (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) with vcr-match-2-sr (ssplit2 ss1 ss2) vcr-recv vcr-send
vcr-match-2-sr {_} {.(nothing ∷ _)} (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-2-sr {_} {.(nothing ∷ _)} (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , G' , G₁' , G₁₁' , G₁₂' , ssplit2 ss1' ss2' , vcr-recv' , vcr-send') = just (t1=t2 , ds1=s2 , _ , _ , _ , _ , ssplit2 (ss-both ss1') (ss-both ss2') , there vcr-recv' , there vcr-send')

vcr-match-2-sr {G₁ = just (.(recv _ _) , POS) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (s , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-send

vcr-match-2-sr {G₁ = just (.(send _ _) , POS) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) (here-pos ina-G) = nothing
vcr-match-2-sr {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) (here-neg ina-G) = nothing
vcr-match-2-sr {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (s , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = .(just (recv _ _ , POSNEG) ∷ _)} {s₁ = s₁} (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) = just (refl , dual-involution _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-posneg ss2) , here-pos ina-G , here-neg ina-G₁)
vcr-match-2-sr {G₁ = (just (send _ s , POSNEG) ∷ _)} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G₁) (here-pos ina-G) = just (refl , equiv-refl _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , here-neg ina-G₁ , here-pos ina-G)
vcr-match-2-sr {G₁ = .(nothing ∷ _)} (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) with vcr-match-2-sr (ssplit2 ss1 ss2) vcr-recv vcr-send
vcr-match-2-sr {_} {.(nothing ∷ _)} (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | nothing = nothing
vcr-match-2-sr {_} {.(nothing ∷ _)} (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-recv) (there vcr-send) | just (t1=t2 , ds1=s2 , G' , G₁' , G₁₁' , G₁₂' , ssplit2 ss1' ss2' , vcr-recv' , vcr-send') = just (t1=t2 , ds1=s2 , _ , _ , _ , _ , ssplit2 (ss-right ss1') (ss-both ss2') , there vcr-recv' , there vcr-send')

vcr-match-2-sr {G₁ = .(just (recv _ _ , POS) ∷ _)} (ssplit2 (ss-posneg ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = .(just (send _ _ , POS) ∷ _)} (ssplit2 (ss-posneg ss1) (ss-right ss2)) (there vcr-recv) (here-pos ina-G) = nothing
vcr-match-2-sr {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-send) = nothing
vcr-match-2-sr {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () (there vcr-send)
vcr-match-2-sr {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) (here-neg ina-G) = nothing
vcr-match-2-sr {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()
vcr-match-2-sr {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-recv) ()


vcr-match-2-sb : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ s₁₁ s₁₂ s₂₁ s₂₂}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ValidChannelRef G₁₁ b₁ (sintern s₁₁ s₁₂)
  → ValidChannelRef G₁₂ b₂ (sextern s₂₁ s₂₂)
  → (lab : Selector)
  → Maybe (s₁₁ ≈ dual s₂₁ × s₁₂ ≈ dual s₂₂ ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₁₁' → Σ SCtx λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ValidChannelRef G₁₁' b₁ (selection lab (SType.force s₁₁) (SType.force s₁₂)) ×
          ValidChannelRef G₁₂' b₂ (selection lab (SType.force s₂₁) (SType.force s₂₂)))
vcr-match-2-sb (ssplit2 ss-[] ss-[]) () vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab with vcr-match-2-sb (ssplit2 ss1 ss2) vcr-int vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | just (ds11=s21 , ds12=s22 , G' , G₁' , G₁₁' , G₁₂' , ssplit2 ss1' ss2' , vcr-int' , vcr-ext') = just (ds11=s21 , ds12=s22 , _ , _ , _ , _ , ssplit2 (ss-both ss1') (ss-both ss2') , there vcr-int' , there vcr-ext')
vcr-match-2-sb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | nothing = nothing
vcr-match-2-sb {G₁ = just (.(sintern _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb {G₁ = just (send t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (recv t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sintN m alt , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sextN m alt , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sintern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sextern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb {G₁ = just (send! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (send? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (.(sextern _ _) , POS) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) (here-pos ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (send t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (recv t s , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (sintN m alt , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (sextN m alt , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (sintern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) (here-neg ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (sextern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (send! , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (send? , NEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {s₁₁ = s₁₁} (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) Left = just (dual-involution _ , dual-involution _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-posneg ss2) , here-pos ina-G ,  here-neg ina-G₁)
vcr-match-2-sb {s₁₂ = s₁₂} (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) Right = just (dual-involution _ , dual-involution _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-posneg ss2) , here-pos ina-G ,  here-neg ina-G₁)
vcr-match-2-sb {G₁ = just (send t s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (recv t s , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sintN m alt , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sextN m alt , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sintern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sextern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G) (here-pos ina-G₁) Left = just (equiv-refl _ , equiv-refl _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , here-neg ina-G , here-pos ina-G₁)
vcr-match-2-sb {G₁ = just (sextern s s₁ , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G) (here-pos ina-G₁) Right = just (equiv-refl _ , equiv-refl _ , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , here-neg ina-G , here-pos ina-G₁)
vcr-match-2-sb {G₁ = just (send! , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (send? , POSNEG) ∷ G₁} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab with vcr-match-2-sb (ssplit2 ss1 ss2) vcr-int vcr-ext lab
vcr-match-2-sb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | just (ds11=s21 , ds12=s22 , G' , G₁' , G₁₁' , G₁₂' , ssplit2 ss1' ss2' , vcr-int' , vcr-ext') = just (ds11=s21 , (ds12=s22 , _ , _ , _ , _ , ssplit2 (ss-right ss1') (ss-both ss2') , there vcr-int' , there vcr-ext'))
vcr-match-2-sb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab | nothing = nothing
vcr-match-2-sb (ssplit2 (ss-posneg ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb (ssplit2 (ss-posneg ss1) (ss-right ss2)) (there vcr-int) (here-pos ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (send t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (recv t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sintN m alt , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sextN m alt , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sintern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (sextern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-ext) lab = nothing
vcr-match-2-sb {G₁ = just (send! , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (send? , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-sb {G₁ = just (send t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (recv t s , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (sintN m alt , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (sextN m alt , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (sintern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) (here-neg ina-G) lab = nothing
vcr-match-2-sb {G₁ = just (sextern s s₁ , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (send! , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-sb {G₁ = just (send? , NEG) ∷ G₁} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab

vcr-match-2-nsb : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ m₁ m₂ alti alte}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ValidChannelRef G₁₁ b₁ (sintN m₁ alti)
  → ValidChannelRef G₁₂ b₂ (sextN m₂ alte)
  → (lab : Fin m₁)
  → Maybe (Σ (m₁ ≡ m₂) λ { refl → 
          ((i : Fin m₁) → dual (alti i) ≈ alte i) ×
          Σ SCtx λ G' → Σ SCtx λ G₁' → Σ SCtx λ G₁₁' → Σ SCtx λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ValidChannelRef G₁₁' b₁ (SType.force (alti lab)) ×
          ValidChannelRef G₁₂' b₂ (SType.force (alte lab))})
vcr-match-2-nsb {G₁ = .[]} (ssplit2 ss-[] ss-[]) () vcr-ext lab
vcr-match-2-nsb {G₁ = .(nothing ∷ _)} (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab =
  map (λ{ (refl , dai=ae , G' , G₁' , G₁₁' , G₁₂' , ssplit2 ss1' ss2' , vcr-int' , vcr-ext') → refl , dai=ae , _ , _ , _ , _ , ssplit2 (ss-both ss1') (ss-both ss2') , (there vcr-int') , (there vcr-ext') }) (vcr-match-2-nsb (ssplit2 ss1 ss2) vcr-int vcr-ext lab)
vcr-match-2-nsb {G₁ = just (.(sintN _ _) , POS) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-ext) lab = nothing
vcr-match-2-nsb {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-ext) lab
vcr-match-2-nsb {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-ext) lab
vcr-match-2-nsb {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-ext) lab
vcr-match-2-nsb {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-ext) lab
vcr-match-2-nsb {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-ext) lab
vcr-match-2-nsb {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-ext) lab = nothing
vcr-match-2-nsb {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-ext) lab
vcr-match-2-nsb {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () (there vcr-ext) lab
vcr-match-2-nsb {G₁ = just (s , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (.(sextN _ _) , POS) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) (here-pos ina-G) lab = nothing
vcr-match-2-nsb {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) (here-neg ina-G) lab = nothing
vcr-match-2-nsb {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (s , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = (just (sintN m alti , POSNEG) ∷ _)} (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G) (here-neg ina-G₁) lab =
  just (refl , (λ i → equiv-refl _) , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-posneg ss2) , here-pos ina-G , helper)
  where 
    helper : ValidChannelRef (just (SType.force (alti lab) , NEG) ∷ _) false (SType.force (dual (alti lab)))
    helper = here-neg ina-G₁
vcr-match-2-nsb {G₁ = just (send t s , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (recv t s , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sintern s₁ s₂ , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sextern s₁ s₂ , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sintN m alt , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sextN m alt , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G) (here-pos ina-G₁) lab =
  just (refl , (λ i → eq-sym (dual-involution _)) , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , helper , here-pos ina-G₁)
  where
    helper : ValidChannelRef (just (SType.force (alt lab) , NEG) ∷ _) false (SType.force (dual (alt lab)))
    helper = here-neg ina-G
vcr-match-2-nsb {G₁ = just (send! , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (send? , POSNEG) ∷ _} (ssplit2 (ss-left ss1) (ss-negpos ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = .(nothing ∷ _)} (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr-int) (there vcr-ext) lab =
  map (λ{ (refl , dai=ae , _ , _ , _ , _ , ssplit2 ss1' ss2' , vcr-int' , vcr-ext') → refl , dai=ae , _ , _ , _ , _ , ssplit2 (ss-right ss1') (ss-both ss2') , there vcr-int' , there vcr-ext' }) (vcr-match-2-nsb (ssplit2 ss1 ss2) vcr-int vcr-ext lab)
vcr-match-2-nsb {G₁ = .(just (sintN _ _ , POS) ∷ _)} (ssplit2 (ss-posneg ss1) (ss-left ss2)) (here-pos ina-G) (there vcr-ext) lab = nothing
vcr-match-2-nsb {G₁ = .(just (sextN _ _ , POS) ∷ _)} (ssplit2 (ss-posneg ss1) (ss-right ss2)) (there vcr-int) (here-pos ina-G) lab = nothing
vcr-match-2-nsb {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) (here-neg ina-G) (there vcr-ext) lab = nothing
vcr-match-2-nsb {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-left ss2)) () vcr-ext lab
vcr-match-2-nsb {G₁ = just (send t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (recv t s , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (sintern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (sextern s₁ s₂ , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (sintN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) (here-neg ina-G) lab = nothing
vcr-match-2-nsb {G₁ = just (sextN m alt , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (send! , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
vcr-match-2-nsb {G₁ = just (send? , NEG) ∷ _} (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr-int) () lab
