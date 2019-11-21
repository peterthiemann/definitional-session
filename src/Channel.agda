module Channel where

open import Data.Bool hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.List hiding (map)
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax hiding (send ; recv)
open import Global


data ChannelEnd : Set where
  POS NEG : ChannelEnd

otherEnd : ChannelEnd → ChannelEnd
otherEnd POS = NEG
otherEnd NEG = POS

-- the main part of a channel endpoint value is a valid channel reference
-- the channel end determines whether it's the front end or the back end of the channel
-- enforces that the session context has only one channel
data ChannelRef : (G : SCtx) (ce : ChannelEnd) (s : STypeF SType) → Set where
  here-pos : ∀ {s s'} {G : SCtx}
    → (ina-G : Inactive G)
    → s ≲' s'
    → ChannelRef (just (s , POS) ∷ G) POS s'
  here-neg : ∀ {s s'} {G : SCtx}
    → (ina-G : Inactive G)
    → dualF s ≲' s'
    → ChannelRef (just (s , NEG) ∷ G) NEG s'
  there : ∀ {b s} {G : SCtx}
    → (vcr : ChannelRef G b s)
    → ChannelRef (nothing ∷ G) b s

-- coerce channel ref to a supertype
vcr-coerce : ∀ {G b s s'} → ChannelRef G b s → s ≲' s' → ChannelRef G b s'
vcr-coerce (here-pos ina-G x) s≤s' = here-pos ina-G (subF-trans x s≤s')
vcr-coerce (here-neg ina-G x) s≤s' = here-neg ina-G (subF-trans x s≤s')
vcr-coerce (there vcr) s≤s' = there (vcr-coerce vcr s≤s')

-- find matching wait instruction in thread pool
vcr-match : ∀ {G G₁ G₂ b₁ b₂ s₁ s₂}
  → SSplit G G₁ G₂
  → ChannelRef G₁ b₁ s₁
  → ChannelRef G₂ b₂ s₂
  → Maybe (b₁ ≡ otherEnd b₂ × dualF s₂ ≲' s₁)
vcr-match () (here-pos _ _) (here-pos _ _)
vcr-match (ss-posneg ss) (here-pos{s} ina-G s<=s') (here-neg ina-G₁ ds<=s'') = just (refl , subF-trans (dual-subF ds<=s'') (subF-trans (eqF-implies-subF (eqF-sym (dual-involutionF s))) s<=s'))
vcr-match (ss-left ss) (here-pos _ _) (there vcr2) = nothing
vcr-match (ss-negpos ss) (here-neg ina-G ds<=s') (here-pos ina-G₁ s<=s'') = just (refl , subF-trans (dual-subF s<=s'') ds<=s')
vcr-match (ss-left ss) (here-neg _ _) (there vcr2) = nothing
vcr-match (ss-right ss) (there vcr1) (here-pos _ ina-G) = nothing
vcr-match (ss-right ss) (there vcr1) (here-neg _ ina-G) = nothing
vcr-match (ss-both ss) (there vcr1) (there vcr2) = vcr-match ss vcr1 vcr2

-- ok. brute force for a fixed tree with three levels
data SSplit2 (G G₁ G₂ G₁₁ G₁₂ : SCtx) : Set where
  ssplit2 : 
    (ss1 : SSplit G G₁ G₂)
    → (ss2 : SSplit G₁ G₁₁ G₁₂)
    → SSplit2 G G₁ G₂ G₁₁ G₁₂

vcr-match-2-sr : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ s₁ s₂ t₁ t₂}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ChannelRef G₁₁ b₁ (recv t₁ s₁)
  → ChannelRef G₁₂ b₂ (send t₂ s₂)
  → Maybe (SubT t₂ t₁ × dual s₂ ≲ s₁ ×
          ∃ λ G' → ∃ λ G₁' → ∃ λ G₁₁' → ∃ λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ChannelRef G₁₁' b₁ (SType.force s₁) ×
          ChannelRef G₁₂' b₂ (SType.force s₂))
vcr-match-2-sr (ssplit2 ss-[] ()) (here-pos ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (here-pos ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-left ss1) ()) (here-pos ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (here-pos ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-posneg ss1) ()) (here-pos ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-negpos ss1) ()) (here-pos ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 ss-[] ()) (here-pos ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (here-pos ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G (sub-recv{s1} t t' t<=t' s1<=s1')) (here-neg ina-G₁ (sub-send .t t'' t'<=t s1<=s1'')) = just ((subt-trans t'<=t t<=t') , (sub-trans (dual-sub s1<=s1'') (sub-trans (eq-implies-sub (eq-sym (dual-involution s1))) s1<=s1')) , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-posneg ss2) , here-pos ina-G (Sub.force s1<=s1') , here-neg ina-G₁ (Sub.force s1<=s1''))
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (here-pos ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-posneg ss1) ()) (here-pos ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-negpos ss1) ()) (here-pos ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 ss-[] ()) (here-pos ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (here-pos ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-left ss2)) (here-pos ina-G x) (there vcr2) = nothing
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (here-pos ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-posneg ss1) (ss-left ss2)) (here-pos ina-G x) (there vcr2) = nothing
vcr-match-2-sr (ssplit2 (ss-negpos ss1) ()) (here-pos ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 ss-[] ()) (here-neg ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr {s₁ = s₁} {s₂} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G (sub-recv .t t'' t<=t' s1<=s1'')) (here-pos ina-G₁ (sub-send t t' t'<=t s1<=s1')) = just ((subt-trans t'<=t t<=t') , ((sub-trans (dual-sub s1<=s1') s1<=s1'') , (_ , (_ , (_ , (_ , ((ssplit2 (ss-left ss1) (ss-negpos ss2)) , ((here-neg ina-G (Sub.force s1<=s1'')) , (here-pos ina-G₁ (Sub.force s1<=s1'))))))))))
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-posneg ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-negpos ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ x₁)
vcr-match-2-sr (ssplit2 ss-[] ()) (here-neg ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (here-neg ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (here-neg ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-posneg ss1) ()) (here-neg ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 (ss-negpos ss1) ()) (here-neg ina-G x) (here-neg ina-G₁ x₁)
vcr-match-2-sr (ssplit2 ss-[] ()) (here-neg ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (here-neg ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-left ss2)) (here-neg ina-G x) (there vcr2) = nothing
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (here-neg ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-posneg ss1) ()) (here-neg ina-G x) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-negpos ss1) (ss-left ss2)) (here-neg ina-G x) (there vcr2) = nothing
vcr-match-2-sr (ssplit2 ss-[] ()) (there vcr1) (here-pos ina-G x)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (there vcr1) (here-pos ina-G x)
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr1) (here-pos ina-G x) = nothing
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (there vcr1) (here-pos ina-G x)
vcr-match-2-sr (ssplit2 (ss-posneg ss1) (ss-right ss2)) (there vcr1) (here-pos ina-G x) = nothing
vcr-match-2-sr (ssplit2 (ss-negpos ss1) ()) (there vcr1) (here-pos ina-G x)
vcr-match-2-sr (ssplit2 ss-[] ()) (there vcr1) (here-neg ina-G x)
vcr-match-2-sr (ssplit2 (ss-both ss1) ()) (there vcr1) (here-neg ina-G x)
vcr-match-2-sr (ssplit2 (ss-left ss1) (ss-right ss2)) (there vcr1) (here-neg ina-G x) = nothing
vcr-match-2-sr (ssplit2 (ss-right ss1) ()) (there vcr1) (here-neg ina-G x)
vcr-match-2-sr (ssplit2 (ss-negpos ss1) (ss-right ss2)) (there vcr1) (here-neg ina-G x) = nothing
vcr-match-2-sr (ssplit2 ss-[] ()) (there vcr1) (there vcr2)
vcr-match-2-sr (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr1) (there vcr2) with vcr-match-2-sr (ssplit2 ss1 ss2) vcr1 vcr2
... | nothing = nothing
... | just (t2<=t1 , ds2<=s1 , _ , _ , _ , _ , ssplit2 ss1' ss2' , vcr1' , vcr2') = just (t2<=t1 , ds2<=s1 , _ , _ , _ , _ , (ssplit2 (ss-both ss1') (ss-both ss2')) , ((there vcr1') , (there vcr2')))
vcr-match-2-sr (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr1) (there vcr2) = map (λ { (t2<=t1 , ds2<=s1 , _ , _ , _ , _ , ssplit2 ss1' ss2' , vcr1' , vcr2') → t2<=t1 , ds2<=s1 , _ , _ , _ , _ , (ssplit2 (ss-right ss1') (ss-both ss2')) , (there vcr1') , (there vcr2') }) (vcr-match-2-sr (ssplit2 ss1 ss2) vcr1 vcr2)
vcr-match-2-sr (ssplit2 (ss-negpos ss1) ()) (there vcr1) (there vcr2)


vcr-match-2-sb : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ s₁₁ s₁₂ s₂₁ s₂₂}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ChannelRef G₁₁ b₁ (sintern s₁₁ s₁₂)
  → ChannelRef G₁₂ b₂ (sextern s₂₁ s₂₂)
  → (lab : Selector)
  → Maybe (dual s₂₁ ≲ s₁₁ × dual s₂₂ ≲ s₁₂ ×
          ∃ λ G' → ∃ λ G₁' → ∃ λ G₁₁' → ∃ λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ChannelRef G₁₁' b₁ (selection lab (SType.force s₁₁) (SType.force s₁₂)) ×
          ChannelRef G₁₂' b₂ (selection lab (SType.force s₂₁) (SType.force s₂₂)))
vcr-match-2-sb (ssplit2 ss1 ss2) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-pos ina-G₁ (sub-sextern s1<=s1'' s2<=s2'')) lab = nothing
vcr-match-2-sb (ssplit2 ss-[] ()) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-neg ina-G₁ x₁) lab
vcr-match-2-sb (ssplit2 (ss-both ss1) ()) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-neg ina-G₁ x₁) lab
vcr-match-2-sb (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-neg ina-G₁ (sub-sextern s1<=s1'' s2<=s2'')) Left = just ((sub-trans (dual-sub s1<=s1'') (sub-trans (eq-implies-sub (eq-sym (dual-involution _))) s1<=s1')) , (sub-trans (dual-sub s2<=s2'') (sub-trans (eq-implies-sub (eq-sym (dual-involution _))) s2<=s2')) , _ , _ , _ , _ , (ssplit2 (ss-left ss1) (ss-posneg ss2)) , (here-pos ina-G (Sub.force s1<=s1')) , (here-neg ina-G₁ (Sub.force s1<=s1'')))
vcr-match-2-sb (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-neg ina-G₁ (sub-sextern s1<=s1'' s2<=s2'')) Right = just ((sub-trans (dual-sub s1<=s1'') (sub-trans (eq-implies-sub (eq-sym (dual-involution _))) s1<=s1')) , (sub-trans (dual-sub s2<=s2'') (sub-trans (eq-implies-sub (eq-sym (dual-involution _))) s2<=s2')) , _ , _ , _ , _ , (ssplit2 (ss-left ss1) (ss-posneg ss2)) , (here-pos ina-G (Sub.force s2<=s2')) , (here-neg ina-G₁ (Sub.force s2<=s2'')))
vcr-match-2-sb (ssplit2 (ss-right ss1) ()) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-neg ina-G₁ x₁) lab
vcr-match-2-sb (ssplit2 (ss-posneg ss1) ()) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-neg ina-G₁ x₁) lab
vcr-match-2-sb (ssplit2 (ss-negpos ss1) ()) (here-pos ina-G (sub-sintern s1<=s1' s2<=s2')) (here-neg ina-G₁ x₁) lab
vcr-match-2-sb (ssplit2 ss1 ss2) (here-pos ina-G x) (there vcr2) lab = nothing
vcr-match-2-sb (ssplit2 ss-[] ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextern s1<=s1' s2<=s2')) lab
vcr-match-2-sb (ssplit2 (ss-both ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextern s1<=s1' s2<=s2')) lab
vcr-match-2-sb (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G (sub-sintern s1<=s1'' s2<=s2'')) (here-pos ina-G₁ (sub-sextern s1<=s1' s2<=s2')) Left = just ((sub-trans (dual-sub s1<=s1') s1<=s1'') , ((sub-trans (dual-sub s2<=s2') s2<=s2'') , (_ , (_ , (_ , (_ , ((ssplit2 (ss-left ss1) (ss-negpos ss2)) , ((here-neg ina-G (Sub.force s1<=s1'')) , (here-pos ina-G₁ (Sub.force s1<=s1'))))))))))
vcr-match-2-sb (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G (sub-sintern s1<=s1'' s2<=s2'')) (here-pos ina-G₁ (sub-sextern s1<=s1' s2<=s2')) Right = just ((sub-trans (dual-sub s1<=s1') s1<=s1'') , ((sub-trans (dual-sub s2<=s2') s2<=s2'') , (_ , (_ , (_ , (_ , ((ssplit2 (ss-left ss1) (ss-negpos ss2)) , ((here-neg ina-G (Sub.force s2<=s2'')) , (here-pos ina-G₁ (Sub.force s2<=s2'))))))))))
vcr-match-2-sb (ssplit2 (ss-right ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextern s1<=s1' s2<=s2')) lab
vcr-match-2-sb (ssplit2 (ss-posneg ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextern s1<=s1' s2<=s2')) lab
vcr-match-2-sb (ssplit2 (ss-negpos ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextern s1<=s1' s2<=s2')) lab
vcr-match-2-sb (ssplit2 ss1 ss2) (here-neg ina-G x) (here-neg ina-G₁ x₁) lab = nothing
vcr-match-2-sb (ssplit2 ss1 ss2) (here-neg ina-G x) (there vcr2) lab = nothing
vcr-match-2-sb (ssplit2 ss1 ss2) (there vcr1) (here-pos ina-G x) lab = nothing
vcr-match-2-sb (ssplit2 ss1 ss2) (there vcr1) (here-neg ina-G x) lab = nothing
vcr-match-2-sb (ssplit2 ss-[] ()) (there vcr1) (there vcr2) lab
vcr-match-2-sb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr1) (there vcr2) lab = map (λ { (ds21<=s11 , ds22<=s12 , _ , _ , _ , _ , ssplit2 ss1' ss2' , vcr1' , vcr2') → ds21<=s11 , ds22<=s12 , _ , _ , _ , _ , (ssplit2 (ss-both ss1') (ss-both ss2')) , ((there vcr1') , (there vcr2')) }) (vcr-match-2-sb (ssplit2 ss1 ss2) vcr1 vcr2 lab)
vcr-match-2-sb (ssplit2 (ss-left ss1) ()) (there vcr1) (there vcr2) lab
vcr-match-2-sb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr1) (there vcr2) lab = map  (λ { (ds21<=s11 , ds22<=s12 , _ , _ , _ , _ , ssplit2 ss1' ss2' , vcr1' , vcr2') → ds21<=s11 , ds22<=s12 , _ , _ , _ , _ , (ssplit2 (ss-right ss1') (ss-both ss2')) , ((there vcr1') , (there vcr2')) }) (vcr-match-2-sb (ssplit2 ss1 ss2) vcr1 vcr2 lab)
vcr-match-2-sb (ssplit2 (ss-posneg ss1) ()) (there vcr1) (there vcr2) lab
vcr-match-2-sb (ssplit2 (ss-negpos ss1) ()) (there vcr1) (there vcr2) lab

vcr-match-2-nsb : ∀ {G G₁ G₂ G₁₁ G₁₂ b₁ b₂ m₁ m₂ alti alte}
  → SSplit2 G G₁ G₂ G₁₁ G₁₂
  → ChannelRef G₁₁ b₁ (sintN m₁ alti)
  → ChannelRef G₁₂ b₂ (sextN m₂ alte)
  → (lab : Fin m₁)
  → Maybe (Σ (m₁ ≤ m₂) λ { p → 
          ((i : Fin m₁) → dual (alti i) ≲ alte (inject≤ i p)) ×
          ∃ λ G' → ∃ λ G₁' → ∃ λ G₁₁' → ∃ λ G₁₂' →
          SSplit2 G' G₁' G₂ G₁₁' G₁₂' ×
          ChannelRef G₁₁' b₁ (SType.force (alti lab)) ×
          ChannelRef G₁₂' b₂ (SType.force (alte (inject≤ lab p)))})
vcr-match-2-nsb (ssplit2 ss1 ss2) (here-pos ina-G _) (here-pos ina-G₁ _) lab = nothing
vcr-match-2-nsb (ssplit2 ss-[] ()) (here-pos ina-G (sub-sintN m'≤m x)) (here-neg ina-G₁ x₁) lab
vcr-match-2-nsb (ssplit2 (ss-both ss1) ()) (here-pos ina-G (sub-sintN m'≤m x)) (here-neg ina-G₁ x₁) lab
vcr-match-2-nsb {m₁ = m₁} {alti = alti} {alte = alte} (ssplit2 (ss-left ss1) (ss-posneg ss2)) (here-pos ina-G (sub-sintN {alt = alt} m'≤m subint)) (here-neg ina-G₁ (sub-sextN m≤m' subext)) lab = just (≤-trans m'≤m m≤m' , auxSub , _ , _ , _ , _ , (ssplit2 (ss-left ss1) (ss-posneg ss2)) , (here-pos ina-G (Sub.force (subint lab))) , (here-neg ina-G₁ auxExt))
  where
    auxSub : (i : Fin m₁) → dual (alti i) ≲ alte (inject≤ i (≤-trans m'≤m m≤m'))
    auxSub i with subext (inject≤ i m'≤m)
    ... | r  rewrite (inject-trans m≤m' m'≤m i) = sub-trans (dual-sub (subint i)) r
    auxExt : dualF (SType.force (alt (inject≤ lab m'≤m))) ≲' SType.force (alte (inject≤ lab (≤-trans m'≤m m≤m')))
    auxExt with Sub.force (subext (inject≤ lab m'≤m))
    ... | se rewrite inject-trans  m≤m' m'≤m lab = se
vcr-match-2-nsb (ssplit2 (ss-right ss1) ()) (here-pos ina-G (sub-sintN m'≤m x)) (here-neg ina-G₁ x₁) lab
vcr-match-2-nsb (ssplit2 (ss-posneg ss1) ()) (here-pos ina-G (sub-sintN m'≤m x)) (here-neg ina-G₁ x₁) lab
vcr-match-2-nsb (ssplit2 (ss-negpos ss1) ()) (here-pos ina-G (sub-sintN m'≤m x)) (here-neg ina-G₁ x₁) lab
vcr-match-2-nsb (ssplit2 ss1 ss2) (here-pos ina-G x) (there vcr2) lab = nothing
vcr-match-2-nsb (ssplit2 ss-[] ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextN m≤m' x₁)) lab
vcr-match-2-nsb (ssplit2 (ss-both ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextN m≤m' x₁)) lab
vcr-match-2-nsb {m₁ = m₁} {alti = alti} {alte = alte} (ssplit2 (ss-left ss1) (ss-negpos ss2)) (here-neg ina-G (sub-sintN m'≤m subint)) (here-pos ina-G₁ (sub-sextN {alt = alt} m≤m' subext)) lab = just ((≤-trans m'≤m m≤m') , auxSub , _ , _ , _ , _ , ssplit2 (ss-left ss1) (ss-negpos ss2) , here-neg ina-G (Sub.force (subint lab)) , here-pos ina-G₁ auxExt)
  where
    auxSub : (i : Fin m₁) → dual (alti i) ≲ alte (inject≤ i (≤-trans m'≤m m≤m'))
    auxSub i with subext (inject≤ i m'≤m)
    ... | sub2 rewrite (inject-trans m≤m' m'≤m i) = 
      sub-trans (sub-trans (dual-sub (subint i)) (eq-implies-sub (eq-sym (dual-involution _)))) sub2
    auxExt : SType.force (alt (inject≤ lab m'≤m)) ≲' SType.force (alte (inject≤ lab (≤-trans m'≤m m≤m')))
    auxExt with Sub.force (subext (inject≤ lab m'≤m))
    ... | se rewrite (inject-trans m≤m' m'≤m lab) = se
vcr-match-2-nsb (ssplit2 (ss-right ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextN m≤m' x₁)) lab
vcr-match-2-nsb (ssplit2 (ss-posneg ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextN m≤m' x₁)) lab
vcr-match-2-nsb (ssplit2 (ss-negpos ss1) ()) (here-neg ina-G x) (here-pos ina-G₁ (sub-sextN m≤m' x₁)) lab
vcr-match-2-nsb (ssplit2 ss1 ss2) (here-neg ina-G x) (here-neg ina-G₁ x₁) lab = nothing
vcr-match-2-nsb (ssplit2 ss1 ss2) (here-neg ina-G x) (there vcr2) lab = nothing
vcr-match-2-nsb (ssplit2 ss1 ss2) (there vcr1) (here-pos ina-G x) lab = nothing
vcr-match-2-nsb (ssplit2 ss1 ss2) (there vcr1) (here-neg ina-G x) lab = nothing
vcr-match-2-nsb (ssplit2 ss-[] ()) (there vcr1) (there vcr2) lab
vcr-match-2-nsb (ssplit2 (ss-both ss1) (ss-both ss2)) (there vcr1) (there vcr2) lab =
  map (λ { (m1≤m2 , fdi≤e , _ , _ , _ , _ , ssplit2 ss1' ss2' , vcr1' , vcr2') → m1≤m2 , fdi≤e , _ , _ , _ , _ , (ssplit2 (ss-both ss1') (ss-both ss2')) , there vcr1' , there vcr2' })
      (vcr-match-2-nsb (ssplit2 ss1 ss2) vcr1 vcr2 lab)
vcr-match-2-nsb (ssplit2 (ss-left ss1) ()) (there vcr1) (there vcr2) lab
vcr-match-2-nsb (ssplit2 (ss-right ss1) (ss-both ss2)) (there vcr1) (there vcr2) lab =
  map (λ { (m1≤m2 , fdi≤e , _ , _ , _ , _ , ssplit2 ss1' ss2' , vcr1' , vcr2') → m1≤m2 , fdi≤e , _ , _ , _ , _ , (ssplit2 (ss-right ss1') (ss-both ss2')) , there vcr1' , there vcr2' })
      (vcr-match-2-nsb (ssplit2 ss1 ss2) vcr1 vcr2 lab)
vcr-match-2-nsb (ssplit2 (ss-posneg ss1) ()) (there vcr1) (there vcr2) lab
vcr-match-2-nsb (ssplit2 (ss-negpos ss1) ()) (there vcr1) (there vcr2) lab

