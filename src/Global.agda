module Global where

open import Data.List
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Typing

-- specific
data PosNeg : Set where
  POS NEG POSNEG : PosNeg

-- global session context
SEntry = Maybe (STypeF SType × PosNeg)
SCtx = List SEntry

-- SSplit G G₁ G₂
-- split G into G₁ and G₂
-- length and position preserving
data SSplit : SCtx → SCtx → SCtx → Set where
  ss-[]    : SSplit [] [] []
  ss-both  : ∀ {  G G₁ G₂ }
           → SSplit G G₁ G₂
           → SSplit (nothing ∷ G) (nothing ∷ G₁) (nothing ∷ G₂)
  ss-left  : ∀ { spn G G₁ G₂ }
           → SSplit G G₁ G₂
           → SSplit (just spn ∷ G) (just spn ∷ G₁) (nothing ∷ G₂)
  ss-right : ∀ { spn G G₁ G₂ }
           → SSplit G G₁ G₂
           → SSplit (just spn ∷ G) (nothing ∷ G₁) (just spn ∷ G₂)
  ss-posneg : ∀ {  s G G₁ G₂ }
          → SSplit G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , POS) ∷ G₁) (just (s , NEG) ∷ G₂)
  ss-negpos : ∀ {  s G G₁ G₂ }
          → SSplit G G₁ G₂
          → SSplit (just (s , POSNEG) ∷ G) (just (s , NEG) ∷ G₁) (just (s , POS) ∷ G₂)

ssplit-sym : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → SSplit G G₂ G₁
ssplit-sym ss-[] = ss-[]
ssplit-sym (ss-both ss12) = ss-both (ssplit-sym ss12)
ssplit-sym (ss-left ss12) = ss-right (ssplit-sym ss12)
ssplit-sym (ss-right ss12) = ss-left (ssplit-sym ss12)
ssplit-sym (ss-posneg ss12) = ss-negpos (ssplit-sym ss12)
ssplit-sym (ss-negpos ss12) = ss-posneg (ssplit-sym ss12)

-- tedious but easy to prove
ssplit-compose : {G G₁ G₂ G₃ G₄ : SCtx}
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₁ G₃ G₄)
  → ∃ λ Gi → SSplit G G₃ Gi × SSplit Gi G₄ G₂
ssplit-compose ss-[] ss-[] =  [] , (ss-[] , ss-[])
ssplit-compose (ss-both ss) (ss-both ss₁) with ssplit-compose ss ss₁
ssplit-compose (ss-both ss) (ss-both ss₁) | Gi , ss₁₃ , ss₂₄ = nothing ∷ Gi , ss-both ss₁₃ , ss-both ss₂₄
ssplit-compose (ss-left ss) (ss-left ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = nothing ∷ Gi , ss-left ss₁₃ , ss-both ss₂₄
ssplit-compose (ss-left ss) (ss-right ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just _ ∷ Gi , ss-right ss₁₃ , ss-left ss₂₄
ssplit-compose (ss-left ss) (ss-posneg ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ =  just ( _ , NEG) ∷ Gi , ss-posneg ss₁₃ , ss-left ss₂₄
ssplit-compose (ss-left ss) (ss-negpos ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just ( _ , POS) ∷ Gi , ss-negpos ss₁₃ , ss-left ss₂₄
ssplit-compose (ss-right ss) (ss-both ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just _ ∷ Gi , ss-right ss₁₃ , ss-right ss₂₄
ssplit-compose (ss-posneg ss) (ss-left ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just ( _ , NEG) ∷ Gi , ss-posneg ss₁₃ , ss-right ss₂₄
ssplit-compose (ss-posneg ss) (ss-right ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just ( _ , POSNEG) ∷ Gi , ss-right ss₁₃ , ss-posneg ss₂₄
ssplit-compose (ss-negpos ss) (ss-left ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just ( _ , POS) ∷ Gi , ss-negpos ss₁₃ , ss-right ss₂₄
ssplit-compose (ss-negpos ss) (ss-right ss₁) with ssplit-compose ss ss₁
... | Gi , ss₁₃ , ss₂₄ = just ( _ , POSNEG) ∷ Gi , ss-right ss₁₃ , ss-negpos ss₂₄

ssplit-compose2 : {G G₁ G₂ G₂₁ G₂₂ : SCtx}
  → SSplit G G₁ G₂
  → SSplit G₂ G₂₁ G₂₂
  → ∃ λ Gi → (SSplit G Gi G₂₁ × SSplit Gi G₁ G₂₂)
ssplit-compose2 ss-[] ss-[] = [] , ss-[] , ss-[]
ssplit-compose2 (ss-both ss) (ss-both ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = nothing ∷ Gi , ss-both ssx , ss-both ssy
ssplit-compose2 (ss-left ss) (ss-both ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just _ ∷ Gi , ss-left ssx , ss-left ssy
ssplit-compose2 (ss-right ss) (ss-left ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = nothing ∷ Gi , ss-right ssx , ss-both ssy
ssplit-compose2 (ss-right ss) (ss-right ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just _ ∷ Gi , ss-left ssx , ss-right ssy
ssplit-compose2 (ss-right ss) (ss-posneg ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just (_ , NEG) ∷ Gi , ss-negpos ssx , ss-right ssy
ssplit-compose2 (ss-right ss) (ss-negpos ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just (_ , POS) ∷ Gi , ss-posneg ssx , ss-right ssy
ssplit-compose2 (ss-posneg ss) (ss-left ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just (_ , POS) ∷ Gi , ss-posneg ssx , ss-left ssy
ssplit-compose2 (ss-posneg ss) (ss-right ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just (_ , POSNEG) ∷ Gi , ss-left ssx , ss-posneg ssy
ssplit-compose2 (ss-negpos ss) (ss-left ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just (_ , NEG) ∷ Gi , ss-negpos ssx , ss-left ssy
ssplit-compose2 (ss-negpos ss) (ss-right ss₂) with ssplit-compose2 ss ss₂
... | Gi , ssx , ssy = just (_ , POSNEG) ∷ Gi , ss-left ssx , ss-negpos ssy

ssplit-compose3 : {G G₁ G₂ G₃ G₄ : SCtx}
  → SSplit G G₁ G₂
  → SSplit G₂ G₃ G₄
  → ∃ λ Gi → (SSplit G Gi G₄ × SSplit Gi G₁ G₃)
ssplit-compose3 ss-[] ss-[] = [] , ss-[] , ss-[]
ssplit-compose3 (ss-both ss12) (ss-both ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = nothing ∷ Gi , ss-both ssi4 , ss-both ssi13
ssplit-compose3 (ss-left ss12) (ss-both ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just _ ∷ Gi , ss-left ssi4 , ss-left ssi13
ssplit-compose3 (ss-right ss12) (ss-left ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just _ ∷ Gi , ss-left ssi4 , ss-right ssi13
ssplit-compose3 (ss-right ss12) (ss-right ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = nothing ∷ Gi , ss-right ssi4 , ss-both ssi13
ssplit-compose3 (ss-right ss12) (ss-posneg ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just ( _ , POS) ∷ Gi , ss-posneg ssi4 , ss-right ssi13
ssplit-compose3 (ss-right ss12) (ss-negpos ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just ( _ , NEG) ∷ Gi , ss-negpos ssi4 , ss-right ssi13
ssplit-compose3 (ss-posneg ss12) (ss-left ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just ( _ , POSNEG) ∷ Gi , ss-left ssi4 , ss-posneg ssi13
ssplit-compose3 (ss-posneg ss12) (ss-right ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just ( _ , POS) ∷ Gi , ss-posneg ssi4 , ss-left ssi13
ssplit-compose3 (ss-negpos ss12) (ss-left ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just ( _ , POSNEG) ∷ Gi , ss-left ssi4 , ss-negpos ssi13
ssplit-compose3 (ss-negpos ss12) (ss-right ss234) with ssplit-compose3 ss12 ss234
... | Gi , ssi4 , ssi13 = just ( _ , NEG) ∷ Gi , ss-negpos ssi4 , ss-left ssi13


ssplit-compose4
  : {G G₁ G₂ G₂₁ G₂₂ : SCtx}
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₂ G₂₁ G₂₂)
  → ∃ λ Gi → SSplit G G₂₁ Gi × SSplit Gi G₁ G₂₂
ssplit-compose4 ss-[] ss-[] = [] , ss-[] , ss-[]
ssplit-compose4 (ss-both ss) (ss-both ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = nothing ∷ Gi , ss-both ss-21i , ss-both ss-122
ssplit-compose4 (ss-left ss) (ss-both ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = just _ ∷ Gi , ss-right ss-21i , ss-left ss-122
ssplit-compose4 (ss-right ss) (ss-left ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = nothing ∷ Gi , ss-left ss-21i , ss-both ss-122
ssplit-compose4 (ss-right ss) (ss-right ss₁) with ssplit-compose4  ss ss₁
... | Gi , ss-21i , ss-122 = just _ ∷ Gi , ss-right ss-21i , ss-right ss-122
ssplit-compose4 (ss-right ss) (ss-posneg ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = just (_ , NEG) ∷ Gi , ss-posneg ss-21i , ss-right ss-122
ssplit-compose4 (ss-right ss) (ss-negpos ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = just (_ , POS) ∷ Gi , ss-negpos ss-21i , ss-right ss-122
ssplit-compose4 (ss-posneg ss) (ss-left ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = just (_ , POS) ∷ Gi , ss-negpos ss-21i , ss-left ss-122
ssplit-compose4 (ss-posneg ss) (ss-right ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = just (_ , POSNEG) ∷ Gi , ss-right ss-21i , ss-posneg ss-122
ssplit-compose4 (ss-negpos ss) (ss-left ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = just (_ , NEG) ∷ Gi , ss-posneg ss-21i , ss-left ss-122
ssplit-compose4 (ss-negpos ss) (ss-right ss₁) with ssplit-compose4 ss ss₁
... | Gi , ss-21i , ss-122 = just (_ , POSNEG) ∷ Gi , ss-right ss-21i , ss-negpos ss-122

ssplit-compose5
  : ∀ {G G₁ G₂ G₁₁ G₁₂ : SCtx}
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₁ G₁₁ G₁₂)
  → ∃ λ Gi → SSplit G G₁₂ Gi × SSplit Gi G₁₁ G₂
ssplit-compose5 ss-[] ss-[] = [] , ss-[] , ss-[]
ssplit-compose5 (ss-both ss) (ss-both ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = nothing ∷ Gi , ss-both ss-12i , ss-both ss-112
ssplit-compose5 (ss-left ss) (ss-left ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just _ ∷ Gi , ss-right ss-12i , ss-left ss-112
ssplit-compose5 (ss-left ss) (ss-right ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = nothing ∷ Gi , ss-left ss-12i , ss-both ss-112
ssplit-compose5 (ss-left ss) (ss-posneg ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just (_ , POS) ∷ Gi , ss-negpos ss-12i , ss-left ss-112
ssplit-compose5 (ss-left ss) (ss-negpos ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just (_ , NEG) ∷ Gi , ss-posneg ss-12i , ss-left ss-112
ssplit-compose5 (ss-right ss) (ss-both ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just _ ∷ Gi , ss-right ss-12i , ss-right ss-112
ssplit-compose5 (ss-posneg ss) (ss-left ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just (_ , POSNEG) ∷ Gi , ss-right ss-12i , ss-posneg ss-112
ssplit-compose5 (ss-posneg ss) (ss-right ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just (_ , NEG) ∷ Gi , ss-posneg ss-12i , ss-right ss-112
ssplit-compose5 (ss-negpos ss) (ss-left ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just (_ , POSNEG) ∷ Gi , ss-right ss-12i , ss-negpos ss-112
ssplit-compose5 (ss-negpos ss) (ss-right ss₁) with ssplit-compose5 ss ss₁
... | Gi , ss-12i , ss-112 = just (_ , POS) ∷ Gi , ss-negpos ss-12i , ss-right ss-112

ssplit-compose6
  : ∀ {G G₁ G₂ G₁₁ G₁₂ : SCtx}
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₁ G₁₁ G₁₂)
  → ∃ λ Gi → SSplit G G₁₁ Gi × SSplit Gi G₁₂ G₂
ssplit-compose6 ss-[] ss-[] = [] , ss-[] , ss-[]
ssplit-compose6 (ss-both ss) (ss-both ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = nothing ∷ Gi , ss-both ss-g11i , ss-both ss-g122
ssplit-compose6 (ss-left ss) (ss-left ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = nothing ∷ Gi , ss-left ss-g11i , ss-both ss-g122
ssplit-compose6 (ss-left ss) (ss-right ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just _ ∷ Gi , ss-right ss-g11i , ss-left ss-g122
ssplit-compose6 (ss-left ss) (ss-posneg ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just (_ , NEG) ∷ Gi , ss-posneg ss-g11i , ss-left ss-g122
ssplit-compose6 (ss-left ss) (ss-negpos ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just (_ , POS) ∷ Gi , ss-negpos ss-g11i , ss-left ss-g122
ssplit-compose6 (ss-right ss) (ss-both ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just _ ∷ Gi , ss-right ss-g11i , ss-right ss-g122
ssplit-compose6 (ss-posneg ss) (ss-left ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just (_ , NEG) ∷ Gi , ss-posneg ss-g11i , ss-right ss-g122
ssplit-compose6 (ss-posneg ss) (ss-right ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just (_ , POSNEG) ∷ Gi , ss-right ss-g11i , ss-posneg ss-g122
ssplit-compose6 (ss-negpos ss) (ss-left ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just (_ , POS) ∷ Gi , ss-negpos ss-g11i , ss-right ss-g122
ssplit-compose6 (ss-negpos ss) (ss-right ss₁) with ssplit-compose6 ss ss₁
... | Gi , ss-g11i , ss-g122 = just (_ , POSNEG) ∷ Gi , ss-right ss-g11i , ss-negpos ss-g122

ssplit-join
  : ∀ {G G₁ G₂ G₁₁ G₁₂ G₂₁ G₂₂}
  → (ss : SSplit G G₁ G₂)
  → (ss₁ : SSplit G₁ G₁₁ G₁₂)
  → (ss₂ : SSplit G₂ G₂₁ G₂₂)
  → ∃ λ G₁' → ∃ λ G₂' → SSplit G G₁' G₂' × SSplit G₁' G₁₁ G₂₁ × SSplit G₂' G₁₂ G₂₂
ssplit-join ss-[] ss-[] ss-[] = [] , [] , ss-[] , ss-[] , ss-[]
ssplit-join (ss-both ss) (ss-both ss₁) (ss-both ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = nothing ∷ G₁' , nothing ∷ G₂' , ss-both ss-12 , ss-both ss-1121 , ss-both ss-2122
ssplit-join (ss-left ss) (ss-left ss₁) (ss-both ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , nothing ∷ G₂' , ss-left ss-12 ,  ss-left ss-1121 , ss-both ss-2122
ssplit-join (ss-left ss) (ss-right ss₁) (ss-both ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = nothing ∷ G₁' ,
                                                just _ ∷ G₂' ,
                                                ss-right ss-12 , ss-both ss-1121 , ss-left ss-2122
ssplit-join (ss-left ss) (ss-posneg ss₁) (ss-both ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-posneg ss-12 , ss-left ss-1121 , ss-left ss-2122
ssplit-join (ss-left ss) (ss-negpos ss₁) (ss-both ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-negpos ss-12 , ss-left ss-1121 , ss-left ss-2122
ssplit-join (ss-right ss) (ss-both ss₁) (ss-left ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' ,
                                                nothing ∷ G₂' , ss-left ss-12 , ss-right ss-1121 , ss-both ss-2122
ssplit-join (ss-right ss) (ss-both ss₁) (ss-right ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = nothing ∷ G₁' ,
                                                just _ ∷ G₂' ,
                                                ss-right ss-12 , ss-both ss-1121 , ss-right ss-2122
ssplit-join (ss-right ss) (ss-both ss₁) (ss-posneg ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-posneg ss-12 , ss-right ss-1121 , ss-right ss-2122
ssplit-join (ss-right ss) (ss-both ss₁) (ss-negpos ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-negpos ss-12 , ss-right ss-1121 , ss-right ss-2122
ssplit-join (ss-posneg ss) (ss-left ss₁) (ss-left ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , nothing ∷ G₂' , ss-left ss-12 , ss-posneg ss-1121 , ss-both ss-2122
ssplit-join (ss-posneg ss) (ss-left ss₁) (ss-right ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-posneg ss-12 , ss-left ss-1121 , ss-right ss-2122
ssplit-join (ss-posneg ss) (ss-right ss₁) (ss-left ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-negpos ss-12 , ss-right ss-1121 , ss-left ss-2122
ssplit-join (ss-posneg ss) (ss-right ss₁) (ss-right ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = nothing ∷ G₁' ,
                                                just (_ , POSNEG) ∷ G₂' ,
                                                ss-right ss-12 , ss-both ss-1121 , ss-posneg ss-2122
ssplit-join (ss-negpos ss) (ss-left ss₁) (ss-left ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , nothing ∷ G₂' , ss-left ss-12 , ss-negpos ss-1121 , ss-both ss-2122
ssplit-join (ss-negpos ss) (ss-left ss₁) (ss-right ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-negpos ss-12 , ss-left ss-1121 , ss-right ss-2122
ssplit-join (ss-negpos ss) (ss-right ss₁) (ss-left ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = just _ ∷ G₁' , just _ ∷ G₂' , ss-posneg ss-12 , ss-right ss-1121 , ss-left ss-2122
ssplit-join (ss-negpos ss) (ss-right ss₁) (ss-right ss₂) with ssplit-join ss ss₁ ss₂
... | G₁' , G₂' , ss-12 , ss-1121 , ss-2122 = nothing ∷ G₁' ,
                                                just (_ , POSNEG) ∷ G₂' ,
                                                ss-right ss-12 , ss-both ss-1121 , ss-negpos ss-2122

-- another rotation
ssplit-rotate : ∀ {G G1 G2 G21 G22 G211 G212 : SCtx}
  → SSplit G G1 G2
  → SSplit G2 G21 G22
  → SSplit G21 G211 G212
  → ∃ λ G2'
  → ∃ λ G21'
  → SSplit G G211 G2' × SSplit G2' G21' G22 × SSplit G21' G1 G212
ssplit-rotate ss-[] ss-[] ss-[] =
  [] , [] , ss-[] , ss-[] , ss-[]
ssplit-rotate (ss-both ss-g12) (ss-both ss-g2122) (ss-both ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  nothing ∷ G2' , nothing ∷ G21' , (ss-both ss-g12') , (ss-both ss-g2122') , (ss-both ss-g211212')
ssplit-rotate (ss-left ss-g12) (ss-both ss-g2122) (ss-both ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , (ss-right ss-g12') , ss-left ss-g2122' , ss-left ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-left ss-g2122) (ss-left ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-left ss-g12' , ss-both ss-g2122' , ss-both ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-left ss-g2122) (ss-right ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-left ss-g2122' , ss-right ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-left ss-g2122) (ss-posneg ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-posneg ss-g12' , ss-left ss-g2122' , ss-right ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-left ss-g2122) (ss-negpos ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-negpos ss-g12' , ss-left ss-g2122' , ss-right ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-right ss-g2122) (ss-both ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-right ss-g2122' , ss-both ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-posneg ss-g2122) (ss-left ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-posneg ss-g12' , ss-right ss-g2122' , ss-both ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-posneg ss-g2122) (ss-right ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-posneg ss-g2122' , ss-right ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-negpos ss-g2122) (ss-left ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-negpos ss-g12' , ss-right ss-g2122' , ss-both ss-g211212'
ssplit-rotate (ss-right ss-g12) (ss-negpos ss-g2122) (ss-right ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-negpos ss-g2122' , ss-right ss-g211212'
ssplit-rotate (ss-posneg ss-g12) (ss-left ss-g2122) (ss-left ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-negpos ss-g12' , ss-left ss-g2122' , ss-left ss-g211212'
ssplit-rotate (ss-posneg ss-g12) (ss-left ss-g2122) (ss-right ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-left ss-g2122' , ss-posneg ss-g211212'
ssplit-rotate (ss-posneg ss-g12) (ss-right ss-g2122) (ss-both ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-posneg ss-g2122' , ss-left ss-g211212'
ssplit-rotate (ss-negpos ss-g12) (ss-left ss-g2122) (ss-left ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-posneg ss-g12' , ss-left ss-g2122' , ss-left ss-g211212'
ssplit-rotate (ss-negpos ss-g12) (ss-left ss-g2122) (ss-right ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-left ss-g2122' , ss-negpos ss-g211212'
ssplit-rotate (ss-negpos ss-g12) (ss-right ss-g2122) (ss-both ss-g211212) with ssplit-rotate ss-g12 ss-g2122 ss-g211212
... | G2' , G21' , ss-g12' , ss-g2122' , ss-g211212' =
  _ , _ , ss-right ss-g12' , ss-negpos ss-g2122' , ss-left ss-g211212'

-- a session context is inactive if all its entries are void
data Inactive : (G : SCtx) → Set where
  []-inactive : Inactive []
  ::-inactive : ∀ {G : SCtx} → Inactive G → Inactive (nothing ∷ G)

inactive-ssplit-trivial : ∀ {G} → Inactive G → SSplit G G G
inactive-ssplit-trivial []-inactive = ss-[]
inactive-ssplit-trivial (::-inactive ina) = ss-both (inactive-ssplit-trivial ina)

ssplit-inactive : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₁ → Inactive G₂ → Inactive G
ssplit-inactive ss-[] []-inactive []-inactive = []-inactive
ssplit-inactive (ss-both ssp) (::-inactive ina1) (::-inactive ina2) = ::-inactive (ssplit-inactive ssp ina1 ina2)
ssplit-inactive (ss-left ssp) () ina2
ssplit-inactive (ss-right ssp) ina1 ()
ssplit-inactive (ss-posneg ssp) () ina2
ssplit-inactive (ss-negpos ssp) ina1 ()

ssplit-inactive-left : ∀ {G G'} → SSplit G G G' → Inactive G'
ssplit-inactive-left ss-[] = []-inactive
ssplit-inactive-left (ss-both ssp) = ::-inactive (ssplit-inactive-left ssp)
ssplit-inactive-left (ss-left ssp) = ::-inactive (ssplit-inactive-left ssp)

ssplit-refl-left : (G : SCtx) → Σ SCtx λ G' → SSplit G G G'
ssplit-refl-left [] = [] , ss-[]
ssplit-refl-left (just x ∷ G) with ssplit-refl-left G
... | G' , ssp' = nothing ∷ G' , ss-left ssp'
ssplit-refl-left (nothing ∷ G) with ssplit-refl-left G
... | G' , ssp' = nothing ∷ G' , ss-both ssp'

ssplit-refl-left-inactive : (G : SCtx) → Σ SCtx λ G' → Inactive G' × SSplit G G G'
ssplit-refl-left-inactive [] = [] , []-inactive , ss-[]
ssplit-refl-left-inactive (x ∷ G) with ssplit-refl-left-inactive G
ssplit-refl-left-inactive (just x ∷ G) | G' , ina-G' , ss-GG' = nothing ∷ G' , ::-inactive ina-G' , ss-left ss-GG'
ssplit-refl-left-inactive (nothing ∷ G) | G' , ina-G' , ss-GG' = nothing ∷ G' , ::-inactive ina-G' , ss-both ss-GG'

ssplit-inactive-right : ∀ {G G'} → SSplit G G' G → Inactive G'
ssplit-inactive-right ss-[] = []-inactive
ssplit-inactive-right (ss-both ss) = ::-inactive (ssplit-inactive-right ss)
ssplit-inactive-right (ss-right ss) = ::-inactive (ssplit-inactive-right ss)

ssplit-refl-right : (G : SCtx) → Σ SCtx λ G' → SSplit G G' G
ssplit-refl-right [] = [] , ss-[]
ssplit-refl-right (just x ∷ G) with ssplit-refl-right G
... | G' , ssp' = nothing ∷ G' , ss-right ssp'
ssplit-refl-right (nothing ∷ G) with ssplit-refl-right G
... | G' , ssp' = nothing ∷ G' , ss-both ssp'

ssplit-refl-right-inactive : (G : SCtx) → Σ SCtx λ G' → Inactive G' × SSplit G G' G
ssplit-refl-right-inactive [] = [] , []-inactive , ss-[]
ssplit-refl-right-inactive (x ∷ G) with ssplit-refl-right-inactive G
ssplit-refl-right-inactive (just x ∷ G) | G' , ina-G' , ssp' = nothing ∷ G' , ::-inactive ina-G' , ss-right ssp'
ssplit-refl-right-inactive (nothing ∷ G) | G' , ina-G' , ssp' = nothing ∷ G' , ::-inactive ina-G' , ss-both ssp'

inactive-left-ssplit : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₁ → G ≡ G₂
inactive-left-ssplit ss-[] []-inactive = refl
inactive-left-ssplit (ss-both ss) (::-inactive inG₁) =
  cong (_∷_ nothing) (inactive-left-ssplit ss inG₁)
inactive-left-ssplit (ss-right ss) (::-inactive inG₁) =
  cong (_∷_ (just _)) (inactive-left-ssplit ss inG₁)

inactive-right-ssplit : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₂ → G ≡ G₁
inactive-right-ssplit ss-[] []-inactive = refl
inactive-right-ssplit (ss-both ssp) (::-inactive ina) =
  cong (_∷_ nothing) (inactive-right-ssplit ssp ina)
inactive-right-ssplit (ss-left ssp) (::-inactive ina) =
  cong (_∷_ (just _)) (inactive-right-ssplit ssp ina)

inactive-right-ssplit-sym : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₂ → G₁ ≡ G
inactive-right-ssplit-sym ssp ina = sym (inactive-right-ssplit ssp ina)

inactive-right-ssplit-transform : ∀ {G G₁ G₂} → SSplit G G₁ G₂ → Inactive G₂ → SSplit G G G₂
inactive-right-ssplit-transform ss-[] []-inactive = ss-[]
inactive-right-ssplit-transform (ss-both ss-GG1G2) (::-inactive ina-G2) = ss-both (inactive-right-ssplit-transform ss-GG1G2 ina-G2)
inactive-right-ssplit-transform (ss-left ss-GG1G2) (::-inactive ina-G2) = ss-left (inactive-right-ssplit-transform ss-GG1G2 ina-G2)
inactive-right-ssplit-transform (ss-right ss-GG1G2) ()
inactive-right-ssplit-transform (ss-posneg ss-GG1G2) ()
inactive-right-ssplit-transform (ss-negpos ss-GG1G2) ()

ssplit-function : ∀ {G G' G₁ G₂} → SSplit G G₁ G₂ → SSplit G' G₁ G₂ → G ≡ G'
ssplit-function ss-[] ss-[] = refl
ssplit-function (ss-both ssp-GG1G2) (ss-both ssp-G'G1G2) =
  cong (_∷_ nothing) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-left ssp-GG1G2) (ss-left ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-right ssp-GG1G2) (ss-right ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-posneg ssp-GG1G2) (ss-posneg ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)
ssplit-function (ss-negpos ssp-GG1G2) (ss-negpos ssp-G'G1G2) =
  cong (_∷_ (just _)) (ssplit-function ssp-GG1G2 ssp-G'G1G2)

ssplit-function1 : ∀ {G G₁ G₁' G₂} → SSplit G G₁ G₂ → SSplit G G₁' G₂ → G₁ ≡ G₁'
ssplit-function1 ss-[] ss-[] = refl
ssplit-function1 (ss-both ssp-GG1G2) (ss-both ssp-GG1'G2) =
  cong (_∷_ nothing) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-left ssp-GG1G2) (ss-left ssp-GG1'G2) =
  cong (_∷_ (just _)) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-right ssp-GG1G2) (ss-right ssp-GG1'G2) =
  cong (_∷_ nothing) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-posneg ssp-GG1G2) (ss-posneg ssp-GG1'G2) =
  cong (_∷_ (just _)) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)
ssplit-function1 (ss-negpos ssp-GG1G2) (ss-negpos ssp-GG1'G2) =
  cong (_∷_ (just _)) (ssplit-function1 ssp-GG1G2 ssp-GG1'G2)

ssplit-function2 : ∀ {G G₁ G₂ G₂'} → SSplit G G₁ G₂ → SSplit G G₁ G₂' → G₂ ≡ G₂'
ssplit-function2 ss-[] ss-[] = refl
ssplit-function2 (ss-both ssp-GG1G2) (ss-both ssp-GG1G2') =
  cong (_∷_ nothing) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-left ssp-GG1G2) (ss-left ssp-GG1G2') =
  cong (_∷_ nothing) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-right ssp-GG1G2) (ss-right ssp-GG1G2') =
  cong (_∷_ (just _)) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-posneg ssp-GG1G2) (ss-posneg ssp-GG1G2') =
  cong (_∷_ (just _)) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
ssplit-function2 (ss-negpos ssp-GG1G2) (ss-negpos ssp-GG1G2') =
  cong (_∷_ (just _)) (ssplit-function2 ssp-GG1G2 ssp-GG1G2')
