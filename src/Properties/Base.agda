module Properties.Base where

open import Data.List
open import Data.Product

open import Global
open import Session
open import Schedule

one-step : ∀ {G} → (∃ λ G' → ThreadPool (G' ++ G)) → Event × (∃ λ G → ThreadPool G)
one-step{G} (G1 , tp)
  with ssplit-refl-left-inactive (G1 ++ G)
... | G' , ina-G' , ss-GG'
  with Alternative.step ss-GG' tp (tnil ina-G')
... | ev , tp' = ev , ( , tp')

restart : ∀ {G} → Command G → Command G
restart (Stopped ss v κ) = apply-cont ss κ v
restart cmd = cmd
