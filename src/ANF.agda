module ANF where

open import Data.List
open import Data.List.All

open import Typing
open import DSyntax
open import Syntax

-- transform a direct style expression into and anf expression

anf : ∀ {φ t} → DExpr φ t → Expr φ t
anf (var x) = var x
anf (nat unr-φ i) = nat unr-φ i
anf (unit unr-φ) = unit unr-φ
anf (pair sp de de₁) = letbind sp (anf de) (letbind (rght (split-all-left _)) (anf de₁) (pair (rght (left [])) (here []) (here [])))
anf (letpair sp de de₁) = letbind sp (anf de) (letpair (left (split-all-right _)) (here []) (anf de₁))
anf (fork de) = fork (anf de)
anf (new unr-φ s) = new unr-φ s
anf (send sp de de₁) = letbind sp (anf de) (letbind (rght (split-all-left _)) (anf de₁) (send (rght (left [])) (here []) (here [])))
anf (recv de) = letbind (split-all-left _) (anf de) (recv (here []))
anf (close de) = letbind (split-all-left _) (anf de) (close (here []))
anf (wait de) = letbind (split-all-left _) (anf de) (wait (here []))
anf (select lab de) = letbind (split-all-left _) (anf de) (select lab (here []))
anf (branch sp de de₁ de₂) = letbind sp (anf de) (branch (left (split-all-right _)) (here []) (anf de₁) (anf de₂))
anf (ulambda unr-φ de) = ulambda (split-all-left _) unr-φ [] (anf de)
anf (llambda de) = llambda (split-all-left _) [] (anf de)
anf (app sp de de₁) = letbind sp (anf de) (letbind (rght (split-all-left _)) (anf de₁) (app (rght (left [])) (here []) (here [])))
anf (subsume de t≤t') = subsume (anf de) t≤t'
