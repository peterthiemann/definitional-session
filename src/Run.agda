module Run where

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List
open import Data.List.All

open import Typing hiding (Session)
open import Syntax
open import Global
open import Channel
open import Values
open import Session

open import Examples

fuel : ℕ → Fuel
fuel zero = Empty
fuel (suc n) = More (fuel n)

-- the magic number shows the last state before termination

-- runs to completion: the magic number is 7
runex1 : Outcome
runex1 = start (fuel 8) ex1

-- works up to (fuel 3)
runex2 : Outcome
runex2 = start (fuel 4) ex2

-- need more steps, but gets *very* slow
runex3 : Outcome
runex3 = start (fuel 4) ex3

-- works up to (fuel 5)
runex4 : Outcome
runex4 = start (fuel 5) ex4

-- just lambda calculus
-- runs to completion: the magic number is 2
runex5 : Outcome
runex5 = start (fuel 3) ex5

-- just lambda calculus
-- magic number is 6
runex6 : Outcome
runex6 = start (fuel 7) ex6
