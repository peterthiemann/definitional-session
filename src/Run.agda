module Run where

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List
open import Data.List.All

open import Typing
open import Syntax
open import Global
open import Values
open import Session

open import Examples

fuel : ℕ → Fuel
fuel zero = Empty
fuel (suc n) = More (fuel n)

-- the magic number is 7
runex1 : Outcome
runex1 = start (fuel 7) ex1

-- need more steps, but gets *very* slow
runex3 : Outcome
runex3 = start (fuel 4) ex3
