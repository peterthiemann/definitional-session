module Run where

open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List
open import Data.List.All

open import Typing
open import Syntax
open import Global
open import Channel
open import Values
open import Session

open import Examples

gas : ℕ → Gas
gas zero = Empty
gas (suc n) = More (gas n)

-- the magic number shows the last state before termination

-- runs to completion: the magic number is 7
runex1 : Outcome
runex1 = start (gas 8) ex1

-- works up to (gas 4), but gets slow at 4
runex2 : Outcome
runex2 = start (gas 4) ex2

-- need more steps, but gets *very* slow
runex3 : Outcome
runex3 = start (gas 4) ex3

-- works up to (gas 5)
runex4 : Outcome
runex4 = start (gas 5) ex4

-- just lambda calculus
-- runs to completion: the magic number is 2
runex5 : Outcome
runex5 = start (gas 3) ex5

-- just lambda calculus
-- magic number is 6
runex6 : Outcome
runex6 = start (gas 7) ex6
