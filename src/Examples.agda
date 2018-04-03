module Examples where

open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Nat

open import Typing
open import Syntax

ex1 : Expr [] TUnit
ex1 =
  letbind [] (new [] SEnd!)
  (letpair (left []) (here [])
  (letbind (rght (left []))
           (fork (wait (here [])))
  (close (there UUnit (here [])))))

ex1dual : Expr [] TUnit
ex1dual =
  letbind [] (new [] SEnd!)
  (letpair (left []) (here [])
  (letbind (left (rght []))
           (fork (close (here [])))
  (wait (there UUnit (here [])))))
