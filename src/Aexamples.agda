module Aexamples where

open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Nat

open import Typing
open import Syntax
open import Async

{-
Lithmus test for asynchronous operations
A thread send something to an asynchronous channel and receives it afterwards.
-}
aex1 : Expr [] TUnit
aex1 = letbind [] (anew [] (delay send!))
       (letpair (left []) (here [])
       (letbind (left (rght [])) (aclose (here []))
       (await (there UUnit (here [])))))

-- just replace synchronous operations by the asynchronous ones
asyncex1 : Expr [] TUnit
asyncex1 =
  letbind [] (anew [] (delay send!))
  (letpair (left []) (here [])
  (letbind (rght (left []))
           (fork (await (here [])))
  (aclose (there UUnit (here [])))))

-- sending and receiving
asyncex2 : Expr [] TUnit
asyncex2 =
  letbind [] (anew [] (delay (send TInt (delay send!))))
  (letpair (left []) (here [])
  (letbind (left (rght []))
           (fork (letbind (rght []) (nat [] 42)
                 (letbind (left (left [])) (asend (rght (left [])) (here []) (here []))
                 (letbind (left []) (aclose (here []))
                 (var (here []))))))
  (letbind (rght (left [])) (arecv (here []))
  (letpair (left (rght [])) (here [])
  (letbind (left (left (rght []))) (await (here (UInt ∷ [])))
  (var (here (UUnit ∷ []))))))))
