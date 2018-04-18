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

-- sending and receiving
ex2 : Expr [] TUnit
ex2 =
  letbind [] (new [] (SSend TInt SEnd!))
  (letpair (left []) (here [])
  (letbind (left (rght []))
           (fork (letbind (rght []) (nat [] 42)
                 (letbind (left (left [])) (send (rght (left [])) (here []) (here []))
                 (letbind (left []) (close (here []))
                 (var (here []))))))
  (letbind (rght (left [])) (recv (here []))
  (letpair (left (rght [])) (here [])
  (letbind (left (left (rght []))) (wait (here (UInt ∷ [])))
  (var (here (UUnit ∷ []))))))))

-- higher order sending and receiving
ex3 : Expr [] TUnit
ex3 =
  letbind [] (new [] (SSend (TChan SEnd!) SEnd!))
  (letbind (rght []) (new [] SEnd!)
  (letpair (left (rght [])) (here [])
  (letpair (rght (rght (left []))) (here [])
  (letbind (left (rght (left (left []))))
           (fork (letbind (left (left (rght []))) (send (left (rght [])) (here []) (here []))
                 (letbind (left (rght [])) (close (here []))
                 (wait (there UUnit (here []))))))
  (letbind (left (left [])) (recv (there UUnit (here [])))
  (letpair (left []) (here [])
  (letbind (left (rght [])) (wait (here []))
  (letbind (left (left [])) (close (there UUnit (here [])))
  (var (here []))))))))))

-- branching
ex4 : Expr [] TUnit
ex4 =
  letbind [] (new [] (SIntern SEnd! SEnd?))
  (letpair (left []) (here [])
  (letbind (left (rght []))
           (fork (letbind (left []) (select Left (here []))
                 (close (here []))))
  (branch (left (left [])) (there UUnit (here []))
          (wait (here []))
          (close (here [])))))
