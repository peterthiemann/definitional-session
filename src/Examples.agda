module Examples where

open import Data.List hiding (reverse)
open import Data.List.All
open import Data.Nat

open import Typing
open import Syntax

ex1 : Expr [] TUnit
ex1 =
  letbind [] (new [] (delay send!))
  (letpair (left []) (here [])
  (letbind (rght (left []))
           (fork (wait (here [])))
  (close (there UUnit (here [])))))

ex1dual : Expr [] TUnit
ex1dual =
  letbind [] (new [] (delay send!))
  (letpair (left []) (here [])
  (letbind (left (rght []))
           (fork (close (here [])))
  (wait (there UUnit (here [])))))

-- sending and receiving
ex2 : Expr [] TUnit
ex2 =
  letbind [] (new [] (delay (Typing.send TInt (delay send!))))
  (letpair (left []) (here [])
  (letbind (left (rght []))
           (fork (letbind (rght []) (nat [] 42)
                 (letbind (left (left [])) (Expr.send (rght (left [])) (here []) (here []))
                 (letbind (left []) (close (here []))
                 (var (here []))))))
  (letbind (rght (left [])) (Expr.recv (here []))
  (letpair (left (rght [])) (here [])
  (letbind (left (left (rght []))) (wait (here (UInt ∷ [])))
  (var (here (UUnit ∷ []))))))))

-- higher order sending and receiving
ex3 : Expr [] TUnit
ex3 =
  letbind [] (new [] (delay (Typing.send (TChan send!) (delay send!))))
  (letbind (rght []) (new [] (delay send!))
  (letpair (left (rght [])) (here [])
  (letpair (rght (rght (left []))) (here [])
  (letbind (left (rght (left (left []))))
           (fork (letbind (left (left (rght []))) (Expr.send (left (rght [])) (here []) (here []))
                 (letbind (left (rght [])) (close (here []))
                 (wait (there UUnit (here []))))))
  (letbind (left (left [])) (Expr.recv (there UUnit (here [])))
  (letpair (left []) (here [])
  (letbind (left (rght [])) (wait (here []))
  (letbind (left (left [])) (close (there UUnit (here [])))
  (var (here []))))))))))

-- branching
ex4 : Expr [] TUnit
ex4 =
  letbind [] (new [] (delay (sintern (delay send!) (delay send?))))
  (letpair (left []) (here [])
  (letbind (left (rght []))
           (fork (letbind (left []) (select Left (here []))
                 (close (here []))))
  (branch (left (left [])) (there UUnit (here []))
          (wait (here []))
          (close (here [])))))

-- simple lambda: (λx.x)()
ex5 : Expr [] TUnit
ex5 = letbind [] (llambda [] [] (var (here [])))
      (letbind (rght []) (unit [])
      (app (rght (left [])) (here []) (here [])))

-- lambda app: (λfx.fx) (λx.x)()
ex6 : Expr [] TUnit
ex6 = letbind [] (llambda [] [] (llambda (left []) [] (app (rght (left [])) (here []) (here []))))
      (letbind (rght []) (llambda [] [] (var (here [])))
      (letbind (rght (rght [])) (unit [])
      (letbind (rght (left (left []))) (app (rght (left [])) (here []) (here []))
      (app (left (rght [])) (here []) (here [])))))
