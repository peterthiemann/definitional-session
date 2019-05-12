module Async where

open import Data.Fin
open import Data.List hiding (drop)
open import Data.List.All

open import Typing renaming (send to ssend ; recv to srecv)
open import Syntax
open import Values

-- an asynchronous channel is a promise for a channel
ASession DSession : STypeF SType → STypeF SType
ASession s = srecv (TChan s) (delay send!)
DSession s = dualF (ASession s)

AChan DChan : STypeF SType → Type
AChan s = TChan (ASession s)
DChan s = TChan (DSession s)

Promise : (s : SType) → Type
Promise s = TPair (AChan (SType.force s)) (DChan (SType.force s))

new-promise : ∀ {Φ} → All Unr Φ → (s : SType) → Expr Φ (Promise s)
new-promise unr-Φ s = new unr-Φ (delay (ASession (SType.force s)))

-- create an async channel
anew : ∀ {Φ}
  → (unr-Φ : All Unr Φ)
  → (s : SType)
  → Expr Φ (TPair (AChan (SType.force s)) (AChan (SType.force (dual s))))
anew unr-Φ s =
  letbind (split-all-unr unr-Φ) (new unr-Φ s)
  (letpair (left (split-all-unr unr-Φ)) (here unr-Φ)
  (letbind (rght (rght (split-all-unr unr-Φ))) (new-promise unr-Φ s)
  (letpair (left (rght (rght (split-all-unr unr-Φ)))) (here unr-Φ)
  (letbind (rght (rght (rght (rght (split-all-unr unr-Φ))))) (new-promise unr-Φ (dual s))
  (letpair (left (rght (rght (rght (rght (split-all-unr unr-Φ)))))) (here unr-Φ)
  (letbind (rght (rght (rght (left (left (rght (split-all-unr unr-Φ)))))))
           (fork (letbind (left (left (split-all-unr unr-Φ))) (send (left (rght (split-all-unr unr-Φ))) (here unr-Φ) (here unr-Φ))
                 (wait (here unr-Φ))))
  (letbind (drop UUnit (rght (left (rght (left (split-all-unr unr-Φ))))))
           (fork (letbind (left (left (split-all-unr unr-Φ))) (send (left (rght (split-all-unr unr-Φ))) (here unr-Φ) (here unr-Φ))
                 (wait (here unr-Φ))))
  (pair (drop UUnit (rght (left (split-all-unr unr-Φ))))
        (here unr-Φ) (here unr-Φ)))))))))

asend : ∀ {Φ Φ₁ Φ₂ s t}
  → (sp : Split Φ Φ₁ Φ₂)
  → (ch : (AChan (ssend t s)) ∈ Φ₁)
  → (vt : t ∈ Φ₂)
  → Expr Φ (AChan (SType.force s))
asend {Φ} {s = s} sp ch vt =
  letbind (split-all-right Φ) (new-promise [] s)
  (letpair (left (split-all-right Φ)) (here [])
  (letbind (rght (left (split-all-left Φ)))
           -- read actual channel & actual send & send depleted channel & close
           (fork (letbind (rght sp) (recv ch)
                 (letpair (left (split-all-right _)) (here [])
                 (letbind (left (split-all-right _)) (close (here []))
                 (letbind (drop UUnit (left (rght (split-all-left _)))) (send (left (split-all-right _)) (here []) vt)
                 (letbind (left (left [])) (send (rght (left [])) (here []) (here []))
                 (letbind (left []) (wait (here []))
                 (var (here [])))))))))
  (var (there UUnit (here [])))))

-- receive is a blocking operation!
arecv : ∀ {Φ s t}
      → (ch : (AChan (srecv t s)) ∈ Φ)
      → Expr Φ (TPair (AChan (SType.force s)) t)
arecv {s = s} ch =
  letbind (split-all-right _) (new-promise [] s)
  (letpair (left (split-all-right _)) (here [])
  (letbind (rght (rght (split-all-left _))) (recv ch) 
  (letpair (left (rght (rght (split-all-right _)))) (here [])
  (letbind (left (rght (rght (rght [])))) (close (here []))
  (letbind (drop UUnit (left (rght (rght [])))) (recv (here []))
  (letpair (left (rght (rght []))) (here [])
  (letbind (left (rght (rght (left []))))
           (fork (letbind (left (left []))
                          (send (rght (left [])) (here []) (here []))
                          (wait (here [])))) 
  (pair (drop UUnit (rght (left []))) (here []) (here [])))))))))

aclose : ∀ {Φ}
      → (ch : AChan send! ∈ Φ)
      → Expr Φ TUnit
aclose ch =
  fork (letbind (split-all-left _) (recv ch)
       (letpair (left []) (here [])
       (letbind (left (rght [])) (close (here []))
       (close (there UUnit (here []))))))

await : ∀ {Φ}
      → (ch : AChan send? ∈ Φ)
      → Expr Φ TUnit
await ch =
  fork (letbind (split-all-left _) (recv ch)
       (letpair (left []) (here [])
       (letbind (left (rght [])) (close (here []))
       (wait (there UUnit (here []))))))

anselect : ∀ {Φ m alt}
      → (lab : Fin m)
      → (ch : AChan (sintN m alt) ∈ Φ)
      → Expr Φ (AChan (SType.force (alt lab)))
anselect {alt = alt} lab ch =
  letbind (split-all-right _)
          (new-promise [] (alt lab))
  (letpair (left (split-all-right _)) (here [])
  (letbind (rght (left (split-all-left _)))
           (fork (letbind (rght (split-all-left _)) (recv ch)
                 (letpair (left (rght [])) (here [])
                 (letbind (left (rght (rght []))) (close (here []))
                 (letbind (drop UUnit (left (rght []))) (nselect lab (here []))
                 (letbind (left (left [])) (send (rght (left [])) (here []) (here []))
                 (wait (here []))))))))
  (var (there UUnit (here [])))))

-- branching is a blocking operation!
anbranch : ∀ {Φ m alt Φ₁ Φ₂ t}
      → (sp : Split Φ Φ₁ Φ₂)
      → (ch : AChan (sextN m alt) ∈ Φ₁)
      → (ealts : (i : Fin m) → Expr (AChan (SType.force (alt i)) ∷ Φ₂) t)
      → Expr Φ t
anbranch{alt = alt} sp ch ealts =
  letbind sp (recv ch)
  (letpair (left (split-all-right _)) (here [])
  (letbind (left (split-all-right _)) (close (here []))
  (nbranch (drop UUnit (left (split-all-right _))) (here [])
  (λ i → letbind (split-all-right _) (new-promise [] (alt i))
         (letpair (left (split-all-right _)) (here [])
         (letbind (rght (left (left (split-all-right _)))) 
                  (fork (letbind (left (left [])) (send (left (rght [])) (here []) (here []))
                        (wait (here [])))) 
         (letbind (drop UUnit (left (split-all-right _))) (var (here []))
                  (ealts i))))))))

