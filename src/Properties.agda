module Properties where

open import Data.Bool
open import Data.Empty
open import Data.Maybe hiding (Any ; All)
open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.List.Any
open import Data.Product
open import Data.Sum
open import Data.Unit

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Typing
open import Syntax
open import Global
open import Channel
open import Values
open import Session
open import Schedule

open import ProcessSyntax
open import ProcessRun


-- adequacy
open import Properties.Base

import Properties.StepBeta
import Properties.StepPair
import Properties.StepFork
import Properties.StepNew
import Properties.StepCloseWait

