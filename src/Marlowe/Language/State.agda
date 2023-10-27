open import Relation.Binary using (DecidableEquality)

module Marlowe.Language.State
  {Party Token : Set}
  (_=ᵖ_ : DecidableEquality Party)
  (_=ᵗ_ : DecidableEquality Token) where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)

import Marlowe.Language.Contract as Contract
open Contract {Party} {Token} (_=ᵖ_) (_=ᵗ_) using (AccountId ; ChoiceId ; ValueId)
open import Primitives using (AssocList ; PosixTime)

Accounts : Set
Accounts = AssocList (AccountId × Token) ℕ

Choices : Set
Choices = AssocList ChoiceId ℕ

BoundValues : Set
BoundValues = AssocList ValueId ℕ

record State : Set where
  constructor mkState
  field
    accounts : Accounts
    choices : Choices
    boundValues : BoundValues
    minTime : PosixTime

emptyState : PosixTime → State
emptyState = mkState [] [] []

TimeInterval : Set
TimeInterval = PosixTime × PosixTime

record Environment : Set where
  constructor mkEnvironment
  field
    timeInterval : TimeInterval

