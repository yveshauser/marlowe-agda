open import Relation.Binary using (DecidableEquality)

module Marlowe.Language.Transaction
  {Party Token : Set}
  (_=ᵖ_ : DecidableEquality Party)
  (_=ᵗ_ : DecidableEquality Token) where

open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Data.Nat using (ℕ; suc; zero)

import Marlowe.Language.Contract as Contract
import Marlowe.Language.Input as Input
import Marlowe.Language.State as State

open Contract {Party} {Token} (_=ᵖ_) (_=ᵗ_) using (AccountId ; ChoiceId ; Contract ; Payee ; ValueId)
open Input {Party} {Token} (_=ᵖ_) (_=ᵗ_) using (Input)
open State {Party} {Token} (_=ᵖ_) (_=ᵗ_) using (Environment ; State ; TimeInterval)
open import Primitives using (PosixTime)

data IntervalError : Set where
  InvalidInterval : TimeInterval → IntervalError
  IntervalInPastError : PosixTime → TimeInterval → IntervalError
  

data IntervalResult : Set where
  IntervalTrimmed : Environment → State → IntervalResult
  mkIntervalError : IntervalError → IntervalResult

data Payment : Set where
  mkPayment : AccountId → Payee → Token → ℕ → Payment

data TransactionWarning : Set where
  TransactionNonPositiveDeposit : Party → AccountId → Token → Int → TransactionWarning
  TransactionNonPositivePay : AccountId → Payee → Token → Int → TransactionWarning
  TransactionPartialPay : AccountId → Payee → Token → Int → Int → TransactionWarning
  TransactionShadowing : ValueId → Int → Int → TransactionWarning
  TransactionAssertionFailed : TransactionWarning


data TransactionError : Set where
  TEAmbiguousTimeIntervalError : TransactionError
  TEApplyNoMatchError : TransactionError
  TEIntervalError : IntervalError → TransactionError
  TEUselessTransaction : TransactionError
  TEHashMismatch : TransactionError


data TransactionInput : Set where
  mkTransactionInput : TimeInterval → List Input → TransactionInput


data TransactionOutput : Set where
  mkTransactionOutput : List TransactionWarning → List Payment → State → Contract → TransactionOutput
  mkError : TransactionError → TransactionOutput
