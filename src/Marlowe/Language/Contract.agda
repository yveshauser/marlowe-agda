open import Relation.Binary using (DecidableEquality)

module Marlowe.Language.Contract
  {Party Token : Set}
  (_=ᵖ_ : DecidableEquality Party)
  (_=ᵗ_ : DecidableEquality Token) where

open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Data.Bool using (Bool; false; _∧_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _≟_)
open import Primitives using (PosixTime)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Relation.Nullary using (yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (cong)

record AccountId : Set where
  constructor mkAccountId
  field
    getParty : Party

_eqAccountId_ : DecidableEquality AccountId
_eqAccountId_ (mkAccountId x) (mkAccountId y) with x =ᵖ y
... | yes p = yes (cong mkAccountId p)
... | no p = no (λ x →  p (cong getParty x)) where open AccountId

data Timeout : Set where
  mkTimeout : PosixTime → Timeout

record ChoiceName : Set where
  constructor mkChoiceName
  field
    getString : String

_eqChoiceName_ : DecidableEquality ChoiceName
_eqChoiceName_ (mkChoiceName x) (mkChoiceName y) with x ≟ y
... | yes p = yes (cong mkChoiceName p)
... | no p = no (λ x →  p (cong getString x)) where open ChoiceName

record ChoiceId : Set where
  constructor mkChoiceId
  field
    getParty : ChoiceName → Party

postulate
  _eqChoiceId_ : DecidableEquality ChoiceId
{-
_eqChoiceId_ (mkChoiceId x a) (mkChoiceId y b) with x eqChoiceName y | a =ᵖ b
... | yes p | yes q = ? -- yes (cong mkAccountId p)
... | yes p | no q = ?
... | no p | yes q = ? -- no (λ x →  p (cong getParty x)) where open AccountId
... | no p | no q = ?
-}

record ValueId : Set where
  constructor mkValueId
  field
    getString : String

_eqValueId_ : DecidableEquality ValueId
_eqValueId_ (mkValueId x) (mkValueId y) with x ≟ y
... | yes p = yes (cong mkValueId p)
... | no p = no (λ x →  p (cong getString x)) where open ValueId

postulate
  _eqAccountIdTokenDec_ : DecidableEquality (AccountId × Token)

data Observation : Set

data Value : Set where
  AvailableMoney : AccountId → Token → Value
  Constant : ℕ → Value
  -- NegValue : Value → Value
  AddValue : Value → Value → Value
  SubValue : Value → Value → Value
  MulValue : Value → Value → Value
  -- DivValue : Value → Value → Value
  ChoiceValue : ChoiceId → Value
  TimeIntervalStart : Value
  TimeIntervalEnd : Value
  UseValue : ValueId → Value
  Cond : Observation → Value → Value → Value

data Observation where
  AndObs : Observation → Observation → Observation
  OrObs : Observation → Observation → Observation
  NotObs : Observation → Observation
  ChoseSomething : ChoiceId → Observation
  ValueGE : Value → Value → Observation
  ValueGT : Value → Value → Observation
  ValueLT : Value → Value → Observation
  ValueLE : Value → Value → Observation
  ValueEQ : Value → Value → Observation
  TrueObs : Observation
  FalseObs : Observation

data Bound : Set where
  mkBound : Int → Int → Bound

data Action : Set where
  Deposit : AccountId → Party → Token → Value → Action
  Choice : ChoiceId → List Bound → Action
  Notify : Observation → Action

data Payee : Set where
  mkAccount : AccountId → Payee
  mkParty : Party → Payee

data Contract : Set

data Case : Set where
  mkCase : Action → Contract → Case

getAction : Case → Action
getAction (mkCase action _) = action

data Contract where
  Close : Contract
  Pay : AccountId → Payee → Token → Value → Contract → Contract
  If : Observation → Contract → Contract → Contract
  When : List Case → Timeout → Contract → Contract
  Let : ValueId → Value → Contract → Contract
  Assert : Observation → Contract → Contract
