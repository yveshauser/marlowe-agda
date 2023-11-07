
module Marlowe.Language.Contract where


open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List)
open import Data.Bool using (Bool; false; _∧_)
open import Primitives
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; _≡_; _≢_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary using (yes; no)

data Party : Set where
  Address : ByteString → Party
  Role : ByteString → Party

unParty : Party → ByteString
unParty (Address x) = x
unParty (Role x) = x

_eqPartyDec_ : DecidableEquality Party
_eqPartyDec_ (Address x) (Address y) with x eqByteString y
... | yes p = yes (cong Address p)
... | no ¬p = no (λ x → let y = cong unParty x in ¬p y)
_eqPartyDec_ (Role x) (Role y) with x eqByteString y
... | yes p = yes (cong Role p)
... | no ¬p = no λ x → let y = cong unParty x in ¬p y
_eqPartyDec_ (Role r) (Address a) = no λ ()
_eqPartyDec_ (Address _) (Role _) = no λ ()

_eqParty_ : Party → Party → Bool
p₁ eqParty p₂ = ⌊ p₁ eqPartyDec p₂ ⌋

data AccountId : Set where
  mkAccountId : Party → AccountId

_eqAccountId_ : AccountId → AccountId → Bool
_eqAccountId_ (mkAccountId x) (mkAccountId y) = x eqParty y

data Timeout : Set where
  mkTimeout : PosixTime → Timeout

data ChoiceName : Set where
  mkChoiceName : ByteString → ChoiceName

unChoiceName : ChoiceName → ByteString
unChoiceName (mkChoiceName s) = s

_eqChoiceNameDec_ : DecidableEquality ChoiceName
_eqChoiceNameDec_ (mkChoiceName x) (mkChoiceName y) with x eqByteString y
... | yes p = yes (cong mkChoiceName p)
... | no ¬p = no (λ x → ¬p (cong unChoiceName x))

_eqChoiceName_ : ChoiceName → ChoiceName → Bool
c₁ eqChoiceName c₂ = ⌊ c₁ eqChoiceNameDec c₂ ⌋

record ChoiceId : Set where
  constructor mkChoiceId
  field
    name : ChoiceName
    party : Party

getChoiceName : ChoiceId → ChoiceName
getChoiceName (mkChoiceId n _) = n

getParty : ChoiceId → Party
getParty (mkChoiceId _ p) = p

_eqChoiceId_ : DecidableEquality ChoiceId
(mkChoiceId n₁ p₁) eqChoiceId (mkChoiceId n₂ p₂) with n₁ eqChoiceNameDec n₂ | p₁ eqPartyDec p₂
... | yes p | yes q = yes (cong₂ mkChoiceId p q)
... | _ | no ¬q = no λ x → ¬q (cong getParty x)
... | no ¬p | _ = no λ x → ¬p (cong getChoiceName x)

data Token : Set where
  mkToken : ByteString → ByteString → Token

_eqToken_ : Token → Token → Bool
_eqToken_ (mkToken xs xn) (mkToken ys yn) = ⌊ xs eqByteString ys ⌋ ∧ ⌊ xn eqByteString yn ⌋

record ValueId : Set where
  constructor mkValueId
  field
    getValueId : ByteString

_eqValueId_ : DecidableEquality ValueId
_eqValueId_ (mkValueId x) (mkValueId y) with (x eqByteString y)
... | yes p = yes (cong mkValueId p)
... | no ¬p = no (λ x → ¬p (cong getValueId x)) where open ValueId

data Observation : Set

data Value : Set where
  AvailableMoney : AccountId → Token → Value
  Constant : Int → Value
  NegValue : Value → Value
  AddValue : Value → Value → Value
  SubValue : Value → Value → Value
  MulValue : Value → Value → Value
  DivValue : Value → Value → Value
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

data Contract where
  Close : Contract
  Pay : AccountId → Payee → Token → Value → Contract → Contract
  If : Observation → Contract → Contract → Contract
  When : List Case → Timeout → Contract → Contract
  Let : ValueId → Value → Contract → Contract
  Assert : Observation → Contract → Contract


getAction : Case → Action
getAction (mkCase action _) = action
