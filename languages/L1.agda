module L1 where

open import Data.Nat
open import Data.String
open import Data.Unit
open import Data.List
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat.Base using (_∸_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
open import Relation.Binary using (Decidable)


-- Variables
Variable : Set
Variable = String

-- Values
Value : Set
Value = ℕ

-- Commands
data Command : Set where
  Return : Value -> Command
  Seq    : Variable -> Command -> Command -> Command
  Loop   : Value -> (Value -> Command) -> Command
  Read   : Variable -> Command
  Write  : Variable -> Value -> Command

-- definicja par wartości
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- stan do przechowywania w 'pamięci'
State : Set
State = List (Variable × Value)

-- funkcja do wyciągania wartości z pamięci (zakładam, że nasza maszyna to potrafi)
loookup : Variable -> State -> Value
loookup _ [] = 0
loookup x ((y , v) ∷ ys) with x
... | y = v
... | _ = loookup x ys

-- nadpisywanie/dopisywanie do pamięci (zakładam, że nasza maszyna to potrafi)
update : Variable -> Value -> State -> State
update x v [] = (x , v) ∷ []
update x v ((y , w) ∷ ys) with x
... | y = (x , v) ∷ ys
... | _ = (y , w) ∷ update x v ys


-- Small-step semantics dla L1
data StepL1 : Command × State -> Command × State -> Set where
  step-return : ∀ {v σ} →
    StepL1 (Return v , σ) (Return v , σ) -- komenda Return nie zmienia stanu

  step-seq1 : ∀ {x c1 c1' c2 σ σ'} → 
    StepL1 (c1 , σ) (c1' , σ') → -- o ile wiemy, że komenda c1 przechodzi w komende c1' zmieniając stan σ w stan σ'
    StepL1 (Seq x c1 c2 , σ) (Seq x c1' c2 , σ') -- wówczas komenda Seq 'uaktualnia się' o zmienioną komendę c1'

  step-seq2 : ∀ {x v c2 σ} →
    StepL1 ( (Seq x (Return v) c2) , σ) (c2 , (update x v σ)) -- gdy c1 stanie się komendą Return v, to zachowuje w pamięci stan (x , v)

  step-loop1 : ∀ {i f σ} →
    i > 0 →
    StepL1 (Loop i f , σ) (Seq "i" (f i) (Loop (i ∸ 1) f) , σ) -- wykonywanie pętli i razy, odłożenie wartości w pamięci

  step-loop2 : ∀ {f σ} →
    StepL1 (Loop 0 f , σ) (Return 0 , σ)

  step-read : ∀ {n σ} →
    StepL1 (Read n , σ) (( Return (loookup n σ) ,  σ))  -- wczytanie wartości z miejsca n

  step-write : ∀ {n v σ} →
    StepL1 (Write n v , σ) ((Return v), (update n v σ))  -- odłożenie wartości v w pamięci n

   

 