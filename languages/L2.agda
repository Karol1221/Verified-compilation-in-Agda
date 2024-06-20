module L2 where

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

Variable : Set
Variable = String


Value : Set
Value = ℕ

data Exp : Set where
    Var : Variable -> Exp
    Const : Value -> Exp
    Plus : Exp -> Exp -> Exp
    Deref : Exp -> Exp

data Stmt : Set where
    Skip : Stmt
    Assign : Variable -> Exp -> Stmt
    Store : Exp -> Exp -> Stmt
    Seq : Stmt -> Stmt -> Stmt
    If : Exp -> Stmt -> Stmt -> Stmt
    While : Exp -> Stmt -> Stmt

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

-- Small-step semantics dla expressions
data StepExp : Exp × State -> Exp × State -> Set where
  step-plus1 : ∀ {e1 e1' e2 σ σ'} →
    StepExp (e1 , σ) (e1' , σ') →
    StepExp (Plus e1 e2 , σ) (Plus e1' e2 , σ') -- ewaluacja pod plusem

  step-plus2 : ∀ {v1 e2 e2' σ σ'} →
    StepExp (e2 , σ) (e2' , σ') →
    StepExp (Plus (Const v1) e2 , σ) (Plus (Const v1) e2' , σ') -- kolejność ewaluacji najpierw lewa potem prawa

  step-plus3 : ∀ {v1 v2 σ} →
    StepExp (Plus (Const v1) (Const v2) , σ) (Const (v1 + v2) , σ) -- ewaluacja plusa na normalne dodawanie, gdy dwie wartości są stałymi

  step-deref1 : ∀ {e e' σ σ'} →
    StepExp (e , σ) (e' , σ') →
    StepExp (Deref e , σ) (Deref e' , σ') -- ewaluacja pod Deref

  step-deref2 : ∀ {x σ} →
    StepExp ( (Deref (Var x)) , σ) (Const (loookup x σ) , σ) -- określenie działania Deref

-- Small-step semantics dla statements
data StepStmt : Stmt × State -> Stmt × State -> Set where
  step-assign1 : ∀ {x e e' σ σ'} →
    StepExp (e , σ) (e' , σ') →
    StepStmt (Assign x e , σ) (Assign x e' , σ') -- ewaluacja po Assign

  step-assign2 : ∀ {x v σ} →
    StepStmt (Assign x (Const v) , σ) (Skip , update x v σ) -- określenie działania Assign

  step-store1 : ∀ {e1 e1' e2 σ σ'} →
    StepExp (e1 , σ) (e1' , σ') →
    StepStmt (Store e1 e2 , σ) (Store e1' e2 , σ') -- kolejność ewaluacji najpierw lewa potem prawa

  step-store2 : ∀ {v1 e2 e2' σ σ'} →
    StepExp (e2 , σ) (e2' , σ') →
    StepStmt (Store (Var v1) e2 , σ) (Store (Var v1) e2' , σ') -- kolejność ewaluacji najpierw lewa potem prawa

  step-store3 : ∀ {v1 v2 σ} →
    StepStmt (Store (Var v1) (Const v2) , σ) (Skip , update v1 v2 σ) -- działanie Store

  step-seq1 : ∀ {s1 s1' s2 σ σ'} →
    StepStmt (s1 , σ) (s1' , σ') →
    StepStmt (Seq s1 s2 , σ) (Seq s1' s2 , σ') -- kolejność ewaluacji najpierw lewa potem prawa 

  step-seq2 : ∀ {s2 σ} →
    StepStmt (Seq Skip s2 , σ) (s2 , σ) -- Skip przechodzi do następnej komendy nie zmienia pamięci

  step-if1 : ∀ {e e' s1 s2 σ σ'} →
    StepExp (e , σ) (e' , σ') →
    StepStmt (If e s1 s2 , σ) (If e' s1 s2 , σ') -- kolejność ewaluacji najpierw lewa potem prawa

  step-iftrue : ∀ {s1 s2 σ} →
    StepStmt (If (Const 0) s1 s2 , σ) (s2 , σ) -- jeżeli fałsz to wykona się druga komenda

  step-iffalse : ∀ {s1 s2 σ} →
    StepStmt (If (Const (suc 0)) s1 s2 , σ) (s1 , σ) -- jeżeli prawda to pierwsza

  step-while : ∀ {e s σ} →
    StepStmt (While e s , σ) (If e (Seq s (While e s)) Skip , σ) -- definicja while za pomocą If