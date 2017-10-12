module Term where

open import Prelude

Name = String
Pointer = String

data Term : Set where
  var : (x : Name) → Term
  app : (t u : Term) → Term 
  lam : (x : Name) → (t : Term) → Term

_↦_ : {A  B : Set} → A → B  → A × B
_↦_ = (_,_) 

Env : Set
Env = List (Name × Pointer)

WNF : Term → Set
WNF (var x) = ⊥
WNF (app t t₁) = ⊥
WNF (lam x t) = ⊤

data VC : Set where
  vc : {t : Term} → WNF t → Env → VC

data TC : Set where
  tc : Term → Env → TC 

Heap : Set
Heap = List (Pointer × TC)
  
