module Sugar where

open import Prelude

_⊢_ : Set → Set → Set
H ⊢ C = H × C

_∶_ : {A  B : Set} → A → B  → A ⊢ B
_∶_ = (_,_)

_∣_↦_∣ : {A B : Set} → List (A × B) → A → B → List (A × B)
L ∣ a ↦ b ∣ = ( a , b ) ∷ L

x : Nat
x = 1

y : Nat
y = 2

z : Nat
z = 3


infix 18 _∶_
infix 21 _⊢_
infix 21 _∣_↦_∣
