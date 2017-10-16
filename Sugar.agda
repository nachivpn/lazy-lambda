module Sugar where

open import Prelude

_⊢_ : Set → Set → Set
H ⊢ C = H × C

_∶_ : {A  B : Set} → A → B  → A ⊢ B
_∶_ = (_,_)

_↦_ : {A B : Set} → (a : A) → (b : B) → A × B
a ↦ b = ( a , b )

_∣_∣ : {A : Set} → List A → A → List A
L ∣ x ∣ = x ∷ L

x : Nat
x = 1

y : Nat
y = 2

z : Nat
z = 3


infix 18 _∶_
infix 21 _⊢_
infix 21 _∣_∣
