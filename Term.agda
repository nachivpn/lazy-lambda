module Term where

open import Prelude
open import Data.Nat
open import Tactic.Deriving.Eq
open import Sugar

Name = Nat
Pointer = Nat

infixr 20 _∙_
data Term : Set where
  var : (x : Name) → Term
  _∙_ : (t u : Term) → Term 
  lam : (x : Name) → (t : Term) → Term

Env : Set
Env = List (Name × Pointer)

data Value : Set where
  lam : (x : Name) → (t : Term) → Value

infix 23 _⟨_⟩
data Closure : Set where
  _⟨_⟩ : Term → Env → Closure

Heap : Nat → Set
Heap = Vec (Pointer × Closure)

--------------------------------------------------------
---------- Constructive types for scoping proofs -------
--------------------------------------------------------

¬[_] : ∀ {a b : Nat} → Dec (a ≡ b) → Set
¬[ (yes x₁) ] = ⊥
¬[ (no x₁) ] = ⊤

_¬≡_ : ( a b : Nat) → Set
a ¬≡ b = ¬[ a == b ]

-- "belongs to" for vectors
data _∈v_ {A : Set} (x : A): {n : Nat} → Vec A n → Set where
  zero : ∀ {m : Nat} {xs : Vec A m}
    → x ∈v (x ∷ xs)
  suc  : {m : Nat} {y : A} {xs : Vec A m}
    → (x ∈v xs) → x ∈v (y ∷ xs)

-- scope sensitive "belongs to" type for Heap
data _↦_∈h_ (p : Pointer) (c : Closure) : {n : Nat} → Heap n → Set where
  zero : ∀ {m : Nat} {xs : Heap m}
    → p ↦ c ∈h ((p , c) ∷ xs)
  suc  : ∀ {m : Nat} {xs : Heap m} {p' c'} {pr : p ¬≡ p'}
    → (p ↦ c ∈h xs) → p ↦ c ∈h ((p' , c') ∷ xs)

-- scope sensitive "belongs to" type for environment
data _↦_∈e_ (n : Name) (p : Pointer) : Env → Set where
  zero : ∀ {xs}            → n ↦ p ∈e ((n , p) ∷ xs)
  suc  : ∀ {n' : Name} { p' xs} {pr : n ¬≡ n'}
    → n ↦ p ∈e xs → n ↦ p ∈e ((n' , p') ∷ xs)


--------------------------------------
-- Common terms and proof utilities --
--------------------------------------

idF : Term
idF = lam x (var x)


private
  env : Env
  env = (y , 5) ∷ (x , 1) ∷ (z , 0) ∷(x , 0 ) ∷ []

  p₁ : x ↦ 1 ∈e env
  p₁ = suc zero

  -- type checker complains! (ﾉ◕ヮ◕)ﾉ*:･ﾟ✧
  -- p₂ : x ↦ 0 ∈e env
  -- p₂ = suc (suc (suc zero))

  H : Heap 3
  H = (2 , var y ⟨ env ⟩) ∷ ( 0 , var x ⟨ env ⟩) ∷ (2 , var z ⟨ env ⟩) ∷ []

  p₃ : 0 ↦ var x ⟨ env ⟩ ∈h H
  p₃ = suc zero

  p₄ : 2 ↦ var y ⟨ env ⟩ ∈h H
  p₄ = zero

  --  type checker complains!
  -- p₅ : 2 ↦ var z ⟨ env ⟩ ∈h H
  -- p₅ = suc (suc zero)
  
