module Term where

open import Prelude

Name = String
Pointer = Nat

data Term : Set where
  var : (x : Name) → Term
  _∙_ : (t u : Term) → Term 
  lam : (x : Name) → (t : Term) → Term

_↦_ : {A  B : Set} → A → B  → A × B
_↦_ = (_,_) 


Env : Set
Env = List (Name × Pointer)

isVal : Term → Set
isVal (var x) = ⊥
isVal (t ∙ t₁) = ⊥
isVal (lam x t) = ⊤

data Value : Set where
  lam : (x : Name) → (t : Term) → Value

data Closure : Set where
  _⟨_⟩ : Term → Env → Closure

Heap : Nat → Set
Heap = Vec Closure

_⊢_ : Set → Set → Set
H ⊢ C = H × C

_∶_ : {A  B : Set} → A → B  → A ⊢ B
_∶_ = (_,_)

_∣_↦_∣ : {A B : Set} → List (A × B) → A → B → List (A × B)
L ∣ a ↦ b ∣ = ( a , b ) ∷ L

x : Nat
x = 0

infix 10 _⇓_
infix 18 _∶_
infix 21 _⊢_
infix 21 _∣_↦_∣
infix 23 _⟨_⟩


-- constructive "belongs to" for vectors
data _∈v_ {A : Set} : {n : Nat} (x : A) → Vec A n → Set where
  zero : {m : Nat} {x : A} {xs : Vec A m}
    → x ∈v (x ∷ xs)
  suc  : {m : Nat} {x y : A} {xs : Vec A m}
    → (x ∈v xs) → x ∈v (y ∷ xs)

-- scope sensitive belongs
-- Unlike ∈, it does not allow scope insensitive proof of belongs
_∈s_ : (Name × Pointer) → Env → Set
np ∈s [] = ⊥
np ∈s (np' ∷ ρ') with np == np' 
... | yes refl = ⊤
... | no _     = np ∈s ρ'

-- indexed "belongs to"
_∈i_!_ : {n : Nat} → Closure → Heap n → Nat → Set
c ∈i H ! n = {!!}

private
  env : Env
  env = ("x", 1) ∷ ("z", 0) ∷( "x" , 0 ) ∷ []

  p₁ : ("x" , 1) ∈s env
  p₁ = tt

  -- this cannot be proved (◕‿◕)
  -- p₂ :  ("x" , 0) ∈s env
  -- p₂ = {!!}

data _⇓_ :  ∀ {m n} → Heap m ⊢ Closure → Heap n ⊢ Closure → Set where
  lam-red : ∀ {x t ρ} {n : Nat} {H : Heap n}
    → H ∶ lam x t ⟨ ρ ⟩ ⇓ H ∶ lam x t ⟨ ρ ⟩
    
  app-red : ∀ {t t₁ x u vc ρ ρ₁}
    {n n₁ n' : Nat} {H : Heap n} {H₁ : Heap n₁} {H' : Heap n'}
    → H ∶ t ⟨ ρ ⟩ ⇓ H₁ ∶ lam x t₁ ⟨ ρ₁ ⟩
    → (u ⟨ ρ ⟩ ∷ H₁) ∶ t₁ ⟨ ρ₁ ∣ x ↦ (suc n₁) ∣ ⟩ ⇓ H' ∶ vc 
    → H ∶ (t ∙ u) ⟨ ρ ⟩ ⇓ H' ∶ vc

  var-red : ∀ { x ρ tc vc} {p : Pointer}
   {n n' : Nat} {H : Heap n} {H' : Heap n'} { fp : Fin n }
   → (x , p) ∈s ρ
   → tc ∈i H ! p
   → H ∶ tc ⇓ H' ∶ vc
   → H ∶ var x ⟨ ρ ⟩ ⇓ (vc ∷ H') ∶ vc
  
  
  
  


