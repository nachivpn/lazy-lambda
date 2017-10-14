module Term where

open import Prelude
open import Data.Nat
open import Tactic.Deriving.Eq

Name = String
Pointer = Nat

data Term : Set where
  var : (x : Name) → Term
  _∙_ : (t u : Term) → Term 
  lam : (x : Name) → (t : Term) → Term

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


unquoteDecl EqType₁ = deriveEq EqType₁ (quote Term)
unquoteDecl EqType₂ = deriveEq EqType₂ (quote Closure)

Heap : Nat → Set
Heap = Vec (Nat × Closure)

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
(n , p) ∈s [] = ⊥
(n , p) ∈s ((n' , p') ∷ ρ') with n == n' 
... | no _     = (n , p) ∈s ρ'
... | yes refl with p == p'
(n , p) ∈s ((.n , p') ∷ ρ') | yes refl | yes _ = ⊤
(n , p) ∈s ((.n , p') ∷ ρ') | yes refl | no _ = ⊥


postulate
  <_post₁ : (m n : Nat) → IsTrue (lessNat m n) → IsTrue (lessNat (n - m - 1) n)
  update-post : ∀ {n ρ} → ( "x" , n ) ∈s ρ ∣ "x" ↦ n ∣
  n<sucn : ∀ {n} → IsTrue (lessNat n (suc n))

private
  env : Env
  env = ("y", 5) ∷ ("x", 1) ∷ ("z", 0) ∷( "x" , 0 ) ∷ []

  p₁ : ("x" , 1) ∈s env
  p₁ = tt

  -- this cannot be proved (◕‿◕)
  -- p₂ :  ("x" , 0) ∈s env
  -- p₂ = {!!}

  H : Heap 2
  H = (1 , var "y" ⟨ env ⟩) ∷ ( 0 , var ("x") ⟨ env ⟩) ∷ []

  -- p₃ : ∈heap H 0 (var "x" ⟨ env ⟩)
  -- p₃ = tt

  idf : Term
  idf = lam "x" (var "x")

_[_]≔_ : ∀ {n} → Heap n → Nat → Closure → Heap n
[] [ n ]≔ y = []
(( n , c ) ∷ H) [ n' ]≔ c' with n == n' 
... | yes _ = (n , c') ∷ H
... | no _ = (n , c) ∷ (H [ n' ]≔ c')

data _⇓_ :  ∀ {m n} → Heap m ⊢ Closure → Heap n ⊢ Closure → Set where
  lam-red : ∀ {x t ρ} {n : Nat} {H : Heap n}
    → H ∶ lam x t ⟨ ρ ⟩ ⇓ H ∶ lam x t ⟨ ρ ⟩
    
  app-red : ∀ {t t₁ x u vc ρ ρ₁}
    {n n₁ n' : Nat} {H : Heap n} {H₁ : Heap n₁} {H' : Heap n'}
    → H ∶ t ⟨ ρ ⟩ ⇓ H₁ ∶ lam x t₁ ⟨ ρ₁ ⟩
    → ((n₁ , u ⟨ ρ ⟩) ∷ H₁) ∶ t₁ ⟨ ρ₁ ∣ x ↦ n₁ ∣ ⟩ ⇓ H' ∶ vc 
    → H ∶ (t ∙ u) ⟨ ρ ⟩ ⇓ H' ∶ vc

  var-red : ∀ { x ρ tc vc} {p : Pointer}
   {n n' : Nat} {H : Heap n} {H' : Heap n'}
   → (x , p) ∈s ρ
   → (p , tc) ∈v H
   → H ∶ tc ⇓ H' ∶ vc
   → H ∶ var x ⟨ ρ ⟩ ⇓ ((p , vc) ∷ H') ∶ vc 
  

idF : Term
idF = lam "x" (var "x")

id∙id⇓id : {n : Nat} {ρ : Env} {H : Heap n}
  → H ∶ (idF ∙ idF) ⟨ ρ ⟩ ⇓ ((n , idF ⟨ ρ ⟩) ∷ (n , idF ⟨ ρ ⟩) ∷ H) ∶ idF ⟨ ρ ⟩
id∙id⇓id {n} {ρ} {H} =
  app-red
    lam-red
      (var-red {!!}
      zero
      lam-red)
  where
  x↦n∈ρ : ∀ {ρ n} → ("x", n) ∈s (("x" ,  n ) ∷ ρ)
  x↦n∈ρ {[]} {zero} = tt
  x↦n∈ρ {[]} {suc zero} = tt
  x↦n∈ρ {[]} {suc (suc n₁)} = {!!} -- x↦n∈ρ {n = n₁}
  x↦n∈ρ {x₁ ∷ ρ₁} {zero} = tt
  x↦n∈ρ {x₁ ∷ ρ₁} {suc n₁} = {!!}
  
  
