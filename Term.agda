module Term where

open import Prelude
open import Tactic.Deriving.Eq
open import Data.Nat

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
(n , p) ∈s [] = ⊥
(n , p) ∈s ((n' , p') ∷ ρ') with n == n' 
... | no _     = (n , p) ∈s ρ'
... | yes refl with p == p'
(n , p) ∈s ((.n , p') ∷ ρ') | yes refl | yes _ = ⊤
(n , p) ∈s ((.n , p') ∷ ρ') | yes refl | no _ = ⊥


postulate
  <_post₁ : (m n : Nat) → IsTrue (lessNat m n) → IsTrue (lessNat ((n -N m) -N 1) n)
  update-post : ∀ {n ρ} → ( "x" , n ) ∈s ρ ∣ "x" ↦ n ∣
  n<sucn : ∀ {n} → IsTrue (lessNat n (suc n))

-- indexed "belongs to"
data _at_≡_ {n : Nat} (m : Nat) ( H : Heap n) (c : Closure) : Set where
  indeed : (m<n : IsTrue (lessNat m n))
    → indexVec H (natToFin ((n -N m) -N 1) {{<_post₁ m n m<n}}) ≡ c
    → m at H ≡ c  

private
  env : Env
  env = ("y", 5) ∷ ("x", 1) ∷ ("z", 0) ∷( "x" , 0 ) ∷ []

  p₁ : ("x" , 1) ∈s env
  p₁ = tt

  -- this cannot be proved (◕‿◕)
  -- p₂ :  ("x" , 0) ∈s env
  -- p₂ = {!!}

  H : Heap 2
  H = var "y" ⟨ env ⟩ ∷ var ("x") ⟨ env ⟩ ∷ []

  p₃ : 0 at H ≡ var "x" ⟨ env ⟩
  p₃ = indeed true refl

-- shamelesly copied
_[_]≔_ : ∀ {a n} {A : Set a} → Vec A n → Fin n → A → Vec A n
[]       [ ()    ]≔ y
(x ∷ xs) [ zero  ]≔ y = y ∷ xs
(x ∷ xs) [ suc i ]≔ y = x ∷ xs [ i ]≔ y

data _⇓_ :  ∀ {m n} → Heap m ⊢ Closure → Heap n ⊢ Closure → Set where
  lam-red : ∀ {x t ρ} {n : Nat} {H : Heap n}
    → H ∶ lam x t ⟨ ρ ⟩ ⇓ H ∶ lam x t ⟨ ρ ⟩
    
  app-red : ∀ {t t₁ x u vc ρ ρ₁}
    {n n₁ n' : Nat} {H : Heap n} {H₁ : Heap n₁} {H' : Heap n'}
    → H ∶ t ⟨ ρ ⟩ ⇓ H₁ ∶ lam x t₁ ⟨ ρ₁ ⟩
    → (u ⟨ ρ ⟩ ∷ H₁) ∶ t₁ ⟨ ρ₁ ∣ x ↦ n₁ ∣ ⟩ ⇓ H' ∶ vc 
    → H ∶ (t ∙ u) ⟨ ρ ⟩ ⇓ H' ∶ vc

  var-red : ∀ { x ρ tc vc} {p : Pointer}
   {n n' : Nat} {H : Heap n} {H' : Heap n'}
   { fp : Fin n } {fp' : Fin n'}
   → (x , p) ∈s ρ
   → p at H ≡ tc
   → H ∶ tc ⇓ H' ∶ vc
   → H ∶ var x ⟨ ρ ⟩ ⇓ (H' [ fp' ]≔ vc) ∶ vc 
  

idF : Term
idF = lam "x" (var "x")

id∙id⇓id : {n : Nat} {ρ : Env} {H : Heap n} { H' : Heap (suc n)}
  → H ∶ (idF ∙ idF) ⟨ ρ ⟩ ⇓ (idF ⟨ ρ ⟩ ∷ H) ∶ idF ⟨ [] ⟩
id∙id⇓id {n} {ρ} {H} {H'} = app-red lam-red {!!}
  where
  p : n at (idF ⟨ ρ ⟩ ∷ H) ≡ idF ⟨ ρ ⟩
  p = {!!}
