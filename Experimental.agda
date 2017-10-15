module Experimental where


open import Prelude
open import Term

_[_]≔_ : ∀ {n} → Heap n → Nat → Closure → Heap n
[] [ n ]≔ y = []
(( n , c ) ∷ H) [ n' ]≔ c' with n == n' 
... | yes _ = (n , c') ∷ H
... | no _ = (n , c) ∷ (H [ n' ]≔ c')


_==n_ : Nat → Nat → Bool
zero ==n zero = true
zero ==n suc n = false
suc m ==n zero = false
suc m ==n suc n = m ==n n

-- scope sensitive belongs
-- Unlike ∈, it does not allow scope insensitive proof of belongs
_∈s_ : (Name × Pointer) → Env → Set
(n , p) ∈s [] = ⊥
(n , p) ∈s ((n' , p') ∷ ρ') with n ==n n' | p ==n p'
... | false | _     = ( n , p ) ∈s ρ'
... | _     | false = ⊥
... | true  | true  = ⊤

private
  env : Env
  env = (y , 5) ∷ (x , 1) ∷ (z , 0) ∷(x , 0 ) ∷ []

  p₁ : (x , 1) ∈s env
  p₁ = tt

  -- this cannot be proved (◕‿◕)
  -- p₂ :  (x , 0) ∈s env
  -- p₂ = {!!}
