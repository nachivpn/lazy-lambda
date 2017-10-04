module LazyNatSem where

open import Data.Nat
open import Data.List
open import Data.Product
open import Data.Maybe
open import Data.Vec



data Var : Set where
  name : ℕ → Var

data Exp  : Set where
  lambda  : Var → Exp → Exp
  _∙_     : Exp → Var → Exp
  var     : Var → Exp
  lEt_iN_ : List (Var × Exp) → Exp → Exp

Heap : Set
Heap = Var → Maybe Exp

-- data Val : Exp →  Set where

data _gives_ : Heap → Exp → Set where

data _[[_/_]] : Exp → Var → Var → Set where

-- data _⇓_ : _gives_ → _gives_ → Set where
--   app_red : {Γ Θ Δ : Heap} {x y z : Var} {e e' : Exp} → (Γ gives e) ⇓ (Δ gives (lambda y e')) → (Δ gives (e' [[ x / y ]])) ⇓ (Θ gives z) → (Γ gives (e ∙ x)) ⇓ (Θ gives z)

--   -- lambda_red : 

fun : ∀ {i} → Set i → Set i
fun A = A → A


