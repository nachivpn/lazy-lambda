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

-- data Val : Exp →  Set where

data Heap : Set where

data _has_ : Heap → Exp → Set where
  _∶_ : (H : Heap) → (E : Exp) → H has E

-- data subst_With_In_ : Var → Var → Exp → Set where
_[|_/_|] : (E : Exp) → (X Y : Var) → Exp
_[|_/_|] = {!!}

infix 30 _∶_
infix 20 _⇓_
infix 31 _[|_/_|]

data _⇓_ : {H₁ H₂ : Heap} → {E₁ E₂ : Exp} → H₁ has E₁ → H₂ has E₂ → Set where
   app_red : {Γ Θ Δ : Heap} {x y : Var} {e e' z : Exp} → Γ ∶ e ⇓ Δ ∶ lambda y e' → Δ ∶ e' [| x / y |] ⇓ Θ ∶ z → Γ ∶ (e ∙ x) ⇓ (Θ ∶ z)
   lam_red : {Γ : Heap} → {x : Var} → {e : Exp} → Γ ∶ lambda x e ⇓ Γ ∶ lambda x e  

{-
-- TODO: 
-- * Heap definition
-- * Remaining constructors (variable and let) {depends on heap defn}
-- * subst function
-- * prove simply labda caluclus evaluation: id x == x
-}

