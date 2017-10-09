module LazyNatSem where

open import Prelude.Bool
open import Prelude.Nat
open import Prelude.List
open import Prelude.Product
open import Prelude.Maybe
open import Prelude.Vec


data Var : Set where
  name : Nat → Var

data Exp  : Set where
  lambda  : Var → Exp → Exp
  _∙_     : Exp → Var → Exp
  var     : Var → Exp
  lEt_iN_ : List (Var × Exp) → Exp → Exp

data Heap : Set where

data _has_ : Heap → Exp → Set where
  _∶_ : (H : Heap) → (E : Exp) → H has E


_Var₌₌_ : Var → Var → Bool
_Var₌₌_ (name x) (name x₁) = eqNat x x₁


{-# NON_TERMINATING #-}
_[|_/_|] : (E : Exp) → (X Y : Var) → Exp
lambda mvar mexp [| X / Y |] = if mvar Var₌₌ Y then lambda mvar mexp else lambda mvar (mexp [| X / Y |])
(mexp ∙ xvar) [| X / Y |] = (mexp [| X / Y |]) ∙ (if (xvar Var₌₌ Y) then X else xvar)
var mvar [| X / Y |] = if mvar Var₌₌ Y then var X else var mvar
(lEt x iN E) [| X / Y |] = lEt (map (λ x₁ → if ((fst x₁) Var₌₌ Y) then x₁ else ((fst x₁) , ((snd x₁) [| X / Y |]))) x) iN (E [| X / Y |])

tstExp1 : Exp
tstExp1 = lambda (name 1) (((var (name 0)) ∙ ( (name 1))) ∙ ((name 2)))

-- tstExp1 [| (name 1)  / (name 0) |]

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

