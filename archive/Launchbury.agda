module LazyNatSem where

open import Prelude

data Var : Set where
  name : Nat → Var

data Exp  : Set where
  lambda  : Var → Exp → Exp
  _∙_     : Exp → Var → Exp
  var     : Var → Exp
  lEt_iN_ : List (Var × Exp) → Exp → Exp

Heap : Set
Heap = List (Var × Exp)

-- Heap entry
_↦_ : Var → Exp → Var × Exp
_↦_ = (_,_)

unname : Var → Nat
unname (name x) = x

var*2 : Var → Var
var*2 (name x₁) = name (x₁ * 2)
  
*2  : Exp → Exp
*2 (lambda x e) = lambda (var*2 x) (*2 e)
*2 (e ∙ name x) = (*2 e) ∙ name (2 * x)
*2 (var (name x)) = var (name (2 * x))
*2 (lEt x iN e) = lEt (renameList x) iN (*2 e)
  where
  renameList : List (Var × Exp) → List (Var × Exp)
  renameList [] = []
  renameList ((v , snd₁) ∷ xs) = (( var*2 v , *2 snd₁)) ∷ xs

-- Renaming function
α_ : Exp → Exp
α e = {!!}
  where
  -- Stateful auxiliary function
  α' : Nat → Exp → Exp
  α' n (lambda x e₁) = {!!}
  α' n (e₁ ∙ x) = {!!}
  α' n (var x) = {!!}
  α' n (lEt x iN e₁) = {!!}

-- "context of"
data _⊢_ : (H : Heap) (E : Exp) → Set where
  _∶_ : (H : Heap) → (E : Exp) → H ⊢ E

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

infix 21 _∶_
infix 20 _⇓_
infix 31 _[|_/_|]
infix 50 α_

data _⇓_ : {H₁ H₂ : Heap} {E₁ E₂ : Exp} → H₁ ⊢ E₁ → H₂ ⊢ E₂ → Set where

  app_red : {Γ Θ Δ : Heap} {x y : Var} {e e' z : Exp}
    → Γ ∶ e ⇓ Δ ∶ lambda y e' → Δ ∶ e' [| x / y |] ⇓ Θ ∶ z → Γ ∶ (e ∙ x) ⇓ (Θ ∶ z)
     
  lam_red : {Γ : Heap} {x : Var} {e : Exp}
    → Γ ∶ lambda x e ⇓ Γ ∶ lambda x e

  var_red : {Γ Δ : Heap} {e z : Exp} {x : Var}
    → Γ ∶ e ⇓ Δ ∶ z →  (x ↦ e ∷ Γ) ∶ var x ⇓ (x ↦ z ∷ Δ) ∶ α z



{-
-- TODO: 
-- * Remaining constructors (variable and let) {depends on heap defn}
-- * subst function
-- * prove simply labda caluclus evaluation: id x == x
-}

