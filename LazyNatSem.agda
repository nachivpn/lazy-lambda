
module LazyNatSem where

open import Prelude.Bool
open import Prelude.Maybe
open import Prelude.Nat
open import Prelude.List
open import Prelude.Product
open import Prelude.Maybe
open import Prelude.Vec


data Var : Set where
  name : Nat → Var


_Var₌₌_ : Var → Var → Bool
_Var₌₌_ (name x) (name x₁) = eqNat x x₁

data UExp  : Set where
  ulambda  : Var → UExp → UExp
  _u∙_     : UExp → UExp → UExp
  uvar     : Var → UExp
  ulEt_iN_ : List (Var × UExp) → UExp → UExp


data Exp  : Set where
  lambda  : Var → Exp → Exp
  _∙_     : Exp → Var → Exp
  var     : Var → Exp
  lEt_iN_ : List (Var × Exp) → Exp → Exp

data Heap : Set where
  [] : Heap
  _∷_ : Var × Exp → Heap → Heap



lookupH : Var → Heap → Maybe Exp
lookupH x [] = nothing
lookupH x (x₁ ∷ x₂) = if x Var₌₌ (fst x₁) then just (snd x₁) else lookupH x x₂


data _entails_ : Heap → Exp → Set where
  _⊢_ : (H : Heap) → (E : Exp) → H entails E


tstloop : Exp
tstloop = lEt ((name 0) , (lambda (name 1) ((var (name 1)) ∙ (name 1)))) ∷ [] iN (lambda (name 0) ((var (name 0)) ∙ (name 0)) ∙ (name 0))

sub_for_lEt_iN_wIth_ : Var → Var → List (Var × Exp) →  Exp → List Var → Exp
sub X for Y lEt x iN exp wIth bounds = {!!}

{-# NON_TERMINATING #-}
_[|_/_|] : (E : Exp) → (X Y : Var) → Exp
lambda mvar mexp [| X / Y |] = if mvar Var₌₌ Y then lambda mvar mexp else lambda mvar (mexp [| X / Y |])
(mexp ∙ xvar) [| X / Y |] = (mexp [| X / Y |]) ∙ (if (xvar Var₌₌ Y) then X else xvar)
var mvar [| X / Y |] = if mvar Var₌₌ Y then var X else var mvar
-- (lEt x iN E) [| X / Y |] = lEt (map (λ x₁ → (fst x₁) , ((snd x₁) [| X / Y |])) x) iN (E [| X / Y |])
(lEt x iN E) [| X / Y |] = lEt (map (λ x₁ → if ((fst x₁) Var₌₌ Y) then x₁ else ((fst x₁) , ((snd x₁) [| X / Y |]))) x) iN (E [| X / Y |])

tstExp1 : Exp
tstExp1 = lambda (name 1) (((var (name 0)) ∙ ( (name 1))) ∙ ((name 2)))

tstExp2 : Exp
tstExp2 = lambda (name 0) (var (name 0) ∙ ((name 0)))

tstExp3 : Exp → Exp
tstExp3 e1 = lEt ((name 0) , tstExp1) ∷ [] iN tstExp2

max : Nat → Nat → Nat
max zero x₁ = x₁
max (suc x) zero = suc x
max (suc x) (suc x₁) = suc (max x x₁)

unname : Var → Nat
unname (name x) = x

usplit : List (Var × UExp) → (List Var) × (List UExp)
usplit [] = [] , []
usplit (x ∷ x₁) = (fst x ∷ fst (usplit x₁)) , ((snd x ∷ snd (usplit x₁)))

esplit : List (Var × Exp) → (List Var) × (List Exp)
esplit [] = [] , []
esplit (x ∷ x₁) = (fst x ∷ fst (esplit x₁)) , ((snd x ∷ snd (esplit x₁)))

foldN : Nat → List Nat → Nat
foldN x [] = x
foldN x (x₁ ∷ x₂) = max x (max x₁ (foldN x x₂))

{-# NON_TERMINATING #-}
umax : UExp → Nat
umax (ulambda x x₁) = max (umax x₁) (unname x)
umax (x u∙ x₁) = max (umax x) (umax x₁)
umax (uvar x) = unname x
umax (ulEt x iN x₁) with usplit x
... | t with foldN 0 (map umax (snd t))
... | w with foldN 0 (map unname (fst t))
... | q = max w q

{-# NON_TERMINATING #-}
emax : Exp → Nat
emax (lambda x x₁) = max (emax x₁) (unname x)
emax (x ∙ x₁) = max (emax x) (emax (var x₁))
emax (var x) = unname x
emax (lEt x iN x₁) with esplit x
... | t with foldN 0 (map emax (snd t))
... | w with foldN 0 (map unname (fst t))
... | q = max w q


{-# NON_TERMINATING #-}
starTransform : UExp → Exp
starTransform (ulambda x x₁) = lambda x (starTransform x₁)
starTransform (uvar x) = var x
starTransform (ulEt x iN x₁) = lEt (map (λ x₂ → (fst x₂) , starTransform (snd x₂)) x) iN starTransform x₁
starTransform (e₁ u∙ uvar x) = starTransform e₁ ∙ x
starTransform (e₁ u∙ e₂) = lEt (name (suc (max (umax e₂) (umax e₁))) , (starTransform e₂)) ∷ [] iN (starTransform e₁ ∙ name ((suc (max (umax e₂) (umax e₁)))))

M N F X U V : Var
X = name 0
F = name 1
M = name 2
N = name 3
U = name 4
V = name 5
Y = name 6


uone utwo uthree uadd : UExp
uone = ulambda F (ulambda X (uvar F u∙ uvar X))
utwo = ulambda F (ulambda X (uvar F u∙ uone))
uthree = ulambda F (ulambda X (uvar F u∙ utwo))
uadd = ulambda M (ulambda N (ulambda F (ulambda X (uvar M u∙ (uvar F u∙ (uvar N u∙  (uvar F u∙ uvar X)))))))

one two three add : Exp
one = starTransform utwo
two = starTransform utwo
three = starTransform utwo
add = starTransform utwo
two+three = starTransform ((uadd u∙ utwo) u∙ uthree)
U+one = starTransform ((uadd u∙ (uvar U)) u∙ uone)
V+U = starTransform ((uadd u∙ (uvar U)) u∙ (uvar V))

ex1 : Exp
ex1 = lEt (U , two+three) ∷ (V , U+one) ∷ [] iN ((V+U))

-- tstExp1 [| (name 1)  / (name 0) |]

infix 30 _⊢_
infix 20 _⇓_
infix 31 _[|_/_|]
infix 32 lEt_iN_


_extendby_ : Heap → Var × Exp → Heap
[] extendby x₁ = x₁ ∷ []
((fst₂ , snd₂) ∷ x₂) extendby (fst₁ , snd₁) = if fst₁ Var₌₌ fst₁ then ( fst₂ , snd₁ ) ∷ x₂ else (fst₂ , snd₂) ∷ (x₂ extendby ( fst₁ , snd₁ ))

-- postulate _extendedby_ : Heap → List (Var × Exp) → Heap
_extendedby_ : Heap → List (Var × Exp) → Heap
x extendedby [] = x
x extendedby (x₁ ∷ x₂) = (x extendby x₁) extendedby x₂
-- x extendedby (x₁ ∷ x₂) = ((fst x₁) , (snd x₁)) ∷ x extendedby x₂

-- postulate hat : Var → Exp → Var
hat : Var → Heap → Var
hat x [] = name 0
hat x ((fst₁ , snd₁) ∷ x₂) = name (max (unname (hat x x₂)) (max (unname fst₁) (emax snd₁)))

infix 33 _extendedby_
infix 34 hat



data _⇓_ : {H₁ H₂ : Heap} → {E₁ E₂ : Exp} → H₁ entails E₁ → H₂ entails E₂ → Set where
  app_red : {Γ Θ Δ : Heap} {x y : Var} {e e' z : Exp} →
    Γ ⊢ e ⇓ Δ ⊢ lambda y e'                →                 Δ ⊢ e' [| x / y |] ⇓ Θ ⊢ z →
                                  Γ ⊢ (e ∙ x) ⇓ (Θ ⊢ z)
  lam_red : {Γ : Heap} → {x : Var} → {e : Exp} → Γ ⊢ lambda x e ⇓ Γ ⊢ lambda x e
  var_red : {Γ Θ Δ : Heap} { x y z : Var} {e : Exp} →
    Γ ⊢ e ⇓ Δ ⊢ var z →
    Δ extendedby ((x , e) ∷ []) ⊢ var x ⇓ Δ extendedby ( (x , var z) ∷ []) ⊢ var (hat z (Δ extendedby ( (x , var z) ∷ [])))
  lEt_red : {Γ Δ : Heap} {x y : Var} {e z : Exp} {TT : List (Var × Exp)} →
    Γ extendedby TT ⊢ e   ⇓ Δ ⊢ z →
    Γ ⊢ lEt TT iN e       ⇓ Δ ⊢ z

evalsteplet : {Γ : Heap} {e : Exp} {TT : List (Var × Exp)}  → Γ entails (lEt TT iN e) → Γ extendedby TT entails e
evalsteplet {.H} {e} {TT} (H ⊢ .(lEt TT iN e)) = H extendedby TT ⊢ e

evalstepapp : {Γ Θ Δ : Heap} {x y : Var} {e e' z : Exp} → Γ entails (e ∙ x) → Γ extendedby ((x , e) ∷ []) entails (lEt [] iN e)
evalstepapp = {!!}

-- evalsteplamb : {Γ : Heap} → {x : Var} → {e : Exp} → Γ entails lambda x e → Γ entails lambda x e
-- evalsteplamb (H ⊢ .(lambda _ _)) = {!!}


{-
-- TODO: 
-- * Heap definition
-- * Remaining constructors (variable and let) {depends on heap defn}
-- * subst function
-- * prove simply labda caluclus evaluation: id x == x
-}

