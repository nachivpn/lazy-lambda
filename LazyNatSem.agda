
module LazyNatSem where

open import Prelude


data Var : Set where
  name : Nat → Var

_Var₌₌_ : Var → Var → Bool
_Var₌₌_ (name x) (name x₁) = eqNat x x₁

data UExp  : Set where
  ulambda  : Var → UExp → UExp
  _u∙_     : UExp → UExp → UExp
  uvar     : Var → UExp
  ulet_iN_ : List (Var × UExp) → UExp → UExp

data Exp  : Set where
  lambda  : Var → Exp → Exp
  _∙_     : Exp → Var → Exp
  var     : Var → Exp
  lEt_iN_ : List (Var × Exp) → Exp → Exp

data Heap : Set where
  [] : Heap
  _∷_ : Var × Exp → Heap → Heap

record Distinct-Exp : Set where
  field
    teh-exp : Exp
    teh-lookup  : List (Var × Nat)


data _entails_ : Heap → Exp → Set where
  _⊢_ : (H : Heap) → (E : Exp) → H entails E

lookup_in-heap_ : (X : Var) → (H : Heap) → Maybe Exp
lookup X in-heap [] = nothing
lookup X in-heap ((fst₁ , snd₁) ∷ H) = if X Var₌₌ fst₁ then just snd₁ else lookup X in-heap H


{-# NON_TERMINATING #-}
_[|_/_|] : (E : Exp) → (X Y : Var) → Exp
lambda mvar mexp [| X / Y |] = if mvar Var₌₌ Y then lambda mvar mexp else lambda mvar (mexp [| X / Y |])
(mexp ∙ xvar) [| X / Y |] = (mexp [| X / Y |]) ∙ (if (xvar Var₌₌ Y) then X else xvar)
var mvar [| X / Y |] = if mvar Var₌₌ Y then var X else var mvar
(lEt x iN E) [| X / Y |] = lEt (map (λ x₁ → if ((fst x₁) Var₌₌ Y) then x₁ else ((fst x₁) , ((snd x₁) [| X / Y |]))) x) iN (E [| X / Y |])

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

umax : UExp → Nat
umax (ulambda x x₁) = max (umax x₁) (unname x)
umax (x u∙ x₁) = max (umax x) (umax x₁)
umax (uvar x) = unname x
umax (ulet x iN x₁) = {!!}


{-# NON_TERMINATING #-}
emax : Exp → Nat
emax (lambda x x₁) = max (emax x₁) (unname x)
emax (x ∙ x₁) = max (emax x) (emax (var x₁))
emax (var x) = unname x
emax (lEt x iN x₁) with esplit x
... | t with foldN 0 (map emax (snd t))
... | w with foldN 0 (map unname (fst t))
... | q = max w q

x = (name 1)
y = (name 2)
z = (name 3)
w = (name 4)



testα = ((uvar y) u∙ (ulambda x (uvar z))) u∙ ulambda x (ulambda y (ulambda z (ulambda x (((uvar y) u∙ (uvar x)) u∙ (uvar x)))))
testα2 = (ulambda x (((uvar y) u∙ (uvar x)) u∙ (uvar x)))
testα3 : UExp
testα3 = ulet (y , (uvar z)) ∷ [] iN ulambda x (uvar y)

stack = List Var
vlookup = List (Var × Nat)

remove_from_ : Var → vlookup → vlookup
remove x from [] = []
remove x from ((fst₁ , snd₁) ∷ x₂) = if (x Var₌₌ fst₁) then (remove x from x₂) else ((fst₁ , snd₁) ∷ (remove x from x₂))

_belongsto_ :  Var → List Var → Bool
x belongsto [] = false
x belongsto (x₁ ∷ x₂) = if x Var₌₌ x₁ then true else x belongsto x₂

_lookupvn_ : Var → vlookup → Maybe Nat
x lookupvn [] = nothing
x lookupvn ((fst₁ , snd₁) ∷ x₂) = if (x Var₌₌ fst₁) then just snd₁ else (x lookupvn x₂)

pop_ : List (Var) → List (Var)
pop [] = []
pop (x₁ ∷ x₂) = x₂

_stack-append_ : stack → stack → stack
_stack-append_ [] x₁ = x₁
_stack-append_ (x₂ ∷ x₃) x₁ = x₂ ∷ (x₃ stack-append x₁)

count-vars : Exp → Nat
count-vars (lambda x₁ x₂) = 1 + count-vars x₂
count-vars (x₁ ∙ x₂) = count-vars x₁ + 1
count-vars (var x₁) = 1
count-vars (lEt [] iN x₂) = count-vars x₂
count-vars (lEt (fst₁ , snd₁) ∷ x₃ iN x₂) = 1 + count-vars snd₁ + count-vars (lEt x₃ iN x₂)

sumN : List Nat → Nat
sumN [] = 0
sumN (x₁ ∷ x₂) = x₁ + sum x₂

α-rename-var : Var → Nat  → (List (Var × Nat)) → (Var × (List (Var × Nat)))
α-rename-var x cc lkup with x lookupvn lkup
... | nothing = ((name (cc))) , ((x ,  cc) ∷ lkup)
... | just x₁ = ((name x₁)) , lkup
-- ... | newexp , newlkup with α-rename x₂ cc newlkup
-- ... | newexp2 , newlkup2 = (newexp2 u∙ newexp) , newlkup2
-- with name x₂ lookupvn lkup
-- ... | nothing = (uvar (name (cc))) , ((name x₂ ,  cc) ∷ lkup)
-- ... | just x₁ = (uvar (name x₁)) , lkup

α-rename : Exp → Nat → (List (Var × Nat)) → Distinct-Exp
α-rename (lambda x₂ x₃) cc lkup with α-rename x₃ (cc + 1) lkup
... | newexp with x₂ lookupvn Distinct-Exp.teh-lookup newexp
... | nothing = record { teh-exp = (lambda (name cc) (Distinct-Exp.teh-exp newexp)) ; teh-lookup = Distinct-Exp.teh-lookup newexp}
... | just x₁ = record {teh-exp = (lambda (name x₁) (Distinct-Exp.teh-exp newexp)) ; teh-lookup = (remove x₂ from Distinct-Exp.teh-lookup newexp)}
α-rename (x₂ ∙ x₃) cc lkup  with count-vars x₂
... | c-vars-in-x₂ with α-rename-var x₃ (c-vars-in-x₂ + cc) lkup
... | newx₃ , newlkup with α-rename x₂ cc newlkup
... | newx₂ = record {teh-exp = ((Distinct-Exp.teh-exp newx₂) ∙ newx₃) ; teh-lookup = Distinct-Exp.teh-lookup newx₂}
α-rename (var x₂) cc lkup with α-rename-var x₂ cc lkup
... | newx₂ , newlkup = record {teh-exp = (var newx₂) ; teh-lookup = newlkup}
α-rename (lEt x₁ iN x₂) cc lkup with snd (esplit x₁)
... | t with length x₁ + (sumN (map count-vars t))
... | t2 with α-rename x₂ (cc + t2) lkup
... | t3 = record {teh-exp = (lEt fst (letα-rename x₁ cc (Distinct-Exp.teh-lookup t3)) iN (Distinct-Exp.teh-exp t3)) ; teh-lookup = snd (letα-rename x₁ cc (Distinct-Exp.teh-lookup t3))}
  where
    letα-rename : List (Var × Exp) → Nat → List (Var × Nat) → (List (Var × Exp)) × (List (Var × Nat))
    letα-rename [] x₁ x₂ = [] , x₂
    letα-rename (x₃ ∷ x₄) x₁ x₂ with letα-rename x₄ (x₁ + (count-vars (snd x₃) + 1)) x₂
    ... | t with α-rename (snd x₃) (1 + x₁) (snd t)
    ... | t2 with (fst x₃) lookupvn (Distinct-Exp.teh-lookup t2)
    ... | nothing = ((name x₁ , Distinct-Exp.teh-exp t2) ∷ fst t) , (fst x₃ , x₁) ∷ snd t
    ... | just t3 = ((name t3 , Distinct-Exp.teh-exp t2) ∷ fst t) , snd t


{-# NON_TERMINATING #-}
starTransform : UExp → Exp
starTransform (ulambda x x₁) = lambda x (starTransform x₁)
starTransform (uvar x) = var x
starTransform (e₁ u∙ e₂) = lEt (name (suc (max (umax e₂) (umax e₁))) , (starTransform e₂)) ∷ [] iN (starTransform e₁ ∙ name ((suc (max (umax e₂) (umax e₁)))))
starTransform (ulet x₁ iN x₂) with usplit x₁
... | t = lEt (zip (fst t) (map starTransform (snd t))) iN (starTransform x₂)



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

hat_with-regards-to_ : Exp → Heap → Exp
hat x with-regards-to x₁ = Distinct-Exp.teh-exp (α-rename x {!!} {!!})

infix 33 _extendedby_
infix 34 hat_with-regards-to_



data _⇓_ : {H₁ H₂ : Heap} → {E₁ E₂ : Exp} → H₁ entails E₁ → H₂ entails E₂ → Set where
  lam-red : {Γ : Heap} → {x : Var} → {e : Exp} → Γ ⊢ lambda x e ⇓ Γ ⊢ lambda x e

  app-red : {Γ Θ Δ : Heap} {x y : Var} {e e' z : Exp} →
    Γ ⊢ e ⇓ Δ ⊢ lambda y e'                →                 Δ ⊢ e' [| x / y |] ⇓ Θ ⊢ z →
-- ---------------------------------------------------------------------------------------------
                                  Γ ⊢ (e ∙ x) ⇓ (Θ ⊢ z)
  var-red : {Γ Δ : Heap} { x y : Var} {e z : Exp} →
    Γ ⊢ e ⇓ Δ ⊢ z →
    Γ extendedby ((x , e) ∷ []) ⊢ var x ⇓ Δ extendedby ( (x , z) ∷ []) ⊢ hat z with-regards-to Δ

  lEt-red : {Γ Δ : Heap} {e z : Exp} {TT : List (Var × Exp)} →
    Γ extendedby TT ⊢ e   ⇓ Δ ⊢ z →
    Γ ⊢ lEt TT iN e       ⇓ Δ ⊢ z

data Value : Set where
  Fn_ : Value
  _↓Fn_ : Value → Value →  Value

Env = List (Var × Value)

ρ : Env → Var → Value
ρ = {!!}

||_||with-env_ : Exp → Env → Value
|| lambda x₂ x₃ ||with-env x₁ = {!!}
|| x₂ ∙ x₃ ||with-env x₁ = (|| x₂ ||with-env x₁) ↓Fn ρ x₁ x₃
|| var x₂ ||with-env x₁ = ρ x₁ x₂
|| lEt x₂ iN x₃ ||with-env x₁ = || x₃ ||with-env {!!}

postulate
  three+two : Exp
  five six : Exp
  U V X Y : Var
  U+one V+V : Exp
  P : ∀ {Γ Δ} → (Γ  ⊢ three+two) ⇓ (Δ ⊢ five)

uexp1 : UExp
uexp1 = ulet (y , (uvar z)) ∷ [] iN ulambda x (uvar y)


ex1 : Distinct-Exp
ex1 = α-rename (starTransform uexp1) (0) []


