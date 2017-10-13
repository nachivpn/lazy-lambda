
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


data Exp  : Set where
  lambda  : Var → Exp → Exp
  _∙_     : Exp → Var → Exp
  var     : Var → Exp
  lEt_iN_ : List (Var × Exp) → Exp → Exp

data Heap : Set where
  [] : Heap
  _∷_ : Var × Exp → Heap → Heap



data _entails_ : Heap → Exp → Set where
  _⊢_ : (H : Heap) → (E : Exp) → H entails E


_[|_/_|] : (E : Exp) → (X Y : Var) → Exp
_[|_/_|] = {!!}

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

count-vars_ : UExp → Nat
count-vars ulambda x₁ x₂ = 1 + count-vars x₂
count-vars (x₁ u∙ x₂) = count-vars x₁ + count-vars x₂
count-vars uvar x₁ = 1

α-rename : UExp → Nat → (List (Var × Nat)) → (UExp × (List (Var × Nat)))
α-rename (ulambda x₂ x₃) cc lkup with α-rename x₃ (cc + 1) lkup
... | newexp , newlkup with x₂ lookupvn newlkup
... | nothing = (ulambda (name cc) newexp) , newlkup
... | just x₁ = (ulambda (name x₁) newexp) , (remove x₂ from newlkup)
α-rename (x₂ u∙ x₃) cc lkup  with count-vars x₂
... | t with α-rename x₃ (t + cc) lkup
... | newexp , newlkup with α-rename x₂ cc newlkup
... | newexp2 , newlkup2 = (newexp2 u∙ newexp) , newlkup2
α-rename (uvar (name x₂)) cc lkup with name x₂ lookupvn lkup
... | nothing = (uvar (name (cc))) , ((name x₂ ,  cc) ∷ lkup)
... | just x₁ = (uvar (name x₁)) , lkup

{-# NON_TERMINATING #-}
starTransform : UExp → Exp
starTransform (ulambda x x₁) = lambda x (starTransform x₁)
starTransform (uvar x) = var x
starTransform (e₁ u∙ uvar x) = starTransform e₁ ∙ x
starTransform (e₁ u∙ e₂) = lEt (name (suc (max (umax e₂) (umax e₁))) , (starTransform e₂)) ∷ [] iN (starTransform e₁ ∙ name ((suc (max (umax e₂) (umax e₁)))))



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

hat : Var → Heap → Var
hat x [] = name 0
hat x ((fst₁ , snd₁) ∷ x₂) = name (max (unname (hat x x₂)) (max (unname fst₁) (emax snd₁)))

infix 33 _extendedby_
infix 34 hat



data _⇓_ : {H₁ H₂ : Heap} → {E₁ E₂ : Exp} → H₁ entails E₁ → H₂ entails E₂ → Set where
  lam-red : {Γ : Heap} → {x : Var} → {e : Exp} → Γ ⊢ lambda x e ⇓ Γ ⊢ lambda x e

  app-red : {Γ Θ Δ : Heap} {x y : Var} {e e' z : Exp} →
    Γ ⊢ e ⇓ Δ ⊢ lambda y e'                →                 Δ ⊢ e' [| x / y |] ⇓ Θ ⊢ z →
-- ---------------------------------------------------------------------------------------------
                                  Γ ⊢ (e ∙ x) ⇓ (Θ ⊢ z)
  var-red : {Γ Δ : Heap} { x y : Var} {e z : Exp} →
    Γ ⊢ e ⇓ Δ ⊢ z →
    Γ extendedby ((x , e) ∷ []) ⊢ var x ⇓ Δ extendedby ( (x , z) ∷ []) ⊢ z -- (hat z (Δ extendedby ( (x , var z) ∷ [])))

  lEt-red : {Γ Δ : Heap} {e z : Exp} {TT : List (Var × Exp)} →
    Γ extendedby TT ⊢ e   ⇓ Δ ⊢ z →
    Γ ⊢ lEt TT iN e       ⇓ Δ ⊢ z


evalsteplet : {Γ : Heap} {e : Exp} {TT : List (Var × Exp)}  → Γ entails (lEt TT iN e) → Γ extendedby TT entails e
evalsteplet {.H} {e} {TT} (H ⊢ .(lEt TT iN e)) = H extendedby TT ⊢ e

postulate
  three+two : Exp
  five six : Exp
  U V X Y : Var
  U+one V+V : Exp
  P : ∀ {Γ Δ} → (Γ  ⊢ three+two) ⇓ (Δ ⊢ five)

ex1 : Exp
ex1 = lEt (U , three+two) ∷ (V , U+one) ∷ [] iN ((V+V))

badsub : Exp
badsub = lambda X (var Y)

uloop : UExp
uloop = (ulambda x ((uvar x) u∙ (uvar x))) u∙ ((ulambda x ((uvar x) u∙ (uvar x))))

ex2 : {x : Var} →  Exp
ex2 {x} = lEt (x , (lambda x ((var x) ∙ x))) ∷ [] iN (lambda x ((var x) ∙ x)) ∙ x

pex2 : {Γ : Heap} {e : Exp} {x y : Var} {TT : List (Var × Exp)} → [] ⊢ ex2 {x} ⇓ ( (x , (lambda x ((var x) ∙ x))) ∷ []) ⊢ ex2 {x}
pex2 {Γ} {e} {x} {y} {TT} with lEt-red {[]} {_} { (lambda x ((var x) ∙ x)) ∙ x} {_} {(x , (lambda x ((var x) ∙ x))) ∷ []}
... | t = {!!}


-- with app-red {_} {_} {_} {_} {_} {_} {_} {_}
-- ... | w = {!!}




-- with app-red  {Γ} {_} {Δ} {_} {_} {_} {_} {_}
-- ... | w = {!!} 
-- ex1sub1 : {Γ Δ : Heap} {x y : Var} {e  z : Exp } → ((( U , three+two ) ∷ []) ⊢ (var U)) ⇓ (((( U , five ))∷ []) ⊢ five)
-- ex1sub1 {Γ} {Δ} {x} {y} {e} {z} with var-red {[]} {[]} {U} {y} {three+two} {five}
-- ... | t = {!!}
-- -- ... | t with t P
-- -- ... | q = q

-- ex1sub2 : {Γ Δ : Heap} {x y : Var} {e  z : Exp } → ((( U , three+two ) ∷ ( V , U+one )∷ []) ⊢ (U+one)) ⇓ (((( U , five ))∷ []) ⊢ six)
-- ex1sub2 with app-red {!!} {!!}
-- ... | t = {!!}

