module Semantics where

open import Prelude
open import Term
open import Sugar

infix 10 _⇓_

data _⇓_ :  ∀ {m n} → Heap m ⊢ Closure → Heap n ⊢ Closure → Set where

  -- a lambda term simply reduces to itself
  -- without changes to Heap or closure
  lam-red : ∀ {x t ρ} {n : Nat} {H : Heap n}
    → H ∶ lam x t ⟨ ρ ⟩ ⇓ H ∶ lam x t ⟨ ρ ⟩

  -- an application involves two reductions:
  app-red : ∀ {t t₁ x u vc ρ ρ₁}
    {n n₁ n' : Nat} {H : Heap n} {H₁ : Heap n₁} {H' : Heap n'}
    -- 1. Reducing the function
    → H ∶ t ⟨ ρ ⟩ ⇓ H₁ ∶ lam x t₁ ⟨ ρ₁ ⟩
    -- 2. Reducing the body of the function with a closure containing argument
    → (n₁ ↦ u ⟨ ρ ⟩ ∷ H₁) ∶ t₁ ⟨ ρ₁ ∣ x ↦ n₁ ∣ ⟩ ⇓ H' ∶ vc 
    → H ∶ (t ∙ u) ⟨ ρ ⟩ ⇓ H' ∶ vc

  -- a variable reduction involves 2 lookups and a reduction:
  var-red : ∀ { x ρ tc vc} {p : Pointer}
   {n n' : Nat} {H : Heap n} {H' : Heap n'}
   -- an environment lookup for a pointer of the variable
   → x ↦ p ∈e ρ
   -- a Heap lookup to find the (term?) closure pointed to by pointer
   → p ↦ tc ∈h H
   -- evaluate the (term?) closure to obtain value closure
   → H ∶ tc ⇓ H' ∶ vc
   -- updating the Heap with the value closure
   → H ∶ var x ⟨ ρ ⟩ ⇓ (p ↦ vc ∷ H') ∶ vc
