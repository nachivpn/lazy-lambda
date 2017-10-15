module Semantics where

open import Prelude
open import Term
open import Sugar

infix 10 _⇓_

data _⇓_ :  ∀ {m n} → Heap m ⊢ Closure → Heap n ⊢ Closure → Set where
  
  lam-red : ∀ {x t ρ} {n : Nat} {H : Heap n}
    → H ∶ lam x t ⟨ ρ ⟩ ⇓ H ∶ lam x t ⟨ ρ ⟩
    
  app-red : ∀ {t t₁ x u vc ρ ρ₁}
    {n n₁ n' : Nat} {H : Heap n} {H₁ : Heap n₁} {H' : Heap n'}
    → H ∶ t ⟨ ρ ⟩ ⇓ H₁ ∶ lam x t₁ ⟨ ρ₁ ⟩
    → ((n₁ , u ⟨ ρ ⟩) ∷ H₁) ∶ t₁ ⟨ ρ₁ ∣ x ↦ n₁ ∣ ⟩ ⇓ H' ∶ vc 
    → H ∶ (t ∙ u) ⟨ ρ ⟩ ⇓ H' ∶ vc

  var-red : ∀ { x ρ tc vc} {p : Pointer}
   {n n' : Nat} {H : Heap n} {H' : Heap n'}
   → x ↦ p ∈e ρ
   → p ↦ tc ∈h H
   → H ∶ tc ⇓ H' ∶ vc
   → H ∶ var x ⟨ ρ ⟩ ⇓ ((p , vc) ∷ H') ∶ vc
