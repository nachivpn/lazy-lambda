module Proofs where

open import Prelude
open import Term
open import Semantics
open import Sugar

-- id applied to itself, evaluates to itself
-- for any Heap and with any environment
id∙id⇓id : {n : Nat} {ρ : Env} {H : Heap n}
  → H ∶ (idF ∙ idF) ⟨ ρ ⟩ ⇓ _ ∶ idF ⟨ ρ ⟩
id∙id⇓id =
  app-red             -- reduce the application
    lam-red           -- reduce left id to λx.x
      (var-red        -- evaluate body i.e, x
        zero          -- lookup on ρ for x ↦ p 
        zero          -- lookup on H for p ↦ λx.x
        lam-red)      -- reduce right id to λx.x 

δ : Term
δ = lam x ( var x ∙ var x)

postulate
  n¬≡n+4 : ∀ {n} → n ¬≡ suc (suc (suc (suc n)))

δ∙|id∙id|⇓id : {n : Nat} {ρ : Env} {H : Heap n}
  → H ∶ (δ ∙ (idF ∙ idF )) ⟨ ρ ⟩ ⇓ _ ∶ idF ⟨ ρ ⟩ 
δ∙|id∙id|⇓id =
  app-red
    lam-red
    (app-red
      -- evaluating 1st x of δ
      (var-red
        zero
        zero
        id∙id⇓id)   -- Proofs compose neatly!
      -- evaluating body of value of x
      (var-red
        zero
        zero
         -- evaluating 2nd x of δ
         -- we don't recompute id∙id⇓id!
         -- instead, we simply take it from the Heap!
        (var-red
          zero
          (suc {pr = n¬≡n+4} zero)
          lam-red)))
