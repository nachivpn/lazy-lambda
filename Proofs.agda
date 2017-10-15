module Proofs where

open import Prelude
open import Term
open import Semantics
open import Sugar

-- id applied to itself, evaluates to itself
-- for any Heap and with any closure
id∙id⇓id : {n : Nat} {ρ : Env} {H : Heap n}
  → H ∶ (idF ∙ idF) ⟨ ρ ⟩ ⇓ _ ∶ idF ⟨ ρ ⟩
id∙id⇓id {n} {ρ} {H} =
  app-red
    lam-red
      (var-red
        zero
        zero
        lam-red)

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
        (app-red
          lam-red
          (var-red
            zero
            zero
            lam-red)))
      -- evaluating body of value of x
      (var-red
        zero
        zero
         -- evaluating 2nd x of δ
        (var-red
          zero
          (suc {pr = n¬≡n+4} zero)
          lam-red)))    

