module Proofs where

open import Prelude
open import Term
open import Semantics
open import Sugar

-- id applied to itself, evaluates to itself
-- for any Heap and with any closure
id∙id⇓id : {n : Nat} {ρ : Env} {H : Heap n}
  → H ∶ (idF ∙ idF) ⟨ ρ ⟩ ⇓ _ ∶ idF ⟨ _ ⟩
id∙id⇓id {n} {ρ} {H} =
  app-red
    lam-red
      (var-red
        zero
        zero
        lam-red)

