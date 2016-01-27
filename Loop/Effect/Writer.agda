{-# OPTIONS --type-in-type #-}

module Loop.Effect.Writer where

open import Loop

data Writer A : Effectful where
  Tell : A -> Writer A ⊤ (const A)

tell : ∀ {Φs Rs rs A} {Ψs : Effects Rs} {{p : Writer , A ∈² Ψs , rs}} -> A -> EffOver Φs Ψs rs ⊤ _
tell = invoke ∘ Tell
