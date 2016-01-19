{-# OPTIONS --type-in-type #-}

module Loop.Effect.State where

open import Loop

data State A : Effectful where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

get : ∀ {Φs Rs rs A} {Ψs : Effects Rs} {{p : State , A ∈ Ψs , rs}} -> EffOver Φs Ψs rs A _
get = invoke Get

zap : ∀ {Φs Rs rs B} {Ψs : Effects Rs} A {{p : State , A ∈ Ψs , rs}} -> B -> EffOver Φs Ψs rs ⊤ _
zap _ = invoke′ ∘ Put

put : ∀ {Φs Rs rs A} {Ψs : Effects Rs} {{p : State , A ∈ Ψs , rs}} -> A -> EffOver Φs Ψs rs ⊤ _
put = invoke ∘ Put
