{-# OPTIONS --type-in-type #-}

module Loop.Effect.State where

open import Loop

data AState A : Effectful where
  Get : AState A A (const A)
  Put : ∀ {B} -> B -> AState A ⊤ (const B)

State : Set -> Effect
State = the AState

get : ∀ {Ψs A} {{p : State A ∈ Ψs}} -> Eff Ψs A _
get = invoke Get

zap : ∀ {Ψs A B} {{p : State A ∈ Ψs}} -> B -> Eff Ψs ⊤ _
zap = invoke′ ∘ Put

put : ∀ {Ψs A} {{p : State A ∈ Ψs}} -> A -> Eff Ψs ⊤ _
put = invoke ∘ Put
