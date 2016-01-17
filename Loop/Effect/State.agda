{-# OPTIONS --type-in-type #-}

module Loop.Effect.State where

open import Loop

data State A : Effectful where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

-- State : Effect
-- State = the AState

-- get : ∀ {A : Set} {A Rs Ψs} {rs : Resources Rs} {{p : State , A ∈ Ψs , rs}} -> Eff Ψs rs A _
-- get {{p}} = invoke Get

-- get : ∀ {Ψ r A Ψs rs} {{p : Ψ # r ∈ rs}} -> Eff Ψs rs A _
-- get = invoke Get

-- zap : ∀ {Ψs A B} {{p : State A ∈ Ψs}} -> B -> Eff Ψs ⊤ _
-- zap = invoke′ ∘ Put

-- put : ∀ {Ψs A} {{p : State A ∈ Ψs}} -> A -> Eff Ψs ⊤ _
-- put = invoke ∘ Put
