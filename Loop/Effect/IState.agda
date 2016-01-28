{-# OPTIONS --type-in-type #-}

module Loop.Effect.IState where

open import Prelude
open import Loop.Indexed

data State A : Effectful where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

get : ∀ {Is is Rs rs A} {Φs : IHigherEffects Is}
        {Ψs : Effects Rs} {{p : State , A ∈² Ψs , rs}}
    -> EffOver Φs is Ψs rs A _
get = invoke Get

zap : ∀ {Is is Rs rs B} {Φs : IHigherEffects Is} {Ψs : Effects Rs}
        A {{p : State , A ∈² Ψs , rs}}
    -> B -> EffOver Φs is Ψs rs ⊤ _
zap _ = invoke′ ∘ Put

put : ∀ {Is is Rs rs A} {Φs : IHigherEffects Is}
        {Ψs : Effects Rs} {{p : State , A ∈² Ψs , rs}}
    -> A -> EffOver Φs is Ψs rs ⊤ _
put = invoke ∘ Put
