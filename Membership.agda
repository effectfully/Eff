module Eff.Membership where

open import Eff.Prelude
open import Eff.Map

infix 3 _∈_

_∈_ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n} {x}
    -> B x -> Map B xs -> Set
y ∈ ys = Union (homo (mapᵐ (y ≅_) ys))

∈→Fin : ∀ n {α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)}
          {xs : A ^ n} {ys : Map B xs} {x} {y : B x}
      -> y ∈ ys -> Fin n
∈→Fin  0      ()
∈→Fin (suc n) (inj₁ r) = zero
∈→Fin (suc n) (inj₂ p) = suc (∈→Fin n p)
