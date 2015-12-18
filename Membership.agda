module Eff.Membership where

open import Eff.Prelude
open import Eff.Zip

infix 3 _∈_

_∈_ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
        {C : ∀ x y -> Set (k x y)} {xs : A ^ n} {ys : B ^ n} {x y}
    -> C x y -> Zip C xs ys -> Set
y ∈ ys = Unionʰ (homo (mapᶻ (y ≅_) ys))

∈→Fin : ∀ n {α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
          {C : ∀ x y -> Set (k x y)} {xs : A ^ n} {ys : B ^ n}
          {x y} {z : C x y} {zs : Zip C xs ys}
      -> z ∈ zs -> Fin n
∈→Fin  0      ()
∈→Fin (suc n) (inj₁ r) = zero
∈→Fin (suc n) (inj₂ p) = suc (∈→Fin n p)
