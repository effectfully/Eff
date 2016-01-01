module Simple.Membership where

open import Prelude
open import Map
open import Simple.Core

infix 3 _∈_

private
  module _ where
    open TrustMe

    Coerce : ∀ {β α} -> Set α -> Set β
    Coerce {β} {α} rewrite trustMe α β = id

    uncoerce : ∀ {β α} {A : Set α} -> Coerce {β} A -> A
    uncoerce {β} {α} rewrite trustMe α β = id

    Coerce-≅→≡ : ∀ {α β} {A : Set α} {B : Set β} -> A ≅ B -> Coerce A ≡ B
    Coerce-≅→≡ {α} {β} rewrite trustMe α β = ≅→≡

    Subst : ∀ {α₁ α₂ β₁ β₂} {A : Set α₁} {F₁ : Set α₁ -> Set β₁} {F₂ : Set α₂ -> Set β₂}
          -> F₁ ≅ F₂ -> F₁ A -> F₂ (Coerce A)
    Subst {α₁} {α₂} {β₁} {β₂} p rewrite trustMe α₁ α₂ | trustMe β₁ β₂ = subst (_$ _) (≅→≡ p)

_∈_ : ∀ {n α ψ} {αψs : Level ²^ n} -> Effect α ψ -> Effects αψs -> Set
_∈_ {0}     Φ  tt      = ⊥
_∈_ {suc n} Φ (Ψ , Ψs) = Φ ≅ Ψ ⊎ Φ ∈ Ψs

∈→Fin : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {Ψs : Effects αψs} -> Ψ ∈ Ψs -> Fin n
∈→Fin {0}     ()
∈→Fin {suc n} (inj₁ _) = zero
∈→Fin {suc n} (inj₂ p) = suc (∈→Fin p)

invoke : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {A} {Ψs : Effects αψs} {{p : Ψ ∈ Ψs}}
       -> Ψ A -> Eff Ψs A
invoke {0}     {{()}}     a
invoke {suc n} {{inj₁ q}} a = call′ zero (Subst q a) (return ∘ uncoerce)
invoke {suc n} {{inj₂ p}} a = shiftᵉ (invoke a)
