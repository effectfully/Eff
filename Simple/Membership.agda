module Simple.Membership where

open import Prelude
open import Map
open import Simple.Core

infix 3 _∈_

open TrustMe

private
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

-- ((Set α₁ -> Set β₁) ≅ (Set α₂ -> Set β₂)) doesn't imply (α₁ ≡ α₂).
-- ∈→ˡ≡ : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {Ψs : Effects αψs}
--      -> (p : Ψ ∈ Ψs) -> α ≡ proj₁ (lookup (∈→Fin p) αψs)
-- ∈→ˡ≡ {0}     ()
-- ∈→ˡ≡ {suc n} (inj₁ q) = {!!}
-- ∈→ˡ≡ {suc n} (inj₂ p) = ∈→ˡ≡ p

fold-lookupᵐ : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {Ψs : Effects αψs}
             -> ∀ (p : Ψ ∈ Ψs) {A} -> lookupᵐ (∈→Fin p) Ψs A -> Ψ (Coerce A)
fold-lookupᵐ {0}     ()       a
fold-lookupᵐ {suc n} (inj₁ q) a = Subst (hsym q) a
fold-lookupᵐ {suc n} (inj₂ p) a = fold-lookupᵐ p a

unfold-lookupᵐ : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {Ψs : Effects αψs}
               -> ∀ (p : Ψ ∈ Ψs) {A} -> Ψ A -> lookupᵐ (∈→Fin p) Ψs (Coerce A)
unfold-lookupᵐ {0}     ()       a
unfold-lookupᵐ {suc n} (inj₁ q) a = Subst q a
unfold-lookupᵐ {suc n} (inj₂ p) a = unfold-lookupᵐ p a

proj : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {Ψs : Effects αψs}
     -> ∀ i (p : Ψ ∈ Ψs) {A} -> lookupᵐ i Ψs A -> Maybe (Ψ (Coerce A))
proj i p a with i ≟ ∈→Fin p
... | yes r rewrite r = just (fold-lookupᵐ p a)
... | no  _ = nothing

invoke : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {A} {Ψs : Effects αψs} {{p : Ψ ∈ Ψs}}
       -> Ψ A -> Eff Ψs A
invoke {{p}} a = uncoerce <$> call′ (∈→Fin p) (unfold-lookupᵐ p a) return

-- Alternatively.
-- invoke : ∀ {n α ψ} {αψs : Level ²^ n} {Ψ : Effect α ψ} {A} {Ψs : Effects αψs} {{p : Ψ ∈ Ψs}}
--        -> Ψ A -> Eff Ψs A
-- invoke {0}     {{()}}     a
-- invoke {suc n} {{inj₁ q}} a = call′ zero (Subst q a) (return ∘ uncoerce)
-- invoke {suc n} {{inj₂ p}} a = shiftᵉ (invoke a)
