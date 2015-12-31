module Resources.Membership where

open import Prelude
open import Map
open import Resources.Core

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

    Subst : ∀ {α₁ α₂ β₁ β₂ γ₁ γ₂ δ₁ δ₂}
              {A₁ : Set α₁} {A₂ : Set α₂} {B : Set β₁} {C : B -> Set γ₁}
              {F₁ : Set α₁ -> (B : Set β₁) -> (B -> Set γ₁) -> Set δ₁}
              {F₂ : Set α₂ -> (B : Set β₂) -> (B -> Set γ₂) -> Set δ₂}
          -> F₁ ≅ F₂
          -> A₁ ≅ A₂
          -> F₁ A₁  B          C
          -> F₂ A₂ (Coerce B) (Coerce ∘ C ∘ uncoerce)
    Subst {α₁} {α₂} {β₁} {β₂} {γ₁} {γ₂} {δ₁} {δ₂} p q x
      rewrite trustMe α₁ α₂ | trustMe β₁ β₂ | trustMe γ₁ γ₂ | trustMe δ₁ δ₂
        = subst₂ (λ F A -> F A _ _) (≅→≡ p) (≅→≡ q) x

_∈_ : ∀ {n ρ α ε} {ρs : Level ^ n} {αεs : Level ²^ n}
    -> Effect ρ α ε × Resource ρ -> Effects ρs αεs × Resources ρs -> Set
_∈_ {0}     (Φ , S) ( tt      ,  tt)      = ⊥
_∈_ {suc n} (Φ , S) ((Ψ , Ψs) , (R , Rs)) = Φ ≅ Ψ × S ≅ R ⊎ Φ , S ∈ Ψs , Rs 

∈→Fin : ∀ {n ρ α ε} {ρs : Level ^ n} {αεs : Level ²^ n}
          {ΨR : Effect ρ α ε × Resource ρ} {ΨsRs : Effects ρs αεs × Resources ρs}
      -> ΨR ∈ ΨsRs -> Fin n
∈→Fin {0}     ()
∈→Fin {suc n} (inj₁ _) = zero
∈→Fin {suc n} (inj₂ p) = suc (∈→Fin p)

invoke′ : ∀ {n ρ α ε} {ρs : Level ^ n} {αεs : Level ²^ n}
            {Ψ : Effect ρ α ε} {R : Resource ρ} {A R′}
            {Ψs : Effects ρs αεs} {Rs : Resources ρs}
            {{p : Ψ , R ∈ Ψs , Rs}}
        -> Ψ R A R′ -> Eff Ψs A Rs (λ x -> replaceᵐ (∈→Fin p) (Coerce (R′ x)) Rs)
invoke′ {0}     {{()}}           a
invoke′ {suc n} {{inj₁ (q , r)}} a =
  call′ zero (Subst q r a) (return ∘ uncoerce)
invoke′ {suc n} {{inj₂  p}}      a = shiftᵉ (invoke′ {{p}} a)

invoke : ∀ {n ρ α ε} {ρs : Level ^ n} {αεs : Level ²^ n}
           {Ψ : Effect ρ α ε} {R : Resource ρ} {A}
           {Ψs : Effects ρs αεs} {Rs : Resources ρs}
           {{p : Ψ , R ∈ Ψs , Rs}}
       -> Ψ R A (const R) -> Eff Ψs A Rs (const Rs)
invoke {0}     {{()}}           a
invoke {suc n} {{inj₁ (q , r)}} a rewrite sym (Coerce-≅→≡ r) =
  call′ zero (Subst q r a) (return ∘ uncoerce)
invoke {suc n} {{inj₂  p}}      a = shiftᵉ (invoke {{p}} a)
