module Fun where

open import Prelude
open import Map

infixl 1 _>>=_
infixr 2 _>>_

Effectful : ∀ α ρ ε -> Set (lsuc (α ⊔ ρ ⊔ ε))
Effectful α ρ ε = (A : Set α) -> (A -> Set ρ) -> Set ε

Effect : ∀ ρ α ε -> Set (lsuc (ρ ⊔ α ⊔ ε))
Effect ρ α ε = Set ρ -> Effectful α ρ ε

Effects : ∀ {n} -> (ρs : Level ^ n) -> (αεs : Level ²^ n) -> Set _
Effects = Zip (λ ρ -> uncurryᵏ (Effect ρ))

Resource : ∀ ρ -> Set (lsuc ρ)
Resource ρ = Set ρ

Resources : ∀ {n} -> (ρs : Level ^ n) -> Set _
Resources = Map Resource

effˡ : ∀ {m n} -> Level ^ n -> Level ²^ n -> Level -> Fin n ^ m -> Level
effˡ {0}     ρs αεs β  tt      = β ⊔ max (map lsuc ρs)
effˡ {suc m} ρs αεs β (i , is) =
  lsuc (proj₁ (lookup i αεs)) ⊔ lsuc (lookup i ρs) ⊔ proj₂ (lookup i αεs) ⊔ effˡ ρs αεs β is

Eff⁻ : ∀ {m n β} {ρs : Level ^ n} {αεs : Level ²^ n}
     -> Effects ρs αεs
     -> Resources ρs
     -> (B : Set β)
     -> (B -> Resources ρs)
     -> (is : Fin n ^ m)
     -> Set (effˡ ρs αεs β is)
Eff⁻ {0}     Ψs Rs B Rs′  tt      = ∃ λ y -> Rs ≡ Rs′ y
Eff⁻ {suc m} Ψs Rs B Rs′ (i , is) =
  ∃ λ A -> ∃ λ R′ ->   lookupᶻ i Ψs (lookupᵐ i Rs) A R′
                     × ∀ x -> Eff⁻ Ψs (replaceᵐ i (R′ x) Rs) B Rs′ is

record Eff {m n β} {ρs : Level ^ n} {αεs : Level ²^ n}
           (Ψs : Effects ρs αεs) (Rs : Resources ρs)
           (B : Set β) (Rs′ : B -> Resources ρs)
           (is : Fin n ^ m) : Set (effˡ ρs αεs β is) where
  constructor wrap
  field unwrap : Eff⁻ Ψs Rs B Rs′ is
open Eff public

return : ∀ {n β} {ρs : Level ^ n} {αεs : Level ²^ n}
           {Ψs : Effects ρs αεs} {B : Set β} {Rs′ : B -> Resources ρs}
       -> ∀ y -> Eff Ψs (Rs′ y) B Rs′ tt
return y = wrap (y , refl)

runEff : ∀ {β} {B : Set β} -> Eff tt tt B (const tt) tt -> B
runEff = proj₁ ∘ unwrap

invoke# : ∀ {n} {ρs : Level ^ n} {αεs : Level ²^ n}
            {Ψs : Effects ρs αεs} {Rs : Resources ρs}
            (i : Fin n) {A R′}
        -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′
        -> Eff Ψs Rs A (λ x -> replaceᵐ i (R′ x) Rs) (i , tt)
invoke# i a = wrap (, , a , (_, refl))

bind : ∀ {m p n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
         {Rs : Resources ρs} {B : Set β} {Rs′ : B -> Resources ρs}
         {C : Set γ} {Rs′′ : C -> Resources ρs} {js : Fin n ^ p}
     -> (is : Fin n ^ m)
     -> Eff⁻ Ψs Rs B Rs′ is
     -> (∀ y -> Eff⁻ Ψs (Rs′ y) C Rs′′ js)
     -> Eff⁻ Ψs Rs C Rs′′ (is ++ js)
bind {0}      tt      (y , refl) g = g y
bind {suc m} (i , is)  b         g = fourth (λ f x -> bind is (f x) g) b

_>>=_ : ∀ {m p n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
          {Rs : Resources ρs} {B : Set β} {Rs′ : B -> Resources ρs}
          {C : Set γ} {Rs′′ : C -> Resources ρs} {is : Fin n ^ m} {js : Fin n ^ p}
      -> Eff Ψs Rs B Rs′ is -> (∀ y -> Eff Ψs (Rs′ y) C Rs′′ js) -> Eff Ψs Rs C Rs′′ (is ++ js)
_>>=_ {is = is} b g = wrap (bind is (unwrap b) (unwrap ∘ g))

_>>_ : ∀ {m p n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
         {Rs₁ Rs₂ : Resources ρs} {B : Set β} {C : Set γ}
         {Rs′′ : C -> Resources ρs} {is : Fin n ^ m} {js : Fin n ^ p}
     -> Eff Ψs Rs₁ B (const Rs₂) is -> Eff Ψs Rs₂ C Rs′′ js -> Eff Ψs Rs₁ C Rs′′ (is ++ js)
b >> c = b >>= const c

non-zeros : ∀ {m n} -> Fin (suc n) ^ m -> ℕ
non-zeros {0}      tt          = 0
non-zeros {suc m} (zero  , is) = non-zeros is
non-zeros {suc m} (suc i , is) = suc (non-zeros is)

shift : ∀ {m n} -> (is : Fin (suc n) ^ m) -> Fin n ^ non-zeros is
shift {0}      tt          = tt
shift {suc m} (zero  , is) = shift is
shift {suc m} (suc i , is) = i , shift is
