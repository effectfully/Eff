module Core where

open import Prelude
open import Map
open import Lifts

infixl 2 _>>=_
infixr 1 _>>_

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

-- Simple : ∀ {ρ α ε} -> Effect ρ α ε -> Set ρ -> Set α -> Set ρ -> Set ε
-- Simple Ψ R₁ A R₂ = Ψ R₁ A (const R₂)

r′ˡ : Level × Level -> Level -> Level
r′ˡ (α , ε) ρ = α ⊔ lsuc ρ

effˡ : ∀ {n} -> Level ^ n -> Level ²^ n -> Level -> Level
effˡ ρs αεs β = max (map (lsuc ∘ proj₁) αεs)
              ⊔ max (zipWith r′ˡ αεs ρs)
              ⊔ max (map proj₂ αεs)
              ⊔ max (map proj₁ αεs)
              ⊔ β

-- data Eff {n β} {ρs : Level ^ n} {αεs : Level ²^ n} (Ψs : Effects ρs αεs) (B : Set β)
--          : Resources ρs -> (B -> Resources ρs) -> Set (effˡ ρs αεs β) where
--   return : ∀ {Rs′} y -> Eff Ψs B (Rs′ y) Rs′
--   call   : ∀ {Rs Rs′} i {A R′}
--          -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′
--          -> (∀ x -> Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
--          -> Eff Ψs B Rs Rs′

data Eff {n β} {ρs : Level ^ n} {αεs : Level ²^ n} (Ψs : Effects ρs αεs) (B : Set β)
         : Resources ρs -> (B -> Resources ρs) -> Set (effˡ ρs αεs β) where
  return : ∀ {Rs′} y -> Eff Ψs B (Rs′ y) Rs′
  call   : ∀ {Rs Rs′} i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αεs λ A ->
               Lift∃ᶻ r′ˡ i αεs ρs λ R′ ->
                 Lift∃ᵐ proj₂ i αεs {lookupᶻ i Ψs (lookupᵐ i Rs) A R′} λ _ ->
                   Lift∀ᵐ  proj₁ i αεs λ x ->
                     Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
         -> Eff Ψs B Rs Rs′

call′ : ∀ {n β} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs} {B : Set β} {Rs Rs′}
          i {A R′}
      -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′
      -> (∀ x -> Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
      -> Eff Ψs B Rs Rs′
call′ i a f = call i (lift∃ᵐ i (, lift∃ᶻ i (, lift∃ᵐ i (a , lift∀ᵐ i f))))

runLifts : ∀ {n β} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs} {B : Set β} {Rs Rs′}
             i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αεs λ A ->
               Lift∃ᶻ r′ˡ i αεs ρs λ R′ ->
                 Lift∃ᵐ proj₂ i αεs {lookupᶻ i Ψs (lookupᵐ i Rs) A R′} λ _ ->
                   Lift∀ᵐ  proj₁ i αεs λ x ->
                     Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
         -> ∃₂ λ A R′ ->
                lookupᶻ i Ψs (lookupᵐ i Rs) A R′
              × ∀ x -> Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′
runLifts i = second (second (second (lower∀ᵐ i) ∘ lower∃ᵐ i) ∘ lower∃ᶻ i) ∘ lower∃ᵐ i

runᵉ : ∀ {β} {B : Set β} -> Eff tt B tt _ -> B
runᵉ (return y)  = y
runᵉ (call () p)

invoke# : ∀ {n} {ρs : Level ^ n} {αεs : Level ²^ n}
            {Ψs : Effects ρs αεs} {Rs : Resources ρs}
            (i : Fin n) {A R′}
        -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′
        -> Eff Ψs A Rs (λ x -> replaceᵐ i (R′ x) Rs)
invoke# i a = call′ i a return

{-# TERMINATING #-}
_>>=_ : ∀ {n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs} {B : Set β}
          {Rs : Resources ρs} {C : Set γ} {Rs′ : B -> Resources ρs} {Rs′′ : C -> Resources ρs}
      -> Eff Ψs B Rs Rs′ -> (∀ y -> Eff Ψs C (Rs′ y) Rs′′) -> Eff Ψs C Rs Rs′′
return y >>= g = g y
call i p >>= g = let , , a , f = runLifts i p in call′ i a λ x -> f x >>= g

_>>_ : ∀ {n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs} {B : Set β}
         {Rs₁ Rs₂ : Resources ρs} {C : Set γ} {Rs′′ : C -> Resources ρs}
     -> Eff Ψs B Rs₁ (const Rs₂) -> Eff Ψs C Rs₂ Rs′′ -> Eff Ψs C Rs₁ Rs′′
b >> c = b >>= const c

{-# TERMINATING #-}
shiftᵉ : ∀ {n α ρ ε β} {ρs : Level ^ n} {αεs : Level ²^ n}
           {Ψ : Effect ρ α ε} {R : Resource ρ} {Ψs : Effects ρs αεs}
           {B : Set β} {Rs : Resources ρs} {Rs′ : B -> Resources ρs}
       -> Eff Ψs B Rs Rs′ -> Eff (Ψ , Ψs) B (R , Rs) (λ x -> R , Rs′ x) 
shiftᵉ (return y) = return y
shiftᵉ (call i p) = let , , a , f = runLifts i p in call′ (suc i) a (shiftᵉ ∘ f)
