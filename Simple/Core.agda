module Simple.Core where

open import Prelude
open import Map
open import Lifts

infixl 2 _>>=_
infixr 1 _>>_
infixl 6 _<$>_ _<*>_

Effect : ∀ α ε -> Set (lsuc (α ⊔ ε))
Effect α ε = Set α -> Set ε

Effects : ∀ {n} -> (αεs : Level ²^ n) -> Set _
Effects = Map (uncurryᵏ Effect)

effˡ : ∀ {n} -> Level ²^ n -> Level -> Level
effˡ αεs β = max (map (lsuc ∘ proj₁) αεs)
           ⊔ max (map proj₂ αεs)
           ⊔ max (map proj₁ αεs)
           ⊔ β

data Eff {n β} {αεs : Level ²^ n} (Ψs : Effects αεs) (B : Set β) : Set (effˡ αεs β) where
  return : B -> Eff Ψs B
  call   : ∀ i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αεs λ A ->
               Lift∃ᵐ proj₂ i αεs {lookupᵐ i Ψs A} λ _ ->
                 Lift∀ᵐ proj₁ i αεs {A} λ _ ->
                   Eff Ψs B)
         -> Eff Ψs B

call′ : ∀ {n β} {αεs : Level ²^ n} {Ψs : Effects αεs} {B : Set β}
          i {A}
      -> lookupᵐ i Ψs A -> (A -> Eff Ψs B) -> Eff Ψs B
call′ i a f = call i (lift∃ᵐ i (, lift∃ᵐ i (a , lift∀ᵐ i f)))

runLifts : ∀ {n β} {αεs : Level ²^ n} {Ψs : Effects αεs} {B : Set β}
             i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αεs λ A ->
               Lift∃ᵐ proj₂ i αεs {lookupᵐ i Ψs A} λ _ ->
                 Lift∀ᵐ proj₁ i αεs {A} λ _ ->
                   Eff Ψs B)
         -> ∃ λ A -> lookupᵐ i Ψs A × (A -> Eff Ψs B)
runLifts i = second (second (lower∀ᵐ i) ∘ lower∃ᵐ i) ∘ lower∃ᵐ i

runᵉ : ∀ {β} {B : Set β} -> Eff tt B -> B
runᵉ (return y)  = y
runᵉ (call () p)

invoke# : ∀ {n} {αεs : Level ²^ n} {Ψs : Effects αεs}
            i {A}
        -> lookupᵐ i Ψs A -> Eff Ψs A
invoke# i a = call′ i a return

{-# TERMINATING #-}
_>>=_ : ∀ {n β γ} {αεs : Level ²^ n} {Ψs : Effects αεs} {B : Set β} {C : Set γ}
      -> Eff Ψs B -> (B -> Eff Ψs C) -> Eff Ψs C
return y >>= g = g y
call i p >>= g = let , a , f = runLifts i p in call′ i a λ x -> f x >>= g

_>>_ : ∀ {n β γ} {αεs : Level ²^ n} {Ψs : Effects αεs} {B : Set β} {C : Set γ}
     -> Eff Ψs B -> Eff Ψs C -> Eff Ψs C
b >> c = b >>= const c

_<$>_ : ∀ {n β γ} {αεs : Level ²^ n} {Ψs : Effects αεs} {B : Set β} {C : Set γ}
      -> (B -> C) -> Eff Ψs B -> Eff Ψs C
g <$> b = b >>= return ∘ g

_<*>_ : ∀ {n β γ} {αεs : Level ²^ n} {Ψs : Effects αεs} {B : Set β} {C : Set γ}
      -> Eff Ψs (B -> C) -> Eff Ψs B -> Eff Ψs C
d <*> b = d >>= _<$> b

{-# TERMINATING #-}
shiftᵉ : ∀ {n α ε β} {αεs : Level ²^ n} {Ψ : Effect α ε} {Ψs : Effects αεs} {B : Set β}
       -> Eff Ψs B -> Eff (Ψ , Ψs) B
shiftᵉ (return y) = return y
shiftᵉ (call i p) = let , a , f = runLifts i p in call′ (suc i) a (shiftᵉ ∘ f)
