module Simple.Core where

open import Prelude
open import Map
open import Lifts

infixl 2 _>>=_
infixr 1 _>>_
infixl 6 _<$>_ _<*>_

Effect : ∀ α ψ -> Set (lsuc (α ⊔ ψ))
Effect α ψ = Set α -> Set ψ

Effects : ∀ {n} -> (αψs : Level ²^ n) -> Set _
Effects = Map (uncurryᵏ Effect)

effˡ : ∀ {n} -> Level ²^ n -> Level -> Level
effˡ αψs β = max (map (lsuc ∘ proj₁) αψs)
           ⊔ max (map proj₂ αψs)
           ⊔ max (map proj₁ αψs)
           ⊔ β

data Eff {n β} {αψs : Level ²^ n} (Ψs : Effects αψs) (B : Set β) : Set (effˡ αψs β) where
  return : B -> Eff Ψs B
  call   : ∀ i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αψs λ A ->
               Lift∃ᵐ proj₂ i αψs {lookupᵐ i Ψs A} λ _ ->
                 Lift∀ᵐ proj₁ i αψs {A} λ _ ->
                   Eff Ψs B)
         -> Eff Ψs B

call′ : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β}
          i {A}
      -> lookupᵐ i Ψs A -> (A -> Eff Ψs B) -> Eff Ψs B
call′ i a f = call i (lift∃ᵐ i (, lift∃ᵐ i (a , lift∀ᵐ i f)))

runLifts : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β}
             i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αψs λ A ->
               Lift∃ᵐ proj₂ i αψs {lookupᵐ i Ψs A} λ _ ->
                 Lift∀ᵐ proj₁ i αψs {A} λ _ ->
                   Eff Ψs B)
         -> ∃ λ A -> lookupᵐ i Ψs A × (A -> Eff Ψs B)
runLifts i = second (second (lower∀ᵐ i) ∘ lower∃ᵐ i) ∘ lower∃ᵐ i

runᵉ : ∀ {β} {B : Set β} -> Eff tt B -> B
runᵉ (return y)  = y
runᵉ (call () p)

invoke# : ∀ {n} {αψs : Level ²^ n} {Ψs : Effects αψs}
        -> ∀ i {A} -> lookupᵐ i Ψs A -> Eff Ψs A
invoke# i a = call′ i a return

{-# TERMINATING #-}
_>>=_ : ∀ {n β γ} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {C : Set γ}
      -> Eff Ψs B -> (B -> Eff Ψs C) -> Eff Ψs C
return y >>= g = g y
call i p >>= g = let , a , f = runLifts i p in call′ i a λ x -> f x >>= g

_>>_ : ∀ {n β γ} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {C : Set γ}
     -> Eff Ψs B -> Eff Ψs C -> Eff Ψs C
b >> c = b >>= const c

_<$>_ : ∀ {n β γ} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {C : Set γ}
      -> (B -> C) -> Eff Ψs B -> Eff Ψs C
g <$> b = b >>= return ∘ g

_<*>_ : ∀ {n β γ} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {C : Set γ}
      -> Eff Ψs (B -> C) -> Eff Ψs B -> Eff Ψs C
d <*> b = d >>= _<$> b

{-# TERMINATING #-}
shiftᵉ : ∀ {n α ψ β} {αψs : Level ²^ n} {Ψ : Effect α ψ} {Ψs : Effects αψs} {B : Set β}
       -> Eff Ψs B -> Eff (Ψ , Ψs) B
shiftᵉ (return y) = return y
shiftᵉ (call i p) = let , a , f = runLifts i p in call′ (suc i) a (shiftᵉ ∘ f)

{-# TERMINATING #-}
execEff : ∀ {n α ψ β γ} {αψs : Level ²^ n} {Ψ : Effect α ψ}
            {Ψs : Effects αψs} {B : Set β} {C : Set γ}
        -> (B -> Eff Ψs C)
        -> (∀ {A} -> Ψ A -> (A -> Eff Ψs C) -> Eff Ψs C)
        -> Eff (Ψ , Ψs) B
        -> Eff  Ψs      C
execEff ret k (return y) = ret y
execEff ret k (call i p) with runLifts i p
... | , a , f with i
... | zero   = k a (execEff ret k ∘ f)
... | suc i' = call′ i' a (execEff ret k ∘ f)
