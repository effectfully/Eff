module Resources.Core where

open import Prelude
open import Map
open import Lifts

infixl 2 _>>=_
infixr 1 _>>_
infixl 6 _<$>_ _<*>_

Effectful : ∀ α ρ ψ -> Set (lsuc (α ⊔ ρ ⊔ ψ))
Effectful α ρ ψ = (A : Set α) -> (A -> Set ρ) -> Set ψ

Effect : ∀ ρ α ψ -> Set (lsuc (ρ ⊔ α ⊔ ψ))
Effect ρ α ψ = Set ρ -> Effectful α ρ ψ

Effects : ∀ {n} -> (ρs : Level ^ n) -> (αψs : Level ²^ n) -> Set _
Effects = Zip (λ ρ -> uncurryᵏ (Effect ρ))

Resource : ∀ ρ -> Set (lsuc ρ)
Resource ρ = Set ρ

Resources : ∀ {n} -> (ρs : Level ^ n) -> Set _
Resources = Map Resource

-- effˡ : ∀ {n} -> Level ^ n -> Level ²^ n -> Level -> Level
-- effˡ ρs αψs β = lsuc (max ρs)
--               ⊔ lsuc (max (map proj₁ αψs))
--               ⊔ max (map proj₂ αψs)
--               ⊔ β

-- data Eff {n β} {ρs : Level ^ n} {αψs : Level ²^ n} (Ψs : Effects ρs αψs) (B : Set β)
--          : Resources ρs -> (B -> Resources ρs) -> Set (effˡ ρs αψs β) where
--   return : ∀ {Rs′} y -> Eff Ψs B (Rs′ y) Rs′
--   call   : ∀ {Rs Rs′} i {A R′}
--          -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′
--          -> (∀ x -> Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
--          -> Eff Ψs B Rs Rs′

r′ˡ : Level × Level -> Level -> Level
r′ˡ (α , ψ) ρ = α ⊔ lsuc ρ

effˡ : ∀ {n} -> Level ^ n -> Level ²^ n -> Level -> Level
effˡ ρs αψs β = max (map (lsuc ∘ proj₁) αψs)
              ⊔ max (zipWith r′ˡ αψs ρs)
              ⊔ max (map proj₂ αψs)
              ⊔ max (map proj₁ αψs)
              ⊔ β

data Eff {n β} {ρs : Level ^ n} {αψs : Level ²^ n} (Ψs : Effects ρs αψs) (B : Set β)
         : Resources ρs -> (B -> Resources ρs) -> Set (effˡ ρs αψs β) where
  return : ∀ {Rs′} y -> Eff Ψs B (Rs′ y) Rs′
  call   : ∀ {Rs Rs′} i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αψs λ A ->
               Lift∃ᶻ r′ˡ i αψs ρs λ R′ ->
                 Lift∃ᵐ proj₂ i αψs {lookupᶻ i Ψs (lookupᵐ i Rs) A R′} λ _ ->
                   Lift∀ᵐ proj₁ i αψs λ x ->
                     Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
         -> Eff Ψs B Rs Rs′

call′ : ∀ {n β} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs} {B : Set β} {Rs Rs′}
          i {A R′}
      -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′
      -> (∀ x -> Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
      -> Eff Ψs B Rs Rs′
call′ i a f = call i (lift∃ᵐ i (, lift∃ᶻ i (, lift∃ᵐ i (a , lift∀ᵐ i f))))

runLifts : ∀ {n β} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs} {B : Set β} {Rs Rs′}
             i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αψs λ A ->
               Lift∃ᶻ r′ˡ i αψs ρs λ R′ ->
                 Lift∃ᵐ proj₂ i αψs {lookupᶻ i Ψs (lookupᵐ i Rs) A R′} λ _ ->
                   Lift∀ᵐ proj₁ i αψs λ x ->
                     Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
         -> ∃₂ λ A R′ ->   lookupᶻ i Ψs (lookupᵐ i Rs) A R′
                         × ∀ x -> Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′
runLifts i = second (second (second (lower∀ᵐ i) ∘ lower∃ᵐ i) ∘ lower∃ᶻ i) ∘ lower∃ᵐ i

runᵉ : ∀ {β} {B : Set β} -> Eff tt B tt _ -> B
runᵉ (return y)  = y
runᵉ (call () p)

invoke# : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n}
            {Ψs : Effects ρs αψs} {Rs : Resources ρs}
            i {A R′}
        -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′ -> Eff Ψs A Rs (λ x -> replaceᵐ i (R′ x) Rs)
invoke# i a = call′ i a return

{-# TERMINATING #-}
_>>=_ : ∀ {n β γ} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs} {B : Set β}
          {C : Set γ} {Rs : Resources ρs} {Rs′ : B -> Resources ρs} {Rs′′ : C -> Resources ρs}
      -> Eff Ψs B Rs Rs′ -> (∀ y -> Eff Ψs C (Rs′ y) Rs′′) -> Eff Ψs C Rs Rs′′
return y >>= g = g y
call i p >>= g = let , , a , f = runLifts i p in call′ i a λ x -> f x >>= g

_>>_ : ∀ {n β γ} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs}
         {B : Set β} {C : Set γ} {Rs₁ Rs₂ : Resources ρs} {Rs′′ : C -> Resources ρs}
     -> Eff Ψs B Rs₁ (const Rs₂) -> Eff Ψs C Rs₂ Rs′′ -> Eff Ψs C Rs₁ Rs′′
b >> c = b >>= const c

_<$>_ : ∀ {n β γ} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs}
          {B : Set β} {C : Set γ} {Rs₁ Rs₂ : Resources ρs}
      -> (B -> C) -> Eff Ψs B Rs₁ (const Rs₂) -> Eff Ψs C Rs₁ (const Rs₂)
g <$> b = b >>= return ∘ g

_<*>_ : ∀ {n β γ} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs}
          {B : Set β} {C : Set γ} {Rs₁ Rs₂ Rs₃ : Resources ρs}
      -> Eff Ψs (B -> C) Rs₁ (const Rs₂) -> Eff Ψs B Rs₂ (const Rs₃) -> Eff Ψs C Rs₁ (const Rs₃)
d <*> b = d >>= _<$> b

{-# TERMINATING #-}
shiftᵉ : ∀ {n α ρ ψ β} {ρs : Level ^ n} {αψs : Level ²^ n}
           {Ψ : Effect ρ α ψ} {R : Resource ρ} {Ψs : Effects ρs αψs}
           {B : Set β} {Rs : Resources ρs} {Rs′ : B -> Resources ρs}
       -> Eff Ψs B Rs Rs′ -> Eff (Ψ , Ψs) B (R , Rs) (λ x -> R , Rs′ x) 
shiftᵉ (return y) = return y
shiftᵉ (call i p) = let , , a , f = runLifts i p in call′ (suc i) a (shiftᵉ ∘ f)

-- Too weak.
{-# TERMINATING #-}
execEff : ∀ {n ρ α ψ β γ} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψ : Effect ρ α ψ}
            {Ψs : Effects ρs αψs} {B : Set β} {C : B -> Set γ}
            {Rs : Resources (ρ , ρs)} {Rs′ : B -> Resources (ρ , ρs)}
        -> (∀ y -> C y)
        -> (∀ {R A R′ Rs Rs′} -> Ψ R A R′ -> (A -> Eff Ψs (Σ B C) Rs Rs′) -> Eff Ψs (Σ B C) Rs Rs′)
        -> Eff (Ψ , Ψs)  B       Rs         Rs′
        -> Eff  Ψs      (Σ B C) (tailᵐ Rs) (tailᵐ ∘ Rs′ ∘ proj₁)
execEff h k (return y) = return (y , h y)
execEff h k (call i p) with runLifts i p
... | , , a , f with i
... | zero   = k a (execEff h k ∘ f)
... | suc i' = call′ i' a (execEff h k ∘ f)
