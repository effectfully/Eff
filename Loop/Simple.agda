{-# OPTIONS --type-in-type #-}

module Loop.Simple where

open import Prelude

infix  3 _∈_
infixl 2 _>>=_
infixr 1 _>>_
infixl 6 _<$>_

_∈_ : ∀ {A} -> A -> List A -> Set
y ∈ xs = lfoldr (λ x R -> y ≡ x ⊎ R) ⊥ xs

Effect : Set
Effect = Set -> Set

Effects : Set
Effects = List Effect

HigherEffect : Set
HigherEffect = Effects -> Effect

HigherEffects : Set
HigherEffects = List HigherEffect

-- Expanded (lfoldr (λ Ψ R -> Ψ A ⊎ R) ⊥ Ψs) to make the function constructor-headed.
Unionᵉ : HigherEffect
Unionᵉ  []      A = ⊥
Unionᵉ (Ψ ∷ Ψs) A = Ψ A ⊎ Unionᵉ Ψs A

_⊎ʰᵉ_ : HigherEffect -> HigherEffect -> HigherEffect
(Φ ⊎ʰᵉ Ξ) Ψs A = Φ Ψs A ⊎ Ξ Ψs A

Unionʰᵉ : HigherEffects -> HigherEffect
Unionʰᵉ = lfoldr _⊎ʰᵉ_ (λ _ _ -> ⊥)

--------------------

data Freer (Ψ : Effect) : Effect where
  return : ∀ {B} -> B -> Freer Ψ B
  call   : ∀ {A B} -> Ψ A -> (A -> Freer Ψ B) -> Freer Ψ B

liftᶠ : ∀ {Ψ A} -> Ψ A -> Freer Ψ A
liftᶠ a = call a return

_>>=_ : ∀ {Ψ B C} -> Freer Ψ B -> (B -> Freer Ψ C) -> Freer Ψ C
return y >>= g = g y
call a f >>= g = call a λ x -> f x >>= g

_>>_ : ∀ {Ψ B C} -> Freer Ψ B -> Freer Ψ C -> Freer Ψ C
b >> c = b >>= const c

_<$>_ : ∀ {Ψ B C} -> (B -> C) -> Freer Ψ B -> Freer Ψ C
g <$> b = b >>= return ∘ g

--------------------

record WUnionʰᵉ Φs Ψs A : Set where
  constructor wUnionʰᵉ
  field unwUnionʰᵉ : Unionʰᵉ Φs Ψs A

pattern wcall a f = call (wUnionʰᵉ a) f 

EffOver : HigherEffects -> HigherEffect
EffOver Φs Ψs = Freer (WUnionʰᵉ (Unionᵉ ∷ Φs) Ψs)

inj : ∀ {Ψs Ψ A} -> Ψ ∈ Ψs -> Ψ A -> Unionᵉ Ψs A
inj {[]}      ()         a
inj {Ψ ∷ Ψs} (inj₁ refl) a = inj₁ a
inj {Ψ ∷ Ψs} (inj₂ p)    a = inj₂ (inj p a)

invoke : ∀ {Φs Ψ Ψs A} {{p : Ψ ∈ Ψs}} -> Ψ A -> EffOver Φs Ψs A
invoke {{p}} = liftᶠ ∘ wUnionʰᵉ ∘ inj₁ ∘ inj p

invoke₀ : ∀ {Φs Ψ Ψs A} -> Ψ A -> EffOver Φs (Ψ ∷ Ψs) A
invoke₀ = invoke

Eff : HigherEffect
Eff = EffOver []
