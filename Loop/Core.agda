{-# OPTIONS --type-in-type #-}

module Loop.Core where

open import Prelude

infixl 2 _>>=_
infixr 1 _>>_

data List₁ {A} (B : A -> Set) : List A -> Set where
  []₁  : List₁ B []
  _∷₁_ : ∀ {x xs} -> B x -> List₁ B xs -> List₁ B (x ∷ xs)

lmap₁ : ∀ {A} {B : A -> Set} -> (∀ x -> B x) -> (xs : List A) -> List₁ B xs
lmap₁ f  []      = []₁
lmap₁ f (x ∷ xs) = f x ∷₁ lmap₁ f xs

head₁ : ∀ {A} {B : A -> Set} {x xs} -> List₁ B (x ∷ xs) -> B x
head₁ (y ∷₁ ys) = y

tail₁ : ∀ {A} {B : A -> Set} {x xs} -> List₁ B (x ∷ xs) -> List₁ B xs
tail₁ (y ∷₁ ys) = ys

_∈_ : ∀ {A} -> A -> List A -> Set
y ∈  []      = ⊥
y ∈ (x ∷ xs) = y ≡ x ⊎ y ∈ xs

-- The laziness is necessary.
replace₁ : ∀ {A} {B : A -> Set} {x} {xs : List A}
         -> (p : x ∈ xs) -> B x -> List₁ B xs -> List₁ B xs
replace₁ {xs = []}     ()          z []₁
replace₁ {xs = x ∷ xs} (inj₁ refl) z ys = z ∷₁ tail₁ ys
replace₁ {xs = x ∷ xs} (inj₂ p)    z ys = head₁ ys ∷₁ replace₁ p z (tail₁ ys)

Effectful : ∀ {R} -> Set
Effectful {R} = (A : Set) -> (A -> R) -> Set

AnEffect : Set -> Set
AnEffect R = R -> Effectful {R}

record Effect : Set where
  constructor the
  field
    {Res} : Set
    eff   : AnEffect Res
    res   : Res
open Effect public

data IFreer {R : Set} (Ψ : AnEffect R) : AnEffect R where
  return : ∀ {B r′} -> (y : B) -> IFreer Ψ (r′ y) B r′
  call   : ∀ {A B r r′ r′′} -> Ψ r A r′ -> (∀ x -> IFreer Ψ (r′ x) B r′′) -> IFreer Ψ r B r′′

perform : ∀ {R : Set} {Ψ : AnEffect R} {r A r′} -> Ψ r A r′ -> IFreer Ψ r A r′
perform a = call a return

_>>=_ : ∀ {R Ψ r B r′ C r′′}
      -> IFreer {R} Ψ r B r′ -> (∀ y -> IFreer Ψ (r′ y) C r′′) -> IFreer Ψ r C r′′
return y >>= g = g y
call a f >>= g = call a λ x -> f x >>= g

_>>_ : ∀ {R Ψ r₁ B r₂ C r′′}
     -> IFreer {R} Ψ r₁ B (const r₂) -> IFreer Ψ r₂ C r′′ -> IFreer Ψ r₁ C r′′
b >> c = b >>= const c

Effects : Set
Effects = List Effect

Union : ∀ Ψs -> List₁ Res Ψs -> (A : Set) -> (A -> List₁ Res Ψs) -> Set
Union  []       []₁      A rs′ = ⊥
Union (Ψ ∷ Ψs) (r ∷₁ rs) A rs′ = eff Ψ r A (head₁ ∘ rs′) ⊎ Union Ψs rs A (tail₁ ∘ rs′)

Eff : ∀ Ψs -> (B : Set) -> (B -> List₁ Res Ψs)  -> Set
Eff Ψs = IFreer (Union Ψs) (lmap₁ res Ψs)

inj′ : ∀ {Ψ A r′ Ψs}
     -> (p : Ψ ∈ Ψs)
     -> eff Ψ (res Ψ) A r′
     -> Union Ψs (lmap₁ res Ψs) A (λ x -> replace₁ p (r′ x) (lmap₁ res Ψs))
inj′ {Ψs = []}      ()         a
inj′ {Ψs = Ψ ∷ Ψs} (inj₁ refl) a = inj₁ a
inj′ {Ψs = Ψ ∷ Ψs} (inj₂ p)    a = inj₂ (inj′ p a)

inj : ∀ {Ψ A Ψs}
    -> (p : Ψ ∈ Ψs)
    -> eff Ψ (res Ψ) A (λ _ -> res Ψ)
    -> Union Ψs (lmap₁ res Ψs) A (λ _ -> lmap₁ res Ψs)
inj {Ψs = []}      ()         a
inj {Ψs = Ψ ∷ Ψs} (inj₁ refl) a = inj₁ a
inj {Ψs = Ψ ∷ Ψs} (inj₂ p)    a = inj₂ (inj p a)

invoke′ : ∀ {Ψ A r′ Ψs} {{p : Ψ ∈ Ψs}} -> eff Ψ (res Ψ) A r′ -> Eff Ψs A _
invoke′ {{p}} a = perform (inj′ p a)

invoke : ∀ {Ψ A Ψs} {{p : Ψ ∈ Ψs}} -> eff Ψ (res Ψ) A (λ _ -> res Ψ) -> Eff Ψs A _
invoke {{p}} a = perform (inj p a)
