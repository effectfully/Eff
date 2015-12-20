module Eff.Map where

open import Eff.Prelude

infixl 6 _^_
infix  3 _∈_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = ⊤
A ^ suc n = A × A ^ n

foldr : ∀ {n α β} {A : Set α}
      -> (B : ℕ -> Set β) -> (∀ {n} -> A -> B n -> B (suc n)) -> B 0 -> A ^ n -> B n
foldr {0}     B f z  tt      = z
foldr {suc n} B f z (x , xs) = f x (foldr B f z xs)

head : ∀ {n α} {A : Set α} -> A ^ suc n -> A
head (x , xs) = x

map : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B) -> A ^ n -> B ^ n
map f = foldr (_ ^_) (_,_ ∘ f) tt

_++_ : ∀ {n m α} {A : Set α} -> A ^ n -> A ^ m -> A ^ (n + m)
xs ++ ys = foldr (λ n -> _ ^ (n + _)) _,_ ys xs

lookup : ∀ {n α} {A : Set α} -> Fin n -> A ^ n -> A
lookup  zero   (x , xs) = x
lookup (suc i) (x , xs) = lookup i xs

replace : ∀ {n α} {A : Set α} -> Fin n -> A -> A ^ n -> A ^ n
replace  zero   y (x , xs) = y , xs
replace (suc i) y (x , xs) = x , replace i y xs

zipWith : ∀ {n α β γ} {A : Set α} {B : Set β} {C : Set γ}
        -> (A -> B -> C) -> A ^ n -> B ^ n -> C ^ n
zipWith {0}     f  tt       tt      = tt
zipWith {suc n} f (x , xs) (y , ys) = f x y , zipWith f xs ys

_⊔ⁿ_ : ∀ {n} -> Level ^ n -> Level -> Level
_⊔ⁿ_ = flip $ foldr _ _⊔_

max : ∀ {n} -> Level ^ n -> Level
max = _⊔ⁿ lzero

Sets : ∀ α -> ℕ -> Set (lsuc α)
Sets α n = Set α ^ n

Union : ∀ {n α} -> Sets α n -> Set α
Union = foldr _ _⊎_ ⊥

Setₛ : ∀ {n} -> (αs : Level ^ n) -> Set _
Setₛ αs = Set (max αs)

Setₖₛ : ∀ {n α} {A : Set α} -> (k : A -> Level) -> (xs : A ^ n) -> Set _
Setₖₛ k xs = Setₛ (map k xs)

Map : ∀ {n α} {A : Set α} {k : A -> Level}
    -> (∀ x -> Set (k x)) -> (xs : A ^ n) -> Setₖₛ k xs
Map {0}     B  tt      = ⊤
Map {suc n} B (x , xs) = B x × Map B xs

foldrᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)}
           {kₛ : ∀ {n} -> A ^ n -> Level} {xs : A ^ n}
       -> (C : ∀ {n} -> (xs : A ^ n) -> Set (kₛ xs))
       -> (∀ {n x} {xs : A ^ n} -> B x -> C xs -> C (x , xs))
       -> C {0} _
       -> Map B xs
       -> C xs
foldrᵐ {0}     B f z  tt      = z
foldrᵐ {suc n} B f z (y , ys) = f y (foldrᵐ B f z ys)

homo : ∀ {n α β} {A : Set α} {B : Set β} {xs : A ^ n} -> Map (λ _ -> B) xs -> B ^ n
homo {B = B} = foldrᵐ (λ {n} _ -> B ^ n) _,_ tt

headᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ suc n}
      -> Map B xs -> B (head xs)
headᵐ (y , ys) = y

mapᵐ : ∀ {n α} {A : Set α} {k₀ : A -> Level} {k₁ : A -> Level}
         {B : ∀ x -> Set (k₀ x)} {C : ∀ x -> Set (k₁ x)} {xs : A ^ n}
     -> (∀ {x} -> B x -> C x) -> Map B xs -> Map C xs
mapᵐ {C = C} f = foldrᵐ (Map C) (_,_ ∘ f) tt

lookupᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n}
        -> (i : Fin n) -> Map B xs -> B (lookup i xs)
lookupᵐ  zero   (y , ys) = y
lookupᵐ (suc i) (y , ys) = lookupᵐ i ys

replaceᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n} {x}
         -> (i : Fin n) -> B x -> Map B xs -> Map B (replace i x xs)
replaceᵐ  zero   y (z , ys) = y , ys
replaceᵐ (suc i) y (z , ys) = z , replaceᵐ i y ys

_∈_ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n} {x}
    -> B x -> Map B xs -> Set
y ∈ ys = Union (homo (mapᵐ (y ≅_) ys))

∈→Fin : ∀ n {α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)}
          {xs : A ^ n} {ys : Map B xs} {x} {y : B x}
      -> y ∈ ys -> Fin n
∈→Fin  0      ()
∈→Fin (suc n) (inj₁ r) = zero
∈→Fin (suc n) (inj₂ p) = suc (∈→Fin n p)

-- Tele : ∀ {n} -> (αs : Level ^ n) -> Setₖₛ lsuc αs
-- Tele {0}      tt      = ⊤
-- Tele {suc n} (α , αs) = Σ (Set α) λ A -> A -> Tele αs

-- Sum : ∀ {n} {αs : Level ^ n} -> Tele αs -> Setₛ αs
-- Sum {0}      tt     = ⊤
-- Sum {suc n} (A , F) = ∃ λ x -> Sum (F x)
