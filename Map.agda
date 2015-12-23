module Map where

open import Prelude

infixl 6 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = ⊤
A ^ suc n = A × A ^ n

foldr : ∀ {n α β} {A : Set α}
      -> (B : ℕ -> Set β) -> (∀ {n} -> A -> B n -> B (suc n)) -> B 0 -> A ^ n -> B n
foldr {0}     B f z  tt      = z
foldr {suc n} B f z (x , xs) = f x (foldr B f z xs)

head : ∀ {n α} {A : Set α} -> A ^ suc n -> A
head (x , xs) = x

tail : ∀ {n α} {A : Set α} -> A ^ suc n -> A ^ n
tail (x , xs) = xs

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

zip : ∀ {n α β} {A : Set α} {B : Set β} -> A ^ n -> B ^ n -> (A × B) ^ n
zip = zipWith _,_

projs₁ : ∀ {n α β} {A : Set α} {B : Set β} -> (A × B) ^ n -> A ^ n
projs₁ = map proj₁

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

Setᵐ : ∀ {n α} {A : Set α} -> (k : A -> Level) -> (xs : A ^ n) -> Set _
Setᵐ k xs = Setₛ (map k xs)

Map : ∀ {n α} {A : Set α} {k : A -> Level}
    -> (∀ x -> Set (k x)) -> (xs : A ^ n) -> Setᵐ k xs
Map {0}     B  tt      = ⊤
Map {suc n} B (x , xs) = B x × Map B xs

headᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ suc n}
      -> Map B xs -> B (head xs)
headᵐ (y , ys) = y

tailᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ suc n}
      -> Map B xs -> Map B (tail xs)
tailᵐ (y , ys) = ys

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

mapᵐ : ∀ {n α} {A : Set α} {k₀ : A -> Level} {k₁ : A -> Level}
         {B : ∀ x -> Set (k₀ x)} {C : ∀ x -> Set (k₁ x)} {xs : A ^ n}
     -> (∀ {x} -> B x -> C x) -> Map B xs -> Map C xs
mapᵐ {C = C} f = foldrᵐ (Map C) (_,_ ∘ f) tt

lookupᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n}
        -> (i : Fin n) -> Map B xs -> B (lookup i xs)
lookupᵐ  zero   (y , ys) = y
lookupᵐ (suc i) (y , ys) = lookupᵐ i ys

replaceᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n}
         -> (i : Fin n) -> B (lookup i xs) -> Map B xs -> Map B xs
replaceᵐ  zero   y (z , ys) = y , ys
replaceᵐ (suc i) y (z , ys) = z , replaceᵐ i y ys

Setᶻ : ∀ {n α β} {A : Set α} {B : Set β}
     -> (k : A -> B -> Level) -> (xs : A ^ n) -> (ys : B ^ n) -> Set _
Setᶻ k xs ys = Setₛ (zipWith k xs ys)

-- We could define `Zip' in terms of `Map' and `zip',
-- but then we would need to define some annoying coercions.
Zip : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
    -> (∀ x y -> Set (k x y)) -> (xs : A ^ n) -> (ys : B ^ n) -> Setᶻ k xs ys
Zip {0}     C  tt       tt      = ⊤
Zip {suc n} C (x , xs) (y , ys) = C x y × Zip C xs ys

headᶻ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
          {C : ∀ x y -> Set (k x y)} {xs : A ^ suc n} {ys : B ^ suc n}
      -> Zip C xs ys -> C (head xs) (head ys)
headᶻ (y , ys) = y

tailᶻ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
          {C : ∀ x y -> Set (k x y)} {xs : A ^ suc n} {ys : B ^ suc n}
      -> Zip C xs ys -> Zip C (tail xs) (tail ys)
tailᶻ (y , ys) = ys

foldrᶻ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level} {C : ∀ x y -> Set (k x y)}
           {kₛ : ∀ {n} -> A ^ n -> B ^ n -> Level} {xs : A ^ n} {ys : B ^ n}
       -> (D : ∀ {n} -> (xs : A ^ n) -> (ys : B ^ n) -> Set (kₛ xs ys))
       -> (∀ {n x y} {xs : A ^ n} {ys : B ^ n} -> C x y -> D xs ys -> D (x , xs) (y , ys))
       -> D tt tt
       -> Zip C xs ys
       -> D xs ys
foldrᶻ {0}     B f w  tt      = w
foldrᶻ {suc n} B f w (z , zs) = f z (foldrᶻ B f w zs)

mapᶻ : ∀ {n α β} {A : Set α} {B : Set β} {k₀ k₁ : A -> B -> Level}
         {C : ∀ x y -> Set (k₀ x y)} {D : ∀ x y -> Set (k₁ x y)}
         {xs : A ^ n} {ys : B ^ n}
     -> (∀ {x y} -> C x y -> D x y) -> Zip C xs ys -> Zip D xs ys
mapᶻ {D = D} f = foldrᶻ (Zip D) (_,_ ∘ f) tt

lookupᶻ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
            {C : ∀ x y -> Set (k x y)} {xs : A ^ n} {ys : B ^ n}
        -> (i : Fin n) -> Zip C xs ys -> C (lookup i xs) (lookup i ys)
lookupᶻ  zero   (z , zs) = z
lookupᶻ (suc i) (z , zs) = lookupᶻ i zs
