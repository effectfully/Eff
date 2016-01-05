module Map where

open import Prelude

infixl 6 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = ⊤
A ^ suc n = A × A ^ n

_²^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ²^ n = (A × A) ^ n

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

Setsʰ : ∀ α -> ℕ -> Set (lsuc α)
Setsʰ α n = Set α ^ n

Unionʰ : ∀ {n α} -> Setsʰ α n -> Set α
Unionʰ = foldr _ _⊎_ ⊥

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

hetero : ∀ {n α β} {A : Set α} {B : Set β} {xs : A ^ n} -> B ^ n -> Map (λ _ -> B) xs
hetero {0}      tt      = tt
hetero {suc n} (y , ys) = y , hetero ys

mapᵐ : ∀ {n α} {A : Set α} {k₀ : A -> Level} {k₁ : A -> Level}
         {B : ∀ x -> Set (k₀ x)} {C : ∀ x -> Set (k₁ x)} {xs : A ^ n}
     -> (∀ {x} -> B x -> C x) -> Map B xs -> Map C xs
mapᵐ {C = C} f = foldrᵐ (Map C) (_,_ ∘ f) tt

_++ᵐ_ : ∀ {n m α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n} {ys : A ^ m}
      -> Map B xs -> Map B ys -> Map B (xs ++ ys)
yz ++ᵐ zs = foldrᵐ (λ xs -> Map _ (xs ++ _)) _,_ zs yz

lookupᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n}
        -> (i : Fin n) -> Map B xs -> B (lookup i xs)
lookupᵐ  zero   (y , ys) = y
lookupᵐ (suc i) (y , ys) = lookupᵐ i ys

replaceᵐ : ∀ {n α} {A : Set α} {k : A -> Level} {B : ∀ x -> Set (k x)} {xs : A ^ n}
         -> (i : Fin n) -> B (lookup i xs) -> Map B xs -> Map B xs
replaceᵐ  zero   y (z , ys) = y , ys
replaceᵐ (suc i) y (z , ys) = z , replaceᵐ i y ys

Sets : ∀ {n} -> (αs : Level ^ n) -> _
Sets = Map (λ α -> Set α)

HList : ∀ {n} {αs : Level ^ n} -> Sets αs -> Setₛ αs
HList = foldrᵐ Setₛ _×_ ⊤

headʰ : ∀ n {αs : Level ^ suc n} {As : Sets αs} -> HList As -> headᵐ As
headʰ n (x , xs) = x

tailʰ : ∀ n {αs : Level ^ suc n} {As : Sets αs} -> HList As -> HList (tailᵐ As)
tailʰ n (x , xs) = xs

lookupʰ : ∀ {n} {αs : Level ^ n} {As : Sets αs}
        -> (i : Fin n) -> HList As -> lookupᵐ i As
lookupʰ  zero   (x , xs) = x
lookupʰ (suc i) (x , xs) = lookupʰ i xs

replaceʰ : ∀ {n} {αs : Level ^ n} {As : Sets αs}
         -> (i : Fin n) -> lookupᵐ i As -> HList As -> HList As
replaceʰ  zero   x (y , xs) = x , xs
replaceʰ (suc i) x (y , xs) = y , replaceʰ i x xs
