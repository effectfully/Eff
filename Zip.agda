module Eff.Zip where

open import Eff.Prelude

infixl 6 _^_
infix  3 _∈_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = ⊤
A ^ suc n = A × A ^ n

foldr : ∀ {n α β} {A : Set α}
      -> (B : ℕ -> Set β) -> (∀ {n} -> A -> B n -> B (suc n)) -> B 0 -> A ^ n -> B n
foldr {0}     B f z  _       = z
foldr {suc n} B f z (x , xs) = f x (foldr B f z xs)

head : ∀ {n α} {A : Set α} -> A ^ suc n -> A
head (x , xs) = x

map : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B) -> A ^ n -> B ^ n
map f = foldr (_ ^_) (_,_ ∘ f) _

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
zipWith {0}     f  _        _       = _
zipWith {suc n} f (x , xs) (y , ys) = f x y , zipWith f xs ys

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

Setₖₛ : ∀ {n α β} {A : Set α} {B : Set β}
      -> (k : A -> B -> Level) -> (xs : A ^ n) -> (ys : B ^ n) -> Set _
Setₖₛ k xs ys = Setₛ (zipWith k xs ys)

Zip : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
    -> (∀ x y -> Set (k x y)) -> (xs : A ^ n) -> (ys : B ^ n) -> Setₖₛ k xs ys
Zip {0}     C  _        _       = ⊤
Zip {suc n} C (x , xs) (y , ys) = C x y × Zip C xs ys

foldrᶻ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level} {C : ∀ x y -> Set (k x y)}
           {kₛ : ∀ {n} -> A ^ n -> B ^ n -> Level} {xs : A ^ n} {ys : B ^ n}
       -> (D : ∀ {n} -> (xs : A ^ n) -> (ys : B ^ n) -> Set (kₛ xs ys))
       -> (∀ {n x y} {xs : A ^ n} {ys : B ^ n} -> C x y -> D xs ys -> D (x , xs) (y , ys))
       -> D {0} _ _
       -> Zip C xs ys
       -> D xs ys
foldrᶻ {0}     B f w  _       = w
foldrᶻ {suc n} B f w (z , zs) = f z (foldrᶻ B f w zs)

homo : ∀ {n α β γ} {A : Set α} {B : Set β} {C : Set γ} {xs : A ^ n} {ys : B ^ n}
     -> Zip (λ _ _ -> C) xs ys -> C ^ n
homo {C = C} = foldrᶻ (λ {n} _ _ -> C ^ n) _,_ _

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

replaceᶻ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
             {C : ∀ x y -> Set (k x y)} {xs : A ^ n} {ys : B ^ n} {x y}
         -> (i : Fin n) -> C x y -> Zip C xs ys -> Zip C (replace i x xs) (replace i y ys)
replaceᶻ  zero   w (z , zs) = w , zs
replaceᶻ (suc i) w (z , zs) = z , replaceᶻ i w zs

_∈_ : ∀ {n α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
        {C : ∀ x y -> Set (k x y)} {xs : A ^ n} {ys : B ^ n} {x y}
    -> C x y -> Zip C xs ys -> Set
y ∈ ys = Unionʰ (homo (mapᶻ (y ≅_) ys))

∈→Fin : ∀ n {α β} {A : Set α} {B : Set β} {k : A -> B -> Level}
          {C : ∀ x y -> Set (k x y)} {xs : A ^ n} {ys : B ^ n}
          {x y} {z : C x y} {zs : Zip C xs ys}
      -> z ∈ zs -> Fin n
∈→Fin  0       ()
∈→Fin (suc n) (inj₁ r) = zero
∈→Fin (suc n) (inj₂ p) = suc (∈→Fin n p)
