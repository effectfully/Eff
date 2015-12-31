module Lifts where

open import Prelude
open import Map

-- ∀′ : ∀ {α β} {A : Set α} -> (A -> Set β) -> Set (α ⊔ β)
-- ∀′ B = ∀ x -> B x

-- Liftᵐ-go : ∀ {n α γ} {A : Set α}
--              β (k : A -> Level) i (xs : A ^ n) {B : Set (k (lookup i xs))}
--          -> ((B -> Set γ) -> Set (k (lookup i xs) ⊔ γ))
--          -> (B -> Set γ)
--          -> Set (β ⊔ max (map k xs) ⊔ γ)
-- Liftᵐ-go β k  zero    xs      F C = Lift {ℓ = β ⊔ max (map k xs)} (F C)
-- Liftᵐ-go β k (suc i) (x , xs) F C = Liftᵐ-go (β ⊔ k x) k i xs F C

-- This generalizes `Lift∃ᵐ' and `Lift∀ᵐ', but not very much,
-- and we then also need to generalize `Lift∃ᶻ', so I decided to use ad hoc versions.
-- Liftᵐ : ∀ {n α γ} {A : Set α}
--           (k : A -> Level) i (xs : A ^ n) {B : Set (k (lookup i xs))}
--       -> ((B -> Set γ) -> Set (k (lookup i xs) ⊔ γ))
--       -> (B -> Set γ)
--       -> Set (max (map k xs) ⊔ γ)
-- Liftᵐ = Liftᵐ-go lzero

Lift∃ᵐ-go : ∀ {n α γ} {A : Set α}
              β (k : A -> Level) i (xs : A ^ n) {B : Set (k (lookup i xs))}
          -> (B -> Set γ) -> Set (β ⊔ max (map k xs) ⊔ γ)
Lift∃ᵐ-go β k  zero    xs      C = Lift {ℓ = β ⊔ max (map k xs)} (∃ C)
Lift∃ᵐ-go β k (suc i) (x , xs) C = Lift∃ᵐ-go (β ⊔ k x) k i xs C

Lift∃ᵐ : ∀ {n α γ} {A : Set α}
           (k : A -> Level) i (xs : A ^ n) {B : Set (k (lookup i xs))}
       -> (B -> Set γ) -> Set (max (map k xs) ⊔ γ)
Lift∃ᵐ = Lift∃ᵐ-go lzero

lift∃ᵐ-go : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
              β i {B : Set (k (lookup i xs))} {C : B -> Set γ}
          -> ∃ C -> Lift∃ᵐ-go β k i xs C
lift∃ᵐ-go                 β  zero   p = lift p
lift∃ᵐ-go {k = k} {x , _} β (suc i) p = lift∃ᵐ-go (β ⊔ k x) i p

lift∃ᵐ : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
           i {B : Set (k (lookup i xs))} {C : B -> Set γ}
       -> ∃ C -> Lift∃ᵐ k i xs C
lift∃ᵐ = lift∃ᵐ-go lzero

lower∃ᵐ-go : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
               β i {B : Set (k (lookup i xs))} {C : B -> Set γ}
           -> Lift∃ᵐ-go β k i xs C -> ∃ C
lower∃ᵐ-go                 β  zero   p = lower p
lower∃ᵐ-go {k = k} {x , _} β (suc i) p = lower∃ᵐ-go (β ⊔ k x) i p

lower∃ᵐ : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
            i {B : Set (k (lookup i xs))} {C : B -> Set γ}
        -> Lift∃ᵐ k i xs C -> ∃ C
lower∃ᵐ = lower∃ᵐ-go lzero

Lift∃ᶻ-go : ∀ {n α β δ} {A : Set α} {B : Set β}
              γ (k : A -> B -> Level) i (xs : A ^ n) (ys : B ^ n)
              {C : Set (k (lookup i xs) (lookup i ys))}
          -> (C -> Set δ) -> Set (γ ⊔ max (zipWith k xs ys) ⊔ δ)
Lift∃ᶻ-go γ k  zero    xs       ys      D = Lift {ℓ = γ ⊔ max (zipWith k xs ys)} (∃ D)
Lift∃ᶻ-go γ k (suc i) (x , xs) (y , ys) D = Lift∃ᶻ-go (γ ⊔ k x y) k i xs ys D

Lift∃ᶻ : ∀ {n α β δ} {A : Set α} {B : Set β}
           (k : A -> B -> Level) i (xs : A ^ n) (ys : B ^ n)
           {C : Set (k (lookup i xs) (lookup i ys))}
       -> (C -> Set δ) -> Set (max (zipWith k xs ys) ⊔ δ)
Lift∃ᶻ = Lift∃ᶻ-go lzero

lift∃ᶻ-go : ∀ {n α β δ} {A : Set α} {B : Set β}
              {k : A -> B -> Level} {xs : A ^ n} {ys : B ^ n}
              γ i {C : Set (k (lookup i xs) (lookup i ys))} {D : C -> Set δ}
          -> ∃ D -> Lift∃ᶻ-go γ k i xs ys D
lift∃ᶻ-go                         γ  zero   p = lift p
lift∃ᶻ-go {k = k} {x , _} {y , _} γ (suc i) p = lift∃ᶻ-go (γ ⊔ k x y) i p

lift∃ᶻ : ∀ {n α β δ} {A : Set α} {B : Set β}
           {k : A -> B -> Level} {xs : A ^ n} {ys : B ^ n}
           i {C : Set (k (lookup i xs) (lookup i ys))} {D : C -> Set δ}
       -> ∃ D -> Lift∃ᶻ k i xs ys D
lift∃ᶻ = lift∃ᶻ-go lzero

lower∃ᶻ-go : ∀ {n α β δ} {A : Set α} {B : Set β}
               {k : A -> B -> Level} {xs : A ^ n} {ys : B ^ n}
               γ i {C : Set (k (lookup i xs) (lookup i ys))} {D : C -> Set δ}
           -> Lift∃ᶻ-go γ k i xs ys D -> ∃ D
lower∃ᶻ-go                         γ  zero   p = lower p
lower∃ᶻ-go {k = k} {x , _} {y , _} γ (suc i) p = lower∃ᶻ-go (γ ⊔ k x y) i p

lower∃ᶻ : ∀ {n α β δ} {A : Set α} {B : Set β}
            {k : A -> B -> Level} {xs : A ^ n} {ys : B ^ n}
            i {C : Set (k (lookup i xs) (lookup i ys))} {D : C -> Set δ}
        -> Lift∃ᶻ k i xs ys D -> ∃ D
lower∃ᶻ = lower∃ᶻ-go lzero

Lift∀ᵐ-go : ∀ {n α γ} {A : Set α}
              β (k : A -> Level) i (xs : A ^ n) {B : Set (k (lookup i xs))}
          -> (B -> Set γ) -> Set (β ⊔ max (map k xs) ⊔ γ)
Lift∀ᵐ-go β k  zero    xs      C = Lift {ℓ = β ⊔ max (map k xs)} (∀ y -> C y)
Lift∀ᵐ-go β k (suc i) (x , xs) C = Lift∀ᵐ-go (β ⊔ k x) k i xs C

Lift∀ᵐ : ∀ {n α γ} {A : Set α}
           (k : A -> Level) i (xs : A ^ n) {B : Set (k (lookup i xs))}
       -> (B -> Set γ) -> Set (max (map k xs) ⊔ γ)
Lift∀ᵐ = Lift∀ᵐ-go lzero

lift∀ᵐ-go : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
              β i {B : Set (k (lookup i xs))} {C : B -> Set γ}
          -> (∀ y -> C y) -> Lift∀ᵐ-go β k i xs C
lift∀ᵐ-go                 β  zero   h = lift h
lift∀ᵐ-go {k = k} {x , _} β (suc i) h = lift∀ᵐ-go (β ⊔ k x) i h

lift∀ᵐ : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
           i {B : Set (k (lookup i xs))} {C : B -> Set γ}
       -> (∀ y -> C y) -> Lift∀ᵐ k i xs C
lift∀ᵐ = lift∀ᵐ-go lzero

lower∀ᵐ-go : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
               β i {B : Set (k (lookup i xs))} {C : B -> Set γ}
           -> Lift∀ᵐ-go β k i xs C -> (∀ y -> C y)
lower∀ᵐ-go                 β  zero   h = lower h
lower∀ᵐ-go {k = k} {x , _} β (suc i) h = lower∀ᵐ-go (β ⊔ k x) i h

lower∀ᵐ : ∀ {n α γ} {A : Set α} {k : A -> Level} {xs : A ^ n}
            i {B : Set (k (lookup i xs))} {C : B -> Set γ}
        -> Lift∀ᵐ k i xs C -> (∀ y -> C y)
lower∀ᵐ = lower∀ᵐ-go lzero
