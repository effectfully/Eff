module Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Nat.Base hiding (_⊔_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Sum       renaming (map to smap) public
open import Data.Product   renaming (map to pmap; zip to pzip) hiding (,_) public
open import Data.List.Base renaming (map to lmap) hiding (foldr; _++_; zipWith; zip) public

infix  4 _≅_
infix  4 ,_
infixr 5 _<∨>_

pattern ,_ y = _ , y

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  constructor tt

data Bool {α} : Set α where
  true false : Bool

_<∨>_ : ∀ {α β} {B : Bool {α} -> Set β} -> B true -> B false -> ∀ b -> B b
(x <∨> y) true  = x
(x <∨> y) false = y

if_then_else_ : ∀ {α β} {B : Set β} -> Bool {α} -> B -> B -> B
if b then x else y = (x <∨> y) b

data _≅_ {α} {A : Set α} (x : A) : ∀ {β} {B : Set β} -> B -> Set where
  hrefl : x ≅ x

≅→≡ : ∀ {α} {A : Set α} {x y : A} -> x ≅ y -> x ≡ y
≅→≡ hrefl = refl

instance
  refl-instance : ∀ {α} {A : Set α} {x : A} -> x ≅ x
  refl-instance = hrefl

  ,-instance : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  ,-instance {{x}} {{y}} = x , y

  inj₁-instance : ∀ {α β} {A : Set α} {B : Set β} {{x : A}} -> A ⊎ B
  inj₁-instance {{x}} = inj₁ x

  inj₂-instance : ∀ {α β} {A : Set α} {B : Set β} {{x : B}} -> A ⊎ B
  inj₂-instance {{y}} = inj₂ y

first : ∀ {α β γ} {A : Set α} {B : Set β} {C : A -> Set γ}
      -> (∀ x -> C x) -> (p : A × B) -> C (proj₁ p) × B
first f (x , y) = f x , y

second : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (∀ {x} -> B x -> C x) -> Σ A B -> Σ A C
second g (x , y) = x , g y

third : ∀ {α β γ δ} {A : Set α} {B : A -> Set β}
          {C : ∀ {x} -> B x -> Set γ} {D : ∀ {x} -> B x -> Set δ}
      -> (∀ {x} {y : B x} -> C y -> D y) -> (∃ λ x -> Σ (B x) C) -> ∃ λ x -> Σ (B x) D
third h (x , y , z) = x , y , h z

fourth : ∀ {α β γ δ ε} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
           {D : ∀ {x} {y : B x} -> C y -> Set δ} {E : ∀ {x} {y : B x} -> C y -> Set ε}
       -> (∀ {x} {y : B x} {z : C y} -> D z -> E z)
       -> (∃ λ x -> Σ (B x) λ y -> Σ (C y) D)
       -> ∃ λ x -> Σ (B x) λ y -> Σ (C y) E
fourth f (x , y , z , w) = x , y , z , f w

uncurryᵏ : ∀ {α β} {A : Set α} {B : A -> Set β} {k : Σ A B -> Level} {C : ∀ p -> Set (k p)}
         -> (∀ x -> (y : B x) -> C (x , y)) -> (p : Σ A B) -> C p
uncurryᵏ f (x , y) = f x y
