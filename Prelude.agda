module Eff.Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Data.Nat.Base hiding (_⊔_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Sum       renaming (map to smap) public
open import Data.Product   renaming (map to pmap) hiding (,_) public
open import Data.List.Base renaming (map to lmap) hiding (foldr; _++_; zipWith; zip) public

infix 4 _≅_
infix 4 ,_

pattern ,_ y = _ , y

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  constructor tt

data _≅_ {α} {A : Set α} (x : A) : ∀ {β} {B : Set β} -> B -> Set where
  hrefl : x ≅ x

hsym : ∀ {α β} {A : Set α} {B : Set β} {x : A} {y : B} -> x ≅ y -> y ≅ x
hsym hrefl = hrefl

hsubst : ∀ {α β} {A : Set α} {x y} -> (B : A -> Set β) -> x ≅ y -> B x -> B y
hsubst B hrefl = id

instance
  refl-instance : ∀ {α} {A : Set α} {x : A} -> x ≅ x
  refl-instance = hrefl

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

uncurryᵏ : ∀ {α β} {A : Set α} {B : A -> Set β} {k : Σ A B -> Level} {C : ∀ p -> Set (k p)}
         -> (∀ x -> (y : B x) -> C (x , y)) -> (p : Σ A B) -> C p
uncurryᵏ f (x , y) = f x y

record Wrap {α} {A : Set α} {k : A -> Level} (B : ∀ x -> Set (k x)) (x : A) : Set (k x) where
  constructor wrap
  field unwrap : B x
open Wrap public

Wrap₂ : ∀ {α β} {A : Set α} {B : A -> Set β} {k : ∀ {x} -> B x -> Level}
      -> (∀ x -> (y : B x) -> Set (k y)) -> ∀ x -> (y : B x) -> Set (k y)
Wrap₂ C x y = Wrap (uncurryᵏ C) (x , y)

Wrap₃ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
          {k : ∀ {x} {y : B x} -> (z : C y) -> Level} 
      -> (∀ x -> (y : B x) -> (z : C y) -> Set (k z)) -> ∀ x -> (y : B x) -> (z : C y) -> Set (k z)
Wrap₃ D x y z = Wrap₂ (λ z -> uncurryᵏ (D z)) x (y , z)

module _ where
  open import Relation.Binary.PropositionalEquality.TrustMe

  Coerce : ∀ {α₁ α₂ β γ} {F : Set α₁ -> Set β} {G : Set α₂ -> Set γ}
         -> F ≅ G -> Set α₁ -> Set α₂
  Coerce {α₁} {α₂} p A rewrite trustMe {x = α₁} {α₂} = A

  uncoerce : ∀ {α₁ α₂ β γ} {F : Set α₁ -> Set β} {G : Set α₂ -> Set γ} {p : F ≅ G} {A : Set α₁}
           -> Coerce p A -> A
  uncoerce {α₁} {α₂} rewrite trustMe {x = α₁} {α₂} = id

  hSubst : ∀ {α₁ α₂ β γ} {F : Set α₁ -> Set β} {G : Set α₂ -> Set γ} {A}
         -> (p : F ≅ G) -> F A -> G (Coerce p A)
  hSubst {α₁} {α₂} {β} {γ} rewrite trustMe {x = α₁} {α₂} | trustMe {x = β} {γ} = hsubst (_$ _)
