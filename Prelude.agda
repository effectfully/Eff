module Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function renaming (_∘′_ to _∘_; _∘_ to _∘′_) public
open import Relation.Nullary public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Nat.Base hiding (_⊔_; _≟_) public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Fin using (Fin; zero; suc) public
open import Data.Fin.Properties using (_≟_) public
open import Data.Maybe.Base hiding (map) public
open import Data.Sum        renaming (map to smap) public
open import Data.Product    renaming (map to pmap; zip to pzip) hiding (,_) public
open import Data.List.Base  renaming (map to lmap; foldr to lfoldr; _++_ to _l++_)
  hiding (zipWith; zip) public

infix  4  ,_
infixr 10 _%
infix  3  _≅_
infixr 5  _<∨>_
infixl 2  _>>=ₘ_
infixl 6  _<$>ₘ_ _<*>ₘ_

pattern ,_ y = _ , y

_% = _∘_

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  constructor tt

⊥₀    = ⊥ {lzero}
⊤₀    = ⊤ {lzero}

⊥-elim : ∀ {α β} {A : Set α} -> ⊥ {β} -> A
⊥-elim ()

_<∨>_ : ∀ {α} {B : Bool -> Set α} -> B false -> B true -> ∀ b -> B b
(x <∨> y) false = x
(x <∨> y) true  = y

True : Bool -> Set
True false = ⊥
True true  = ⊤

False : Bool -> Set
False = True ∘ not

if′_then_else_ : ∀ {α} {A : Set α} b -> (True b -> A) -> (False b -> A) -> A
if′ true  then f else g = f tt
if′ false then f else g = g tt

_>>=ₘ_ : ∀ {α β} {A : Set α} {B : Set β} -> Maybe A -> (A -> Maybe B) -> Maybe B
a >>=ₘ f = maybe′ f nothing a

_<$>ₘ_ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> Maybe A -> Maybe B
f <$>ₘ a = a >>=ₘ just ∘ f

_<*>ₘ_ : ∀ {α β} {A : Set α} {B : Set β} -> Maybe (A -> B) -> Maybe A -> Maybe B
h <*>ₘ a = h >>=ₘ _<$>ₘ a

data _≅_ {α} {A : Set α} (x : A) : ∀ {β} {B : Set β} -> B -> Set where
  hrefl : x ≅ x

hsym : ∀ {α β} {A : Set α} {B : Set β} {x : A} {y : B} -> x ≅ y -> y ≅ x
hsym hrefl = hrefl

≅→≡ : ∀ {α} {A : Set α} {x y : A} -> x ≅ y -> x ≡ y
≅→≡ hrefl = refl

module TrustMe where
  import Relation.Binary.PropositionalEquality.TrustMe as T

  trustMe : ∀ {α} {A : Set α} -> (x y : A) -> x ≡ y
  trustMe _ _ = T.trustMe

  Coerce : ∀ {β α} -> Set α -> Set β
  Coerce {β} {α} rewrite trustMe α β = id

  uncoerce-cong : ∀ {β α} {A : Set α} -> (F : ∀ {α} -> Set α -> Set α) -> F (Coerce {β} A) -> F A
  uncoerce-cong {β} {α} F rewrite trustMe α β = id

  uncoerce : ∀ {β α} {A : Set α} -> Coerce {β} A -> A
  uncoerce = uncoerce-cong id

  Coerce-≅→≡ : ∀ {α β} {A : Set α} {B : Set β} -> A ≅ B -> Coerce A ≡ B
  Coerce-≅→≡ {α} {β} rewrite trustMe α β = ≅→≡

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

_[>_<]_ : ∀ {α β γ δ ε} {A : Set α} {B : A -> Set β}
            {C : A -> Set γ} {D : ∀ {x} -> B x -> Set δ}
            {E : ∀ {x} {y : B x} -> C x -> D y -> Set ε}
        -> (f : ∀ x -> C x)
        -> (∀ {x y} -> (c : C x) -> (d : D y) -> E c d)
        -> (g : ∀ {x} -> (y : B x) -> D y)
        -> (p : Σ A B)
        -> E (f (proj₁ p)) (g (proj₂ p))
(f [> h <] g) (x , y) = h (f x) (g y)

uncurryᵏ : ∀ {α β} {A : Set α} {B : A -> Set β} {k : Σ A B -> Level} {C : ∀ p -> Set (k p)}
         -> (∀ x -> (y : B x) -> C (x , y)) -> (p : Σ A B) -> C p
uncurryᵏ f (x , y) = f x y
