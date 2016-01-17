{-# OPTIONS --type-in-type #-}

module Loop.Core where

open import Prelude

infix  3 _∈₁_ _∈_
infixl 2 _>>=_
infixr 1 _>>_

List₁ : ∀ {A} (B : A -> Set) -> List A -> Set
List₁ B  []      = ⊤
List₁ B (x ∷ xs) = B x × List₁ B xs

lmap₁ : ∀ {A} {B : A -> Set} -> (∀ x -> B x) -> (xs : List A) -> List₁ B xs
lmap₁ f  []      = tt
lmap₁ f (x ∷ xs) = f x , lmap₁ f xs

head₁ : ∀ {A} {B : A -> Set} {x xs} -> List₁ B (x ∷ xs) -> B x
head₁ (y , ys) = y

tail₁ : ∀ {A} {B : A -> Set} {x xs} -> List₁ B (x ∷ xs) -> List₁ B xs
tail₁ (y , ys) = ys

data _∈₁_ {A} {B : A -> Set} {x} (y : B x) : ∀ {xs} -> List₁ B xs -> Set where
  here₁  : ∀ {xs} {ys : List₁ B xs} -> y ∈₁ y , ys
  there₁ : ∀ {x xs} {z : B x} {ys : List₁ B xs} -> y ∈₁ ys -> y ∈₁ z , ys 

_∈_ : ∀ {A} {B C : A -> Set} {x xs} -> B x × C x -> List₁ B xs × List₁ C xs -> Set
_∈_ {x = x₁} {[]}     (y₁ , z₁) (tt        , tt      )  = ⊥
_∈_ {x = x₁} {x₂ ∷ _} (y₁ , z₁) ((y₂ , ys) , (z₂ , zs)) = x₁ ≡ x₂ × y₁ ≅ y₂ × z₁ ≅ z₂
                                                        ⊎ y₁ , z₁ ∈ ys , zs

un∈ʳ : ∀ {A} {B C : A -> Set} {x xs} {y : B x} {z : C x} {ys : List₁ B xs} {zs : List₁ C xs}
     -> y , z ∈ ys , zs -> z ∈₁ zs
un∈ʳ {xs = []}     ()
un∈ʳ {xs = _ ∷ _} (inj₁ (refl , hrefl , hrefl)) = here₁
un∈ʳ {xs = _ ∷ _} (inj₂ p)                      = there₁ (un∈ʳ p)

replace₁ : ∀ {A} {B : A -> Set} {x} {xs : List A} {y : B x} {ys : List₁ B xs}
         -> B x -> y ∈₁ ys -> List₁ B xs
replace₁ {ys = y , ys} z  here₁     = z , ys
replace₁ {ys = y , ys} z (there₁ p) = y , replace₁ z p

--------------------

Sets : Set
Sets = List Set

HList : Sets -> Set
HList = List₁ id

Resources = HList

Effectful : ∀ {R} -> Set
Effectful {R} = (A : Set) -> (A -> R) -> Set
 
Effect : Set -> Set
Effect R = R -> Effectful {R}

Effects : Sets -> Set
Effects = List₁ Effect

-- The (∀ {Rs}) part might be too restrictive.
HigherEffect : Set
HigherEffect = ∀ {Rs} -> Effects Rs -> Effect (Resources Rs)

HigherEffects : Set
HigherEffects = List HigherEffect

Unionᵉ : HigherEffect
Unionᵉ {[]}     tt       tt      A rs′ = ⊥
Unionᵉ {_ ∷ _} (Ψ , Ψs) (r , rs) A rs′ =        Ψ  r  A (head₁ ∘ rs′)
                                       ⊎ Unionᵉ Ψs rs A (tail₁ ∘ rs′)

_⊎ᵒᵉ_ : HigherEffect -> HigherEffect -> HigherEffect
(Φ ⊎ᵒᵉ Ξ) Ψs rs A rs′ = Φ Ψs rs A rs′ ⊎ Ξ Ψs rs A rs′

Unionᵒᵉ : HigherEffects -> HigherEffect
Unionᵒᵉ = lfoldr _⊎ᵒᵉ_ (λ _ _ _ _ -> ⊥)

--------------------

data IFreer {R : Set} (Ψ : Effect R) : Effect R where
  return : ∀ {B r′} y -> IFreer Ψ (r′ y) B r′
  call   : ∀ {A B r r′ r′′} -> Ψ r A r′ -> (∀ x -> IFreer Ψ (r′ x) B r′′) -> IFreer Ψ r B r′′

liftᶠ : ∀ {R Ψ r A r′} -> Ψ r A r′ -> IFreer {R} Ψ r A r′
liftᶠ a = call a return

_>>=_ : ∀ {R Ψ r B r′ C r′′}
      -> IFreer {R} Ψ r B r′ -> (∀ y -> IFreer Ψ (r′ y) C r′′) -> IFreer Ψ r C r′′
return y >>= g = g y
call a f >>= g = call a λ x -> f x >>= g

_>>_ : ∀ {R Ψ r₁ B r₂ C r′′}
     -> IFreer {R} Ψ r₁ B (const r₂) -> IFreer Ψ r₂ C r′′ -> IFreer Ψ r₁ C r′′
b >> c = b >>= const c

--------------------

record WUnionᵒᵉ {Rs} Φs Ψs (rs : Resources Rs) A rs′ : Set where
  constructor wrapUnionᵒᵉ
  field unwrapUnionᵒᵉ : Unionᵒᵉ Φs Ψs rs A rs′

EffOver : HigherEffects -> HigherEffect
EffOver Φs Ψs = IFreer (WUnionᵒᵉ (Unionᵉ ∷ Φs) Ψs)

inj′ : ∀ {R} {Ψ : Effect R} {r A r′ Rs Ψs} {rs : Resources Rs}
     -> (p : Ψ , r ∈ Ψs , rs) -> Ψ r A r′ -> Unionᵉ Ψs rs A (λ x -> replace₁ (r′ x) (un∈ʳ p))
inj′ {Rs = []}     ()                           a
inj′ {Rs = _ ∷ _} (inj₁ (refl , hrefl , hrefl)) a = inj₁ a
inj′ {Rs = _ ∷ _} (inj₂  p)                     a = inj₂ (inj′ p a)

inj : ∀ {R} {Ψ : Effect R} {r A Rs Ψs} {rs : Resources Rs}
    -> (p : Ψ , r ∈ Ψs , rs) -> Ψ r A (const r) -> Unionᵉ Ψs rs A (const rs)
inj {Rs = []}     ()                           a
inj {Rs = _ ∷ _} (inj₁ (refl , hrefl , hrefl)) a = inj₁ a
inj {Rs = _ ∷ _} (inj₂  p)                     a = inj₂ (inj p a)

invoke′ : ∀ {Φs R} {Ψ : Effect R} {r A r′ Rs Ψs} {rs : Resources Rs} {{p : Ψ , r ∈ Ψs , rs}}
        -> Ψ r A r′ -> EffOver Φs Ψs rs A _
invoke′ {{p}} = liftᶠ ∘ wrapUnionᵒᵉ ∘ inj₁ ∘ inj′ p

invoke : ∀ {Φs R} {Ψ : Effect R} {r A Rs Ψs} {rs : Resources Rs} {{p : Ψ , r ∈ Ψs , rs}}
       -> Ψ r A (const r) -> EffOver Φs Ψs rs A _
invoke {{p}} = liftᶠ ∘ wrapUnionᵒᵉ ∘ inj₁ ∘ inj p

invoke₀ : ∀ {Φs R} {Ψ : Effect R} {r A r′ Rs Ψs} {rs : Resources Rs}
        -> Ψ r A r′ -> EffOver Φs (Ψ , Ψs) (r , rs) A _
invoke₀ {Ψ = Ψ} = invoke′ {Ψ = Ψ}

Eff : HigherEffect
Eff = EffOver []
