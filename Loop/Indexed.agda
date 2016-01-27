{-# OPTIONS --type-in-type #-}

module Loop.Indexed where

open import Prelude

infix  3 _∈₁_ _∈²_
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

_∈²_ : ∀ {A} {B C : A -> Set} {x xs} -> B x × C x -> List₁ B xs × List₁ C xs -> Set
_∈²_ {x = x₁} {[]}     (y₁ , z₁) (tt        , tt      )  = ⊥
_∈²_ {x = x₁} {x₂ ∷ _} (y₁ , z₁) ((y₂ , ys) , (z₂ , zs)) = x₁ ≡ x₂ × y₁ ≅ y₂ × z₁ ≅ z₂
                                                        ⊎ y₁ , z₁ ∈² ys , zs

un∈ʳ : ∀ {A} {B C : A -> Set} {x xs} {y : B x} {z : C x} {ys : List₁ B xs} {zs : List₁ C xs}
     -> y , z ∈² ys , zs -> z ∈₁ zs
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

IHigherEffect : Set -> Set
IHigherEffect I = I -> HigherEffect

IHigherEffects : Sets -> Set
IHigherEffects = List₁ IHigherEffect

toI : HigherEffect -> IHigherEffect ⊤
toI Ψ tt = Ψ

Unionᵉ : HigherEffect
Unionᵉ {[]}     tt       tt      A rs′ = ⊥
Unionᵉ {_ ∷ _} (Ψ , Ψs) (r , rs) A rs′ = Ψ r A (head₁ ∘ rs′) ⊎ Unionᵉ Ψs rs A (tail₁ ∘ rs′)

Unionʰᵉ : ∀ {Is} -> IHigherEffects Is -> IHigherEffect (HList Is)
Unionʰᵉ {[]}      tt       tt      Ψs rs A rs′ = ⊥
Unionʰᵉ {I ∷ Is} (Φ , Φs) (i , is) Ψs rs A rs′ = Φ i Ψs rs A rs′ ⊎ Unionʰᵉ Φs is Ψs rs A rs′

--------------------

data IFreer {R : Set} (Ψ : Effect R) : Effect R where
  return : ∀ {B r′} y -> IFreer Ψ (r′ y) B r′
  call   : ∀ {r A r′ B r′′} -> Ψ r A r′ -> (∀ x -> IFreer Ψ (r′ x) B r′′) -> IFreer Ψ r B r′′

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

record WUnionʰᵉ {Is Rs} (Φs : IHigherEffects Is) is (Ψs : Effects Rs) rs A rs′ : Set where
  constructor wUnionʰᵉ
  field unwUnionʰᵉ : Unionʰᵉ Φs is Ψs rs A rs′

pattern wcall a f = call (wUnionʰᵉ a) f 

EffOver : ∀ {Is} -> IHigherEffects Is -> IHigherEffect (HList Is)
EffOver Φs is Ψs = IFreer (WUnionʰᵉ (toI Unionᵉ , Φs) (tt , is) Ψs)

inj′ : ∀ {R} {Ψ : Effect R} {r A r′ Rs rs} {Ψs : Effects Rs}
     -> (p : Ψ , r ∈² Ψs , rs) -> Ψ r A r′ -> Unionᵉ Ψs rs A (λ x -> replace₁ (r′ x) (un∈ʳ p))
inj′ {Rs = []}     ()
inj′ {Rs = _ ∷ _} (inj₁ (refl , hrefl , hrefl)) = inj₁
inj′ {Rs = _ ∷ _} (inj₂  p)                     = inj₂ ∘ inj′ p

inj : ∀ {R} {Ψ : Effect R} {r A Rs rs} {Ψs : Effects Rs}
    -> Ψ , r ∈² Ψs , rs -> Ψ r A (const r) -> Unionᵉ Ψs rs A (const rs)
inj {Rs = []}     ()
inj {Rs = _ ∷ _} (inj₁ (refl , hrefl , hrefl)) = inj₁
inj {Rs = _ ∷ _} (inj₂  p)                     = inj₂ ∘ inj p

invoke′ : ∀ {Is} {Φs : IHigherEffects Is} {is R r A r′ Rs rs}
            {Ψ : Effect R} {Ψs : Effects Rs} {{p : Ψ , r ∈² Ψs , rs}}
        -> Ψ r A r′ -> EffOver Φs is Ψs rs A _
invoke′ {{p}} = liftᶠ ∘ wUnionʰᵉ ∘ inj₁ ∘ inj′ p

invoke : ∀ {Is} {Φs : IHigherEffects Is} {is R r A Rs rs}
           {Ψ : Effect R} {Ψs : Effects Rs} {{p : Ψ , r ∈² Ψs , rs}}
       -> Ψ r A (const r) -> EffOver Φs is Ψs rs A _
invoke {{p}} = liftᶠ ∘ wUnionʰᵉ ∘ inj₁ ∘ inj p

hinj : ∀ {Is I} {Φ : IHigherEffect I} {Φs : IHigherEffects Is}
         {is i Rs rs A rs′} {Ψs : Effects Rs}
     -> Φ , i ∈² Φs , is -> Φ i Ψs rs A rs′ -> Unionʰᵉ Φs is Ψs rs A rs′
hinj {[]}      ()
hinj {_ ∷ _} (inj₁ (refl , hrefl , hrefl)) = inj₁
hinj {_ ∷ _} (inj₂  p)                     = inj₂ ∘ hinj p

hinvoke : ∀ {Is I} {Φ : IHigherEffect I} {Φs : IHigherEffects Is}
            {is i Rs rs A rs′} {Ψs : Effects Rs} {{p : Φ , i ∈² Φs , is}}
        -> Φ i Ψs rs A rs′ -> EffOver Φs is Ψs rs A rs′
hinvoke {{p}} = liftᶠ ∘ wUnionʰᵉ ∘ inj₂ ∘ hinj p

hinvoke₀ : ∀ {Is I} {Φ : IHigherEffect I} {Φs : IHigherEffects Is}
            {is i Rs rs A rs′} {Ψs : Effects Rs}
         -> Φ i Ψs rs A rs′ -> EffOver (Φ , Φs) (i , is) Ψs rs A rs′
hinvoke₀ {Φ = Φ} = hinvoke {Φ = Φ}

Eff : HigherEffect
Eff = EffOver tt tt
