module Resources.Dep where

open import Prelude
open import Map
open import Resources.Core

infixl 1 _↓>>=_ _↑>>=_
infixl 6 _<$>ᵈ_

data _↓>>=_ {n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
            {B : Set β}  {Rs : Resources ρs} {Rs′ : B -> Resources ρs}
            (b : Eff Ψs B Rs Rs′) (C : B -> Set γ) : Set (β ⊔ γ) where
  call : (∀ y -> C y) -> b ↓>>= C

Call : ∀ {n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
         {B : Set β} {Rs : Resources ρs} {Rs′ : B -> Resources ρs} {b : Eff Ψs B Rs Rs′}
     -> (B -> Set γ) -> Set (β ⊔ γ)
Call {b = b} C = b ↓>>= C

⟨_⟩_ : ∀ {n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {B : Set β}
         {Rs : Resources ρs} {Rs′ : B -> Resources ρs}
     -> (Ψs : Effects ρs αεs) {b : Eff Ψs B Rs Rs′} -> (B -> Set γ) -> Set (β ⊔ γ)
⟨_⟩_ Ψs {b} C = b ↓>>= C

_↑>>=_ : ∀ {n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
           {B : Set β} {Rs : Resources ρs} {Rs′ : B -> Resources ρs} {C : B -> Set γ}
       -> (b : Eff Ψs B Rs Rs′) -> (∀ y -> C y) -> b ↓>>= C
b ↑>>= g = call g

execᵈ : ∀ {n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs} {B : Set β}
          {Rs : Resources ρs} {Rs′ : B -> Resources ρs} {b : Eff Ψs B Rs Rs′} {C : B -> Set γ}
      -> (run : Eff Ψs B Rs Rs′ -> B) -> b ↓>>= C -> C (run b)
execᵈ run (call g) = g _

_<$>ᵈ_ : ∀ {n β γ δ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
           {B : Set β} {Rs : Resources ρs} {Rs′ : B -> Resources ρs}
           {b : Eff Ψs B Rs Rs′} {C : B -> Set γ} {D : B -> Set δ}
       -> (∀ {y} -> C y -> D y) -> b ↓>>= C -> b ↓>>= D
h <$>ᵈ call g = call (h ∘ g)

-- _↓>>=_ is a "higher-kinded applicative functor".
_<*>ᵈ_ : ∀ {n β γ δ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
           {B : Set β} {Rs : Resources ρs} {Rs′ : B -> Resources ρs}
           {b : Eff Ψs B Rs Rs′} {C : B -> Set γ} {D : B -> Set δ}
       -> b ↓>>= (λ y -> C y -> D y) -> b ↓>>= C -> b ↓>>= D
call h <*>ᵈ call g = call (h ˢ g)
