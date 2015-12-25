module Dep where

open import Prelude
open import Map
open import Core

infixl 1 _↓>>=_ _↑>>=_
infixl 6 _<$>ᵈ_

data _↓>>=_ {m n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
            {Rs : Resources ρs} {B : Set β} {Rs′ : B -> Resources ρs}
            {is : Fin n ^ m} (b : Eff Ψs Rs B Rs′ is) (C : B -> Set γ) : Set (β ⊔ γ) where
  call : (∀ y -> C y) -> b ↓>>= C

Call : ∀ {m n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
         {Rs : Resources ρs} {B : Set β} {Rs′ : B -> Resources ρs}
         {is : Fin n ^ m} {b : Eff Ψs Rs B Rs′ is}
     -> (B -> Set γ) -> Set (β ⊔ γ)
Call {b = b} C = b ↓>>= C

⟨_⟩_ : ∀ {m n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Rs : Resources ρs}
         {B : Set β} {Rs′ : B -> Resources ρs} {is : Fin n ^ m}
     -> (Ψs : Effects ρs αεs) {b : Eff Ψs Rs B Rs′ is} -> (B -> Set γ) -> Set (β ⊔ γ)
⟨_⟩_ Ψs {b} C = b ↓>>= C

_↑>>=_ : ∀ {m n β γ} {ρs : Level ^ n} {αεs : Level ²^ n}
           {Ψs : Effects ρs αεs} {Rs : Resources ρs} {B : Set β}
           {Rs′ : B -> Resources ρs} {is : Fin n ^ m} {C : B -> Set γ}
       -> (b : Eff Ψs Rs B Rs′ is) -> (∀ y -> C y) -> b ↓>>= C
b ↑>>= g = call g

execᵈ : ∀ {m n β γ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
          {Rs : Resources ρs} {B : Set β} {Rs′ : B -> Resources ρs}
          {is : Fin n ^ m} {b : Eff Ψs Rs B Rs′ is} {C : B -> Set γ}
      -> (run : Eff Ψs Rs B Rs′ is -> B) -> b ↓>>= C -> C (run b)
execᵈ run (call g) = g _

_<$>ᵈ_ : ∀ {m n β γ δ} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
          {Rs : Resources ρs} {B : Set β} {Rs′ : B -> Resources ρs}
          {is : Fin n ^ m} {b : Eff Ψs Rs B Rs′ is} {C : B -> Set γ} {D : B -> Set δ}
       -> (∀ {y} -> C y -> D y) -> b ↓>>= C -> b ↓>>= D
h <$>ᵈ call g = call (h ∘ g)
