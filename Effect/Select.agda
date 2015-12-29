module Effect.Select where

open import Prelude
open import Map
open import Core
open import Membership
open import Dep

data Select {α} (A : Set α) : Effectful α α α where
  MZero : Select A A    (const A)
  MPlus : Select A Bool (const A)

⟨⟩ : ∀ {n α} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
       {A : Set α} {Rs : Resources ρs} {{p : Select , A ∈ Ψs , Rs}}
   -> Eff Ψs A Rs _
⟨⟩ = invoke MZero

_<>_ : ∀ {n ρ β} {ρs : Level ^ n} {αεs : Level ²^ n}
         {Ψs : Effects ρs αεs} {B : Set β} {R : Resource ρ}
         {Rs : Resources ρs} {Rs′ : B -> Resources ρs} {{p : Select , R ∈ Ψs , Rs}}
     -> Eff Ψs B Rs Rs′ -> Eff Ψs B Rs Rs′ -> Eff Ψs B Rs Rs′
m₁ <> m₂ = invoke MPlus >>= m₁ <∨> m₂
