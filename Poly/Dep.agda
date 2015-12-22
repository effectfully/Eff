module Dep where

open import Prelude
open import Map
open import Core

infixl 1 _↓>>=_ _↑>>=_
infixl 6 _<$>ᵗ_

data _↓>>=_ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs} {C : Set γ} {is : Fin n ^ m}
            (c : Eff Fs C is) (D : C -> Set δ) : Set (γ ⊔ δ) where
  call : (∀ z -> D z) -> c ↓>>= D

Call : ∀ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs}
         {C : Set γ} {is : Fin n ^ m} {c : Eff Fs C is}
     -> (C -> Set δ) -> Set (γ ⊔ δ)
Call {c = c} D = c ↓>>= D

⟨_⟩_ : ∀ {m n γ δ} {αβs : Levels n} {C : Set γ} {is : Fin n ^ m}
     -> (Fs : Effects αβs) {c : Eff Fs C is} -> (C -> Set δ) -> Set (γ ⊔ δ)
⟨_⟩_ Fs {c} D = c ↓>>= D

_↑>>=_ : ∀ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs}
           {C : Set γ} {is : Fin n ^ m} {D : C -> Set δ}
       -> (c : Eff Fs C is) -> (∀ z -> D z) -> c ↓>>= D
c ↑>>= h = call h

execᵗ : ∀ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs} {C : Set γ}
          {is : Fin n ^ m} {c : Eff Fs C is} {D : C -> Set δ}
      -> (run : Eff Fs C is -> C) -> c ↓>>= D -> D (run c)
execᵗ run (call h) = h _

_<$>ᵗ_ : ∀ {m n γ δ ε} {αβs : Levels n} {Fs : Effects αβs} {C : Set γ}
           {is : Fin n ^ m} {c : Eff Fs C is} {D : C -> Set δ} {E : C -> Set ε}
       -> (∀ {z} -> D z -> E z) -> c ↓>>= D -> c ↓>>= E
h₂ <$>ᵗ call h₁ = call (h₂ ∘ h₁)

_>>=ᵗ_ : ∀ {m n γ δ ε} {αβs : Levels n} {Fs : Effects αβs} {C : Set γ}
           {is : Fin n ^ m} {c : Eff Fs C is} {D : C -> Set δ} {E : ∀ {z} -> D z -> Set ε}
       -> (d : c ↓>>= D)
       -> (∀ {z} -> (w : D z) -> E w)
       -> c ↓>>= λ z -> case d of λ{ (call h₁) -> E (h₁ z) }
call h₁ >>=ᵗ h₂ = call (h₂ ∘ h₁)
