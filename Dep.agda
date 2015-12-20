module Eff.Dep where

open import Eff.Prelude
open import Eff.Map
open import Eff.Core

infixl 1 _>>=ᵀ_
infixl 6 _<$>ᵗ_

data _>>=ᵀ_ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs} {C : Set γ} {is : Fin n ^ m}
            (c : Eff Fs C is) (D : C -> Set δ) : Set (γ ⊔ δ) where
  call : (∀ z -> D z) -> c >>=ᵀ D

Call : ∀ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs}
         {C : Set γ} {is : Fin n ^ m} {c : Eff Fs C is}
     -> (C -> Set δ) -> Set (γ ⊔ δ)
Call {c = c} D = c >>=ᵀ D

⟨_⟩_ : ∀ {m n γ δ} {αβs : Levels n} {C : Set γ} {is : Fin n ^ m}
     -> (Fs : Effects αβs) {c : Eff Fs C is} -> (C -> Set δ) -> Set (γ ⊔ δ)
⟨_⟩_ Fs {c} D = c >>=ᵀ D

_>>=ᵗ_ : ∀ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs}
           {C : Set γ} {is : Fin n ^ m} {D : C -> Set δ}
       -> (c : Eff Fs C is) -> (∀ z -> D z) -> c >>=ᵀ D
c >>=ᵗ h = call h

execᵗ : ∀ {m n γ δ} {αβs : Levels n} {Fs : Effects αβs} {C : Set γ}
          {is : Fin n ^ m} {c : Eff Fs C is} {D : C -> Set δ}
      -> (run : Eff Fs C is -> C) -> c >>=ᵀ D -> D (run c)
execᵗ run (call h) = h _

_<$>ᵗ_ : ∀ {m n γ δ ε} {αβs : Levels n} {Fs : Effects αβs} {C : Set γ}
          {is : Fin n ^ m} {c : Eff Fs C is} {D : C -> Set δ} {E : C -> Set ε}
       -> (∀ {z} -> D z -> E z) -> c >>=ᵀ D -> c >>=ᵀ E
h₂ <$>ᵗ call h₁ = call (h₂ ∘ h₁)
