{-# OPTIONS --type-in-type --no-positivity-check #-}

module Loop.Effect.ILNSTLC where

open import Prelude
open import Loop.Indexed

open import Data.Vec as V using ([]; _∷_)

infixr 6 _⇒_
infixl 5 _▻_
infixr 4 vs_
infixr 0 ƛ_
infixl 6 _·_
-- infixr 5 _::_
-- infixr 1 _>>>_

data Type : Set where
  nat  : Type
  list : Type -> Type
  _⇒_  : Type -> Type -> Type

⟦_⟧ : Type -> Set
⟦ nat    ⟧ = ℕ
⟦ list σ ⟧ = List ⟦ σ ⟧
⟦ σ ⇒ τ  ⟧ = ⟦ σ ⟧ -> ⟦ τ ⟧

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data In σ : Con -> Set where
  vz  : ∀ {Γ}   -> In σ (Γ ▻ σ)
  vs_ : ∀ {Γ τ} -> In σ  Γ      -> In σ (Γ ▻ τ)

data Env : Con -> Set where
  ∅   : Env ε
  _▷_ : ∀ {Γ σ} -> Env Γ -> ⟦ σ ⟧ -> Env (Γ ▻ σ)

lookupEnv : ∀ {Γ σ} -> In σ Γ -> Env Γ -> ⟦ σ ⟧
lookupEnv  vz    (ρ ▷ x) = x
lookupEnv (vs v) (ρ ▷ x) = lookupEnv v ρ

mutual
  Term : ∀ {Rs} -> Effects Rs -> Resources Rs -> Con -> Type -> Resources Rs -> Set
  Term  Ψs rs₁ Γ σ rs₂ = HTerm (Γ , σ) Ψs rs₁ ⊤ (const rs₂)

  Termᴱ : ∀ {Rs} -> Effects Rs -> Resources Rs -> Con -> Type -> Resources Rs -> Set
  Termᴱ Ψs rs₁ Γ σ rs₂ = EffOver (HTerm , tt) ((Γ , σ) , tt) Ψs rs₁ ⊤ (const rs₂)

  data HTerm : IHigherEffect (Con × Type) where
    Pure  : ∀ {Rs rs Γ σ} {Ψs : Effects Rs} -> ⟦ σ ⟧  -> Term Ψs rs Γ σ rs
    Var   : ∀ {Rs rs Γ σ} {Ψs : Effects Rs} -> In σ Γ -> Term Ψs rs Γ σ rs
    Lam   : ∀ {Rs rs₁ rs₂     Γ σ τ} {Ψs : Effects Rs}
          -> Termᴱ Ψs rs₁ (Γ ▻ σ)  τ          rs₂
          -> Term  Ψs rs₁  Γ      (σ ⇒ τ)     rs₂
    App   :                                       ∀ {Rs rs₁ rs₂ rs₃ Γ σ τ} {Ψs : Effects Rs}
          -> Termᴱ Ψs rs₁  Γ      (σ ⇒ τ)     rs₂
          -> Termᴱ Ψs rs₂  Γ       σ          rs₃
          -> Term  Ψs rs₁  Γ       τ          rs₃
    Z     :                                       ∀ {Rs rs          Γ    } {Ψs : Effects Rs}
          -> Term  Ψs rs   Γ       nat        rs
    S     :                                       ∀ {Rs rs₁ rs₂     Γ    } {Ψs : Effects Rs}
          -> Termᴱ Ψs rs₁  Γ       nat        rs₂
          -> Term  Ψs rs₁  Γ       nat        rs₂
    Fold  :                                       ∀ {Rs rs₁ rs₂ rs₃ Γ σ  } {Ψs : Effects Rs}
          -> Termᴱ Ψs rs₃  Γ      (σ ⇒ σ)     rs₃
          -> Termᴱ Ψs rs₂  Γ       σ          rs₃
          -> Termᴱ Ψs rs₁  Γ       nat        rs₂
          -> Term  Ψs rs₁  Γ       σ          rs₃
    Nil   :                                       ∀ {Rs rs          Γ σ  } {Ψs : Effects Rs}
          -> Term  Ψs rs   Γ      (list σ)    rs
    Cons  :                                       ∀ {Rs rs₁ rs₂ rs₃ Γ σ  } {Ψs : Effects Rs}
          -> Termᴱ Ψs rs₁  Γ       σ          rs₂
          -> Termᴱ Ψs rs₂  Γ      (list σ)    rs₃
          -> Term  Ψs rs₁  Γ      (list σ)    rs₃
    Foldr :                                       ∀ {Rs rs₁ rs₂ rs₃ Γ σ τ} {Ψs : Effects Rs}
          -> Termᴱ Ψs rs₃  Γ      (σ ⇒ τ ⇒ τ) rs₃
          -> Termᴱ Ψs rs₂  Γ       τ          rs₃
          -> Termᴱ Ψs rs₁  Γ      (list σ)    rs₂
          -> Term  Ψs rs₁  Γ       τ          rs₃

var : ∀ {Rs rs Γ σ} {Ψs : Effects Rs} -> In σ Γ -> Termᴱ Ψs rs Γ σ rs
var v = hinvoke₀ (Var v)

ƛ_ : ∀ {Rs rs₁ rs₂ Γ σ τ} {Ψs : Effects Rs}
   -> Termᴱ Ψs rs₁ (Γ ▻ σ) τ rs₂ -> Termᴱ Ψs rs₁ Γ (σ ⇒ τ) rs₂
ƛ b = hinvoke₀ (Lam b)

_·_ : ∀ {Rs rs₁ rs₂ rs₃ Γ σ τ} {Ψs : Effects Rs}
    -> Termᴱ Ψs rs₁ Γ (σ ⇒ τ) rs₂ -> Termᴱ Ψs rs₂ Γ σ rs₃ -> Termᴱ Ψs rs₁ Γ τ rs₃
f · x = hinvoke₀ (App f x)

-- ...
