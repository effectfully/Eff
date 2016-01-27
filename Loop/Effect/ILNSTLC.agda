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
infixr 5 _::_

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

-- `rs₂' should be dependent actually.
mutual
  Term : ∀ {Rs} -> Effects Rs -> Resources Rs -> Con -> Type -> Resources Rs -> Set
  Term  Ψs rs₁ Γ σ rs₂ = HTerm (Γ , σ) Ψs rs₁ ⟦ σ ⟧ (const rs₂)

  Termᴱ : ∀ {Rs} -> Effects Rs -> Resources Rs -> Con -> Type -> Resources Rs -> Set
  Termᴱ Ψs rs₁ Γ σ rs₂ = EffOver (HTerm , tt) ((Γ , σ) , tt) Ψs rs₁ ⟦ σ ⟧ (const rs₂)

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

pure : ∀ {Rs rs Γ σ} {Ψs : Effects Rs} -> ⟦ σ ⟧ -> Termᴱ Ψs rs Γ σ rs
pure = hinvoke₀ ∘ Pure

var : ∀ {Rs rs Γ σ} {Ψs : Effects Rs} -> In σ Γ -> Termᴱ Ψs rs Γ σ rs
var = hinvoke₀ ∘ Var

ƛ_ : ∀ {Rs rs₁ rs₂ Γ σ τ} {Ψs : Effects Rs}
   -> Termᴱ Ψs rs₁ (Γ ▻ σ) τ rs₂ -> Termᴱ Ψs rs₁ Γ (σ ⇒ τ) rs₂
ƛ b = hinvoke₀ (Lam b)

_·_ : ∀ {Rs rs₁ rs₂ rs₃ Γ σ τ} {Ψs : Effects Rs}
    -> Termᴱ Ψs rs₁ Γ (σ ⇒ τ) rs₂ -> Termᴱ Ψs rs₂ Γ σ rs₃ -> Termᴱ Ψs rs₁ Γ τ rs₃
f · x = hinvoke₀ (App f x)

z : ∀ {Rs rs Γ} {Ψs : Effects Rs} -> Termᴱ Ψs rs Γ nat rs
z = hinvoke₀ Z

s : ∀ {Rs rs₁ rs₂ Γ} {Ψs : Effects Rs} -> Termᴱ Ψs rs₁ Γ nat rs₂ -> Termᴱ Ψs rs₁ Γ nat rs₂
s n = hinvoke₀ (S n)

tfold : ∀ {Rs rs₁ rs₂ rs₃ Γ σ} {Ψs : Effects Rs}
      -> Termᴱ Ψs rs₃ Γ (σ ⇒ σ) rs₃
      -> Termᴱ Ψs rs₂ Γ  σ      rs₃
      -> Termᴱ Ψs rs₁ Γ  nat    rs₂
      -> Termᴱ Ψs rs₁ Γ  σ      rs₃
tfold f z n = hinvoke₀ (Fold f z n)

nil : ∀ {Rs rs Γ σ} {Ψs : Effects Rs} -> Termᴱ Ψs rs Γ (list σ) rs
nil = hinvoke₀ Nil

_::_ : ∀ {Rs rs₁ rs₂ rs₃ Γ σ} {Ψs : Effects Rs}
     -> Termᴱ Ψs rs₁ Γ σ rs₂ -> Termᴱ Ψs rs₂ Γ (list σ) rs₃ -> Termᴱ Ψs rs₁ Γ (list σ) rs₃
x :: xs = hinvoke₀ (Cons x xs)

tfoldr : ∀ {Rs rs₁ rs₂ rs₃ Γ σ τ} {Ψs : Effects Rs}
       -> Termᴱ Ψs rs₃  Γ (σ ⇒ τ ⇒ τ) rs₃
       -> Termᴱ Ψs rs₂  Γ  τ          rs₃
       -> Termᴱ Ψs rs₁  Γ (list σ)    rs₂
       -> Termᴱ Ψs rs₁  Γ  τ          rs₃
tfoldr f z xs = hinvoke₀ (Foldr f z xs)

open import Loop.Effect.IState

-- This is awesome.
test : Termᴱ (State , tt) (⊤ , tt) ε ((nat ⇒ nat) ⇒ nat ⇒ nat) (ℕ , tt)
test = ƛ ƛ var vz >>= zap ⊤ >> var (vs vz) · get
