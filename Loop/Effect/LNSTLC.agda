{-# OPTIONS --type-in-type --no-positivity-check #-}

module Loop.Effect.LNSTLC where

open import Loop

open import Data.Vec as V using ([]; _∷_)

infixr 6 _⇒_
infixl 5 _▻_
infixr 4 vs_
infixr 0 ƛ_
infixl 6 _·_
infixr 5 _::_
infixr 1 _>>>_

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

app-arg : Bool -> Type -> Type -> Type
app-arg b σ τ = if b then σ else σ ⇒ τ

fold-arg : Fin 3 -> Type -> Type
fold-arg i σ = V.lookup i (σ ⇒ σ ∷ σ ∷ nat ∷ [])

cons-arg : Bool -> Type -> Type
cons-arg b σ = if b then list σ else σ

foldr-arg : Fin 3 -> Type -> Type -> Type
foldr-arg i σ τ = V.lookup i (σ ⇒ τ ⇒ τ ∷ τ ∷ list σ ∷ [])

data Term : Effect (Con × Type) where
  Pure  : ∀ {Γ σ  } -> ⟦ σ ⟧  -> Term (Γ , σ     )  ⊥       ⊥-elim
  Var   : ∀ {Γ σ  } -> In σ Γ -> Term (Γ , σ     )  ⊥       ⊥-elim
  Lam   : ∀ {Γ σ τ} ->           Term (Γ , σ ⇒ τ )  ⊤      (λ _ -> Γ ▻ σ , τ              )
  App   : ∀ {Γ σ τ} ->           Term (Γ , τ     )  Bool   (λ b -> Γ     , app-arg b σ τ  )
  Z     : ∀ {Γ    } ->           Term (Γ , nat   )  ⊥       ⊥-elim
  S     : ∀ {Γ    } ->           Term (Γ , nat   )  ⊤      (λ _ -> Γ     , nat            )
  Fold  : ∀ {Γ σ  } ->           Term (Γ , σ     ) (Fin 3) (λ i -> Γ     , fold-arg i σ   )
  Nil   : ∀ {Γ σ  } ->           Term (Γ , list σ)  ⊥       ⊥-elim
  Cons  : ∀ {Γ σ  } ->           Term (Γ , list σ)  Bool   (λ b -> Γ     , cons-arg b σ   )
  Foldr : ∀ {Γ σ τ} ->           Term (Γ , τ     ) (Fin 3) (λ i -> Γ     , foldr-arg i σ τ)

Termᴱ′ : ∀ {Rs} Φs (Ψs : Effects Rs) Γ σ (rs₁ : Resources Rs) A (r′ : A -> _) rs₂ -> Set
Termᴱ′ Φs Ψs Γ σ rs₁ A r′ rs₂ = EffOver Φs (Term , Ψs) ((Γ , σ) , rs₁) A (λ x -> r′ x , rs₂)

Termᴱ : ∀ {Rs} Φs (Ψs : Effects Rs) Γ σ rs₁ rs₂ -> Set _
Termᴱ Φs Ψs Γ σ rs₁ rs₂ = Termᴱ′ Φs Ψs Γ σ rs₁ ⊥ ⊥-elim rs₂

Termᴱ⁺ : ∀ {Rs} Φs (Ψs : Effects Rs) σ rs₁ rs₂ -> Set _
Termᴱ⁺ Φs Ψs σ rs₁ rs₂ = ∀ {Γ} -> Termᴱ Φs Ψs Γ σ rs₁ rs₂

pure : ∀ {Φs Rs Γ σ rs} {Ψs : Effects Rs}
     -> ⟦ σ ⟧ -> Termᴱ Φs Ψs Γ σ rs rs
pure = invoke₀ ∘ Pure

var : ∀ {Φs Rs Γ σ rs} {Ψs : Effects Rs}
    -> In σ Γ -> Termᴱ Φs Ψs Γ σ rs rs
var = invoke₀ ∘ Var

ƛ_ : ∀ {Φs Rs Γ σ τ rs₁ rs₂} {Ψs : Effects Rs}
   -> Termᴱ Φs Ψs (Γ ▻ σ) τ _ rs₂ -> Termᴱ Φs Ψs Γ (σ ⇒ τ) rs₁ rs₂
ƛ b = invoke₀ Lam >> b

_·_ : ∀ {Φs Rs Γ σ τ rs₁ rs₂} {Ψs : Effects Rs}
    -> Termᴱ Φs Ψs Γ (σ ⇒ τ) _ rs₂ -> Termᴱ Φs Ψs Γ σ _ rs₂ -> Termᴱ Φs Ψs Γ τ rs₁ rs₂
f · x = invoke₀ App >>= f <∨> x

z : ∀ {Φs Rs Γ rs} {Ψs : Effects Rs}
  -> Termᴱ Φs Ψs Γ nat rs rs
z = invoke₀ Z

s : ∀ {Φs Rs Γ rs₁ rs₂} {Ψs : Effects Rs}
  -> Termᴱ Φs Ψs Γ nat _ rs₂ -> Termᴱ Φs Ψs Γ nat rs₁ rs₂
s n = invoke₀ S >>= const n

tfold : ∀ {Φs Rs Γ σ rs₁ rs₂} {Ψs : Effects Rs}
      -> Termᴱ Φs Ψs Γ (σ ⇒ σ) _   rs₂
      -> Termᴱ Φs Ψs Γ  σ      _   rs₂
      -> Termᴱ Φs Ψs Γ  nat    _   rs₂
      -> Termᴱ Φs Ψs Γ  σ      rs₁ rs₂
tfold f z n = invoke₀ Fold >>= k where
  k : (i : Fin 3) -> Termᴱ _ _ _ _ _ _
  k  zero                = f
  k (suc zero)           = z
  k (suc (suc zero))     = n
  k (suc (suc (suc ())))

nil : ∀ {Φs Rs Γ σ rs} {Ψs : Effects Rs}
    -> Termᴱ Φs Ψs Γ (list σ) rs rs
nil = invoke₀ Nil

_::_ : ∀ {Φs Rs Γ σ rs₁ rs₂} {Ψs : Effects Rs}
     -> Termᴱ Φs Ψs Γ σ _ rs₂ -> Termᴱ Φs Ψs Γ (list σ) _ rs₂ -> Termᴱ Φs Ψs Γ (list σ) rs₁ rs₂
x :: xs = invoke₀ Cons >>= x <∨> xs

tfoldr : ∀ {Φs Rs Γ σ τ rs₁ rs₂} {Ψs : Effects Rs}
       -> Termᴱ Φs Ψs Γ (σ ⇒ τ ⇒ τ) _   rs₂
       -> Termᴱ Φs Ψs Γ  τ          _   rs₂
       -> Termᴱ Φs Ψs Γ (list σ)    _   rs₂
       -> Termᴱ Φs Ψs Γ  τ          rs₁ rs₂
tfoldr f z n = invoke₀ Foldr >>= k where
  k : (i : Fin 3) -> Termᴱ _ _ _ _ _ _
  k  zero                = f
  k (suc zero)           = z
  k (suc (suc zero))     = n
  k (suc (suc (suc ())))

mutual
  data Forcer : HigherEffect where
    Seq   : ∀ {Rs Γ σ τ rs₁ A r₁′ rs₂ rs₃} {Ψs : Effects Rs}
          -> TermForceᴱ′ Ψs Γ σ rs₁ A r₁′ rs₂
          -> TermForceᴱ  Ψs Γ τ rs₂       rs₃
          -> Forcer (Term , Ψs) ((Γ , τ) , rs₁) ⊥ ⊥-elim
    Force : ∀ {Rs Γ σ rs₁ rs₂} {Ψs : Effects Rs}
          -> TermForceᴱ Ψs Γ σ rs₁ rs₂
          -> Forcer (Term , Ψs) ((Γ , σ) , rs₁) ⟦ σ ⟧ (λ _ -> (Γ , σ) , rs₂)

  TermForceᴱ′ : ∀ {Rs} (Ψs : Effects Rs) Γ σ rs₁ A (r′ : A -> _) rs₂ -> Set
  TermForceᴱ′ Ψs = Termᴱ′ (Forcer ∷ []) Ψs

  TermForceᴱ : ∀ {Rs} (Ψs : Effects Rs) Γ σ rs₁ rs₂ -> Set
  TermForceᴱ Ψs Γ σ rs₁ rs₂ = TermForceᴱ′ Ψs Γ σ rs₁ ⊥ ⊥-elim rs₂

TermForceᴱ⁺ : ∀ {Rs} (Ψs : Effects Rs) σ rs₁ rs₂ -> Set
TermForceᴱ⁺ Ψs σ rs₁ rs₂ = ∀ {Γ} -> TermForceᴱ Ψs Γ σ rs₁ rs₂

force : ∀ {Rs Γ σ rs₁ rs₂} {Ψs : Effects Rs}
      -> TermForceᴱ Ψs Γ σ rs₁ rs₂ -> TermForceᴱ′ Ψs Γ σ rs₁ ⟦ σ ⟧ _ rs₂
force t = call (wrapUnionᵒᵉ (inj₂ (inj₁ (Force t)))) return

_>>>_ : ∀ {Rs Γ σ τ rs₁ A r₁′ rs₂ rs₃} {Ψs : Effects Rs}
      -> TermForceᴱ′ Ψs Γ σ rs₁ A r₁′ rs₂
      -> TermForceᴱ  Ψs Γ τ rs₂       rs₃
      -> TermForceᴱ  Ψs Γ τ rs₁       rs₃
t₁ >>> t₂ = call (wrapUnionᵒᵉ (inj₂ (inj₁ (Seq t₁ t₂)))) λ()



tmap : ∀ {Φs Rs σ τ rs} {Ψs : Effects Rs}
     -> Termᴱ⁺ Φs Ψs ((σ ⇒ τ) ⇒ list σ ⇒ list τ) rs rs
tmap = ƛ ƛ tfoldr (ƛ ƛ var (vs vs vs vz) · var (vs vz) :: var vz) nil (var vz)

open import Loop.Effect.Writer

tell-inc : TermForceᴱ⁺ (Writer , tt) (list nat ⇒ list nat) (ℕ , tt) (ℕ , tt)
tell-inc = tmap · (ƛ force (var vz) >>= tell >>> s (var vz))
