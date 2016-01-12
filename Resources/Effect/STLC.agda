module Resources.Effect.STLC where

open import Resources

infixr 6 _⇒_
infixl 5 _▻_

data Type : Set where
  ι   : Type
  _⇒_ : Type -> Type -> Type

data Con : Set where
  ε   : Con
  _▻_ : Con -> Type -> Con

data In σ : Con -> Set where
  vz : ∀ {Γ}   -> In σ (Γ ▻ σ)
  vs : ∀ {Γ τ} -> In σ  Γ      -> In σ (Γ ▻ τ)

Sig = Con × Type

data Term : Effect Sig lzero lzero where
  Var : ∀ {Γ σ}   -> In σ Γ -> Term (Γ , σ)     Sig   id
  Lam : ∀ {Γ σ τ} ->           Term (Γ , σ ⇒ τ) ⊤    (λ _ -> Γ ▻ σ ,  τ)
  App : ∀ {Γ σ τ} ->           Term (Γ , τ)     Bool (λ b -> Γ     , (if b then σ else σ ⇒ τ))

var : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
        {Ψs : Effects Rs αψs} {Γ σ rs} {{p : Term , Γ , σ ∈ Ψs , rs}}
    -> In σ Γ -> Eff Ψs Sig rs _
var = invoke′ ∘ Var

lam : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
        {Ψs : Effects Rs αψs} {Γ σ τ rs} {{p : Term , Γ , σ ⇒ τ ∈ Ψs , rs}}
    -> Eff Ψs ⊤ rs _
lam = invoke′ Lam

app : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
        {Ψs : Effects Rs αψs} {Γ σ τ rs rs′} {{p : Term , Γ , τ ∈ Ψs , rs}}
    -> Eff Ψs Sig _ rs′ -> Eff Ψs Sig _ rs′ -> Eff Ψs Sig rs rs′
app {σ = σ} {{p}} f x = invoke′ {{p}} (App {σ = σ}) >>= f <∨> x



Termᴱ : Con -> Type -> Set₁
Termᴱ Γ σ = Eff (Term , tt) Sig ((Γ , σ) , tt) (_, tt)

A : ∀ {σ τ} -> Termᴱ ε ((σ ⇒ τ) ⇒ σ ⇒ τ)
A = lam >> lam >> app (var (vs vz)) (var vz)
