module Resources.Effect.STLC where

open import Resources

infixr 6 _⇒_
infixl 5 _▻_
infixl 6 _·_

data Type : Set where
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

_·_ : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
        {Ψs : Effects Rs αψs} {Γ σ τ rs rs′} {{p : Term , Γ , τ ∈ Ψs , rs}}
    -> Eff Ψs Sig _ rs′ -> Eff Ψs Sig _ rs′ -> Eff Ψs Sig rs rs′
_·_ {σ = σ} {{p}} f x = invoke′ {{p}} (App {σ = σ}) >>= f <∨> x



Termᵢ : ∀ {s} -> Set
Termᵢ {s} = Term s Sig id

Termᴱ : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
      -> Effects Rs αψs -> Con -> Type -> Resources Rs -> Resources Rs -> Set _
Termᴱ Ψs Γ σ rs₁ rs₂ = Eff {Rs = Sig , _} (Term , Ψs) Sig ((Γ , σ) , rs₁) (_, rs₂)

A : ∀ {σ τ} -> Termᴱ tt ε ((σ ⇒ τ) ⇒ σ ⇒ τ) tt tt
A = lam >> lam >> var (vs vz) · var vz

open import Resources.Effect.State

test : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
         {Ψs : Effects Rs αψs} {rs : Resources Rs} {A : Set α} {Γ σ τ rs}
         {{p₁ : State , Termᵢ ∈ Ψs , rs}} {{p₂ : State , ℕ ∈ Ψs , rs}}
     -> Termᴱ Ψs Γ ((σ ⇒ τ) ⇒ τ) rs _
test = lam >> shift (put 0) >> var vz · embed get
