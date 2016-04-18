{-# OPTIONS --type-in-type --no-positivity-check #-}

module Loop.Effect.Vars where

open import Loop
open import Loop.Effect.Break

open import Data.List.Any
open Membership-≡ renaming (_∈_ to _∈ₗ_)

pattern phere = here refl

hlookup : ∀ {A Γ} -> A ∈ₗ Γ -> HList Γ -> A
hlookup  phere    (x , xs) = x
hlookup (there v) (x , xs) = hlookup v xs

mutual
  Term  : ∀ {Rs} -> Effects Rs -> Resources Rs -> List Set -> Set -> Resources Rs -> Set
  Term  Ψs rs₁ Γ A rs₂ = HTerm Γ Ψs rs₁ A (const rs₂)

  Termᴱ : ∀ {Rs} -> Effects Rs -> Resources Rs -> List Set -> Set -> Resources Rs -> Set
  Termᴱ Ψs rs₁ Γ A rs₂ = EffOver (HTerm Γ ∷ []) Ψs rs₁ A (const rs₂)

  data HTerm Γ : HigherEffect where
    Var : ∀ {Rs rs A} {Ψs : Effects Rs} -> A ∈ₗ Γ -> Term Ψs rs Γ A rs
    App : ∀ {Rs rs₁ rs₂ rs₃ A B} {Ψs : Effects Rs}
        -> Termᴱ Ψs rs₁ Γ (A -> B) rs₂ -> Termᴱ Ψs rs₂ Γ A rs₃ -> Term Ψs rs₁ Γ B rs₃

var : ∀ {Rs rs Γ A} {Ψs : Effects Rs} -> A ∈ₗ Γ -> Termᴱ Ψs rs Γ A rs
var v = hinvoke (Var v)

_·_ : ∀ {Rs rs₁ rs₂ rs₃ Γ A B} {Ψs : Effects Rs}
    -> Termᴱ Ψs rs₁ Γ (A -> B) rs₂ -> Termᴱ Ψs rs₂ Γ A rs₃ -> Termᴱ Ψs rs₁ Γ B rs₃
f · x = hinvoke (App f x)

evalTermᴱ : ∀ {Rs rs₁ rs₂ Γ A} {Ψs : Effects Rs}
          -> HList Γ -> Termᴱ Ψs rs₁ Γ A rs₂ -> Eff Ψs rs₁ A (const rs₂)
evalTermᴱ ρ (return x)                            = return x
evalTermᴱ ρ (call (hereʰᵉ   a                ) k) = call (hereʰᵉ a) (λ x -> evalTermᴱ ρ (k x))
evalTermᴱ ρ (call (thereʰᵉ (thereʰᵉ ()      )) k)
evalTermᴱ ρ (call (thereʰᵉ (hereʰᵉ (Var v  ))) k) = evalTermᴱ ρ (k (hlookup v ρ))
evalTermᴱ ρ (call (thereʰᵉ (hereʰᵉ (App f x))) k) =
  evalTermᴱ ρ f <*> evalTermᴱ ρ x >>= λ fx -> evalTermᴱ ρ (k fx)



open import Loop.Effect.State
open import Data.String.Base hiding (show)
open import Data.Nat.Show

private
  test : Termᴱ (State , tt) (⊤ , tt) ((ℕ -> String) ∷ ℕ ∷ []) String (ℕ , tt)
  test = var (there phere) >>= zap ⊤ >> var phere · get

  -- "2" , 2
  test-test : String × ℕ
  test-test = runEff $ execState tt $ evalTermᴱ (show , 2 , tt) test
