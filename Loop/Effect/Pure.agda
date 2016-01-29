{-# OPTIONS --type-in-type --no-positivity-check #-}

module Loop.Effect.Pure where

open import Loop

mutual
  Pure : ∀ {Rs} -> Effects Rs -> Resources Rs -> Set -> Resources Rs -> Set
  Pure Ψs rs₁ A rs₂ = HPure Ψs rs₁ A (const rs₂)

  Pureᴱ : ∀ {Rs} -> Effects Rs -> Resources Rs -> Set -> Resources Rs -> Set
  Pureᴱ Ψs rs₁ A rs₂ = EffOver (HPure ∷ []) Ψs rs₁ A (const rs₂)

  data HPure : HigherEffect where
    Lam : ∀ {Rs rs₁ A rs₂} {B : A -> Set} {Ψs : Effects Rs}
        -> (∀ x -> Pureᴱ Ψs rs₁ (B x) rs₂) -> Pure Ψs rs₁ (∀ x -> B x) rs₂

lam : ∀ {Rs rs₁ A rs₂} {B : A -> Set} {Ψs : Effects Rs}
    -> (∀ x -> Pureᴱ Ψs rs₁ (B x) rs₂) -> Pureᴱ Ψs rs₁ (∀ x -> B x) rs₂
lam = hinvoke ∘ Lam

open import Loop.Effect.State

private
  test₁ : Pureᴱ (State , tt) (⊤ , tt) ((ℕ -> ℕ) -> ℕ -> ℕ) (ℕ , tt)
  test₁ = lam λ f -> zap ⊤ 0 >> lam λ n -> put n >> return (f n)

  test₂ : Pureᴱ (State , tt) (⊤ , tt) ℕ (⊤ , tt)
  test₂ = test₁ >>= λ f -> zap ℕ tt >> return (f id 0)
