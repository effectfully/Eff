{-# OPTIONS --type-in-type --no-positivity-check #-}

module Loop.Effect.Break where

open import Loop

mutual
  Break : ∀ {Rs} -> Effects Rs -> Resources Rs -> Set -> Resources Rs -> Set
  Break Ψs rs₁ A rs₂ = HBreak Ψs rs₁ A (const rs₂)

  Breakᴱ : ∀ {Rs} -> Effects Rs -> Resources Rs -> Set -> Resources Rs -> Set
  Breakᴱ Ψs rs₁ A rs₂ = EffOver (HBreak ∷ []) Ψs rs₁ A (const rs₂)

  -- The name due to the fact that this effect breaks purity.
  -- E.g. in (lam λ x -> get >>= λ f -> e) `f' has a pure type and impure behaviour.
  data HBreak : HigherEffect where
    Lam : ∀ {Rs rs₁ A rs₂} {B : A -> Set} {Ψs : Effects Rs}
        -> (∀ x -> Breakᴱ Ψs rs₁ (B x) rs₂) -> Break Ψs rs₁ (∀ x -> B x) rs₂

lam : ∀ {Rs rs₁ A rs₂} {B : A -> Set} {Ψs : Effects Rs}
    -> (∀ x -> Breakᴱ Ψs rs₁ (B x) rs₂) -> Breakᴱ Ψs rs₁ (∀ x -> B x) rs₂
lam = hinvoke ∘ Lam

open import Loop.Effect.State

private
  test₁ : Breakᴱ (State , tt) (⊤ , tt) ((ℕ -> ℕ) -> ℕ -> ℕ) (ℕ , tt)
  test₁ = lam λ f -> zap ⊤ (f 0) >> lam λ n -> put n >> return (f n)

  test₂ : Breakᴱ (State , tt) (⊤ , tt) ℕ (⊤ , tt)
  test₂ = test₁ >>= λ f -> zap ℕ tt >> return (f id 0)
