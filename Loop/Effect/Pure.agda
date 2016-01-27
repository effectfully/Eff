{-# OPTIONS --type-in-type --no-positivity-check #-}

module Loop.Effect.Pure where

open import Loop

mutual
  data Pure Φs : HigherEffect where
    Lam : ∀ {Rs A rs₁ rs₂} {B : A -> Set} {Ψs : Effects Rs}
        -> (∀ x -> EffPure Φs Ψs rs₁ (B x) (const rs₂))
        -> Pure Φs Ψs rs₁ (∀ x -> B x) (const rs₂)

  EffPure : HigherEffects -> HigherEffect
  EffPure Φs = EffOver (Pure Φs ∷ Φs)

lam : ∀ {Φs Rs A rs₁ rs₂} {B : A -> Set} {Ψs : Effects Rs}
    -> (∀ x -> EffPure Φs Ψs rs₁ (B x) (const rs₂))
    -> EffPure Φs Ψs rs₁ (∀ x -> B x) (const rs₂)
lam = hinvoke ∘ Lam

open import Loop.Effect.State

test : EffPure [] (State , tt) (⊤ , tt) ((ℕ -> ℕ) -> ℕ -> ℕ) (λ _ -> ℕ , tt)
test = lam λ f -> zap ⊤ 0 >> lam λ n -> put n >> return (f n)

test₂ : EffPure [] (State , tt) (⊤ , tt) ℕ (λ _ -> ⊤ , tt)
test₂ = test >>= λ f -> zap ℕ tt >> return (f id 0)
