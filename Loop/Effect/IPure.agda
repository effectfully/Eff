{-# OPTIONS --type-in-type --no-positivity-check #-}

module Loop.Effect.IPure where

open import Prelude
open import Loop.Indexed

mutual
  Pure : ∀ {Rs} -> Effects Rs -> Resources Rs -> Set -> Resources Rs -> Set
  Pure Ψs rs₁ A rs₂ = HPure Ψs rs₁ A (const rs₂)

  Pureᴱ : ∀ {Rs} -> Effects Rs -> Resources Rs -> Set -> Resources Rs -> Set
  Pureᴱ Ψs rs₁ A rs₂ = EffOver (toI HPure , tt) (tt , tt) Ψs rs₁ A (const rs₂)

  data HPure : HigherEffect where
    Lam : ∀ {Rs rs₁ A rs₂} {B : A -> Set} {Ψs : Effects Rs}
        -> (∀ x -> Pureᴱ Ψs rs₁ (B x) rs₂) -> Pure Ψs rs₁ (∀ x -> B x) rs₂

lam : ∀ {Rs rs₁ A rs₂} {B : A -> Set} {Ψs : Effects Rs}
    -> (∀ x -> Pureᴱ Ψs rs₁ (B x) rs₂) -> Pureᴱ Ψs rs₁ (∀ x -> B x) rs₂
lam = hinvoke₀ ∘ Lam
