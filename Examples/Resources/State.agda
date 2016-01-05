module Examples.Resources.State where

open import Resources
open import Resources.Effect.State

import Data.Vec as V

eff₁ : Eff (State , tt) ℕ (ℕ , tt) (λ n -> V.Vec Bool n , tt)
eff₁ = get >>= λ n -> zap ℕ (V.replicate true) >> return n

eff₂ : ∀ {α} -> Eff (State , State , tt) ℕ (ℕ , Set α , tt) (λ _ -> ℕ , Set α , tt)
eff₂ = get >>= λ n -> put n >> return (suc n)

-- 3 , true ∷ true ∷ true ∷ []
test₁ : ∃ (V.Vec Bool)
test₁ = runEff $ execState 3 eff₁

-- 4 , 3
test₂ : ℕ × ℕ
test₂ = proj₁ $ runEff $ execState ℕ $ execState 3 eff₂
