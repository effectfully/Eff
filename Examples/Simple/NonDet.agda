module Examples.Simple.NonDet where

open import Simple
open import Simple.Effect.NonDet 

open import Data.Nat.DivMod
open import Data.Nat.Properties

run-≤′ : ∀ {n m} -> n ≤′ m -> List ℕ
run-≤′ = go [] where
  go : ∀ {m n} -> List ℕ -> n ≤′ m -> List ℕ
  go {m}     ms  ≤′-refl     = m ∷ ms
  go {suc m} ms (≤′-step le) = go (suc m ∷ ms) le

-- primes 15 = 2 ∷ 3 ∷ 5 ∷ 7 ∷ 11 ∷ 13 ∷ []
primes : ℕ -> List ℕ
primes n = runᵉ ∘ execNonDet $
  gen n >>= λ m ->
    ifte (gen (pred m) >>= λ d -> dguard $ m mod (suc (pred d)) ≟ zero)
         (const ⟨⟩)
         (return m)
    where
      gen : ℕ -> _
      gen  0            = ⟨⟩
      gen  1            = ⟨⟩
      gen (suc (suc n)) = msum ∘ lmap return ∘ run-≤′ $ ≤⇒≤′ (s≤s (s≤s (z≤n {n})))
