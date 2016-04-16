{-# OPTIONS --type-in-type #-}

module Loop.Effect.State where

open import Loop

data State A : Effectful where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

get : ∀ {Φs Rs rs A} {Ψs : Effects Rs} {{p : State , A ∈² Ψs , rs}} -> EffOver Φs Ψs rs A _
get = invoke Get

zap : ∀ {Φs Rs rs B} {Ψs : Effects Rs} A {{p : State , A ∈² Ψs , rs}} -> B -> EffOver Φs Ψs rs ⊤ _
zap _ = invoke′ ∘ Put

put : ∀ {Φs Rs rs A} {Ψs : Effects Rs} {{p : State , A ∈² Ψs , rs}} -> A -> EffOver Φs Ψs rs ⊤ _
put = invoke ∘ Put

{-# TERMINATING #-}
execState : ∀ {Rs A rs B rs′} {Ψs : Effects Rs}
          -> A
          -> Eff (State , Ψs) (A , rs)  B                   rs′
          -> Eff  Ψs           rs      (Σ B (head₁ ∘ rs′)) (tail₁ ∘ rs′ ∘ proj₁)
execState s (return y)                  = return (y , s)
execState s (call (hereʰᵉ (thereᵉ a)) k) = call (hereʰᵉ a) (λ x -> execState s (k x))
execState s (call (thereʰᵉ ())        k)
execState s (call (hereʰᵉ (hereᵉ a))  k) with a
... | Get    = execState s  (k s)
... | Put s' = execState s' (k tt)

private
  open import Data.Vec as V hiding (_>>=_)

  test : Eff (State , tt) (ℕ , tt) ℕ (λ n -> V.Vec Bool n , tt)
  test = get >>= λ n -> zap ℕ (V.replicate true) >> return n

  test-test : runEff (execState 3 test) ≡ (3 , true ∷ true ∷ true ∷ [])
  test-test = refl
