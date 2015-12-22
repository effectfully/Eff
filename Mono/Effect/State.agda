module Effect.State where

open import Prelude
open import Core

data State {α} (A : Set α) : Effectful α α (lsuc α) where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

execState : ∀ {n α β} {Ψs : Effects α α (lsuc α) n} {B : Set β}
              {Rs : Resources α (suc n)} {Rs′ : B -> Resources α (suc n)}
          -> head Rs
          -> Eff (State ∷ Ψs)  B                  Rs        Rs′
          -> Eff  Ψs          (Σ B (head ∘ Rs′)) (tail Rs) (tail ∘ Rs′ ∘ proj₁)
execState              s (return y)               = return (y , s)
execState {Rs = _ ∷ _} s (call  zero    Get    f) = execState s (f s)
execState {Rs = _ ∷ _} _ (call  zero   (Put s) f) = execState s (f tt)
execState {Rs = _ ∷ _} s (call (suc i)  a      f) = call i a λ x -> execState s (f x)

open import Data.Bool.Base

eff : Eff [ State ] ℕ [ ℕ ] (λ n -> [ Vec Bool n ])
eff = call zero (Put (replicate {n = 3} true)) (λ _ -> return 3)

test : ∃ (Vec Bool)
test = runEff $ execState 0 eff
