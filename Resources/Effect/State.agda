module Resources.Effect.State where

open import Prelude
open import Map
open import Resources.Core
open import Resources.Membership

data State {α} (A : Set α) : Effectful α α (lsuc α) where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

get : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs}
        {Rs : Resources ρs} {A : Set α} {{p : State , A ∈ Ψs , Rs}}
    -> Eff Ψs A Rs _
get = invoke Get

zap : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n}
        {Ψs : Effects ρs αψs} {Rs : Resources ρs}
        (A {B} : Set α) {{p : State , A ∈ Ψs , Rs}}
    -> B -> Eff Ψs ⊤ Rs _
zap _ {{p}} = invoke′ {{p}} ∘ Put

put : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs}
        {Rs : Resources ρs} {A : Set α} {{p : State , A ∈ Ψs , Rs}}
    -> A -> Eff Ψs ⊤ Rs _
put = zap _

{-# TERMINATING #-}
execState : ∀ {n ρ β} {ρs : Level ^ n} {αψs : Level ²^ n} {Ψs : Effects ρs αψs}
              {B : Set β} {R : Set ρ} {Rs : Resources ρs} {Rs′ : B -> Resources (ρ , ρs)}
          -> R
          -> Eff (State , Ψs)  B                  (R , Rs)  Rs′
          -> Eff  Ψs          (Σ B (headᵐ ∘ Rs′))  Rs      (tailᵐ ∘ Rs′ ∘ proj₁)
execState s (return y) = return (y , s)
execState s (call i p) with runLifts i p
... | , , a , f with i
... | suc i' = call′ i' a (execState s ∘ f)
... | zero   with a
... | Get    = execState s  (f s)
... | Put s' = execState s' (f tt)



private
  import Data.Vec as V

  eff₁ : Eff (State , tt) ℕ (ℕ , tt) (λ n -> V.Vec Bool n , tt)
  eff₁ = get >>= λ n -> zap ℕ (V.replicate true) >> return n

  eff₂ : ∀ {α} -> Eff (State , State , tt) ℕ (ℕ , Set α , tt) (λ _ -> ℕ , Set α , tt)
  eff₂ = get >>= λ n -> put n >> return (suc n)

  -- 3 , true ∷ true ∷ true ∷ []
  test₁ : ∃ (V.Vec Bool)
  test₁ = runᵉ $ execState 3 eff₁

  -- 4 , 3
  test₂ : ℕ × ℕ
  test₂ = proj₁ $ runᵉ $ execState ℕ $ execState 3 eff₂
