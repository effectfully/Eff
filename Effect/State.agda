module Effect.State where

open import Prelude
open import Map
open import Core
open import Membership

data State {α} (A : Set α) : Effectful α α (lsuc α) where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

get : ∀ {n α} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
        {Rs : Resources ρs} {A : Set α} {{p : State , A ∈ Ψs , Rs}}
    -> Eff Ψs Rs A _ _
get = invoke Get

zap : ∀ {n α} {ρs : Level ^ n} {αεs : Level ²^ n}
        {Ψs : Effects ρs αεs} {Rs : Resources ρs}
        (A {B} : Set α) {{p : State , A ∈ Ψs , Rs}}
    -> B -> Eff Ψs Rs ⊤ _ _
zap _ {{p}} = invoke′ {{p}} ∘ Put

put : ∀ {n α} {ρs : Level ^ n} {αεs : Level ²^ n} {Ψs : Effects ρs αεs}
        {Rs : Resources ρs} {A : Set α} {{p : State , A ∈ Ψs , Rs}}
    -> A -> Eff Ψs Rs ⊤ _ _
put = zap _

execState⁻ : ∀ {m n ρ β} {ρs : Level ^ n} {αεs : Level ²^ n}
               {Ψs : Effects ρs αεs} {R : Set ρ} {Rs : Resources ρs}
               {B : Set β} {Rs′ : B -> Resources (ρ , ρs)}
           -> (is : Fin (suc n) ^ m)
           -> R
           -> Eff⁻ (State , Ψs) (R , Rs)  B                   Rs′                   is
           -> Eff⁻  Ψs           Rs      (Σ B (headᵐ ∘ Rs′)) (tailᵐ ∘ Rs′ ∘ proj₁) (shift is)
execState⁻ {0}      tt          s (y , refl)      = (y , s) , refl
execState⁻ {suc m} (zero  , is) s (, , Get   , f) = execState⁻ is s (f s)
execState⁻ {suc m} (zero  , is) _ (, , Put s , f) = execState⁻ is s (f tt)
execState⁻ {suc m} (suc i , is) s  b              = fourth (execState⁻ is s ∘_) b

execState : ∀ {m n ρ β} {ρs : Level ^ n} {αεs : Level ²^ n}
              {Ψs : Effects ρs αεs} {R : Set ρ} {Rs : Resources ρs}
              {B : Set β} {Rs′ : B -> Resources (ρ , ρs)} {is : Fin (suc n) ^ m}
          -> R
          -> Eff (State , Ψs) (R , Rs)  B                   Rs′                   is
          -> Eff  Ψs           Rs      (Σ B (headᵐ ∘ Rs′)) (tailᵐ ∘ Rs′ ∘ proj₁) (shift is)
execState {is = is} s = wrap ∘ execState⁻ is s ∘ unwrap


open import Data.Bool.Base
import Data.Vec as V

eff₁ : Eff (State , tt) (ℕ , tt) ℕ (λ n -> V.Vec Bool n , tt) _
eff₁ = get >>= λ n -> zap ℕ (V.replicate true) >> return n

eff₂ : ∀ {α} -> Eff (State , State , tt) (ℕ , Set α , tt) ℕ (λ _ -> ℕ , Set α , tt) _
eff₂ = get >>= λ n -> put n >> return (suc n)

-- 3 , true ∷ true ∷ true ∷ []
test₁ : ∃ (V.Vec Bool)
test₁ = runEff $ execState 3 eff₁

-- 4 , 3
test₂ : ℕ × ℕ
test₂ = proj₁ $ runEff $ execState ℕ $ execState 3 eff₂
