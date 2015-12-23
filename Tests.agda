module Tests where

open import Prelude
open import Map
open import Core
open import Membership
-- open import Dep

data Reader {α} (A : Set α) : Effectful α α lzero where
  Get : Reader A A (const A)

data Writer {α} (A : Set α) : Effectful lzero α (lsuc α) where
  Put : ∀ {B} -> B -> Writer A ⊤ (const B)

{-runReader : ∀ {α} {A B : Set α} -> A -> Reader A B -> B
runReader x Get = x

runWriter : ∀ {α} {A : Set α} {B : Set} -> Writer A B -> B × A
runWriter (Put x) = tt , x-}

ask : ∀ {n α} {ρs : Level ^ n} {αεs : Level ²^ n}
        {Ψs : Effects ρs αεs} {Rs : Resources ρs}
        {A : Set α} {{p : Reader , A ∈ Ψs , Rs}}
    -> Eff Ψs Rs A _ _
ask = invoke Get

zap : ∀ {n α} {ρs : Level ^ n} {αεs : Level ²^ n}
        {Ψs : Effects ρs αεs} {Rs : Resources ρs}
        (A {B} : Set α) {{p : Writer , A ∈ Ψs , Rs}} -> B -> Eff Ψs Rs ⊤ _ _
zap _ {{p}} = invoke {{p}} ∘ Put

tell : ∀ {n α} {ρs : Level ^ n} {αεs : Level ²^ n}
         {Ψs : Effects ρs αεs} {Rs : Resources ρs}
         {A : Set α} {{p : Writer , A ∈ Ψs , Rs}}
     -> A -> Eff Ψs Rs ⊤ _ _
tell = zap _

import Data.Vec as V

eff₁ : Eff (Writer , Reader , tt) (Set , ℕ , tt) ℕ (λ n -> V.Vec Set n , ℕ , tt) _
eff₁ = ask >>= λ n -> zap Set (V.replicate (Fin n)) >> return n



-- execReader : ∀ {m n α γ} {αβs : Levels n} {A : Set α}
--                {Fs : Effects αβs} {C : Set γ} {is : Fin (suc n) ^ m}
--            -> A -> Eff (Reader A , Fs) C is -> Eff Fs C (shift is)
-- execReader x = execEff id id (λ r -> runReader x r , id)

-- execWriter : ∀ {m n α γ} {αβs : Levels n} {A : Set α}
--                {Fs : Effects αβs} {C : Set γ} {is : Fin (suc n) ^ m}
--            -> Eff (Writer A , Fs) C is -> Eff Fs (List A × C) (shift is)
-- execWriter = execEff (List _ ×_) (_,_ []) (second (first ∘ _∷_) ∘ runWriter)

-- eff₁ : Eff (Writer Set , Reader ℕ , tt) ℕ _
-- eff₁ = ask >>= λ n -> tell (Fin n) >> tell (Fin (suc n)) >> return n

-- -- Fin 3 ∷ Fin 4 ∷ [] , 3
-- test₁ : List Set × ℕ
-- test₁ = runEff $ execReader 3 $ execWriter eff₁

-- open import Data.Fin

-- -- tell {{inj₁ hrefl}} (fromℕ n) >> return 0
-- effₜ : ask {Fs = Reader ℕ , tt} ↓>>= λ n -> Eff (Writer (Fin (suc n)) , tt) ℕ (zero , tt)
-- effₜ = call λ n -> invokeᵢ zero (Put (fromℕ n)) >> return 2

-- effₜ′ : ⟨ Reader ℕ , tt ⟩ λ n -> Eff (Writer (Fin (suc n)) , tt) ℕ (zero , tt)
-- effₜ′ = ask ↑>>= λ n -> invokeᵢ zero (Put (fromℕ n)) >> return 2

-- -- zero ∷ suc (suc (suc (suc zero))) ∷ [] , 2
-- test₂ : List (Fin 5) × ℕ
-- test₂ = runEff
--       $ execWriter
--       $ execᵗ (runEff ∘ execReader 4)
--       $ (λ e -> invokeᵢ zero (Put zero) >> e) <$>ᵗ effₜ

-- -- suc (suc (suc (suc zero))) ∷ [] , 2
-- test₃ : List (Fin 5) × ℕ
-- test₃ = runEff $ execᵗ (runEff ∘ execReader 4) $ execWriter <$>ᵗ effₜ

-- open import Data.Vec as V

-- effₜ₂ : ⟨ Reader ℕ   , tt ⟩ λ n ->
--         ⟨ Reader Set , tt ⟩ λ A ->
--         Eff (Writer (Vec Set n) , tt) ℕ (zero , tt)
-- effₜ₂ = ask                 ↑>>= λ n ->
--         ask  {{inj₁ hrefl}} ↑>>= λ A ->
--         tell {{inj₁ hrefl}} (V.replicate {n = n} A) >>
--         return 2

-- test₄ : List (Vec Set 4) × ℕ
-- test₄ = runEff
--       $ execᵗ (runEff ∘ execReader ℕ)
--       $ execᵗ (runEff ∘ execReader 4)
--       $ (execWriter <$>ᵗ_) <$>ᵗ effₜ₂
