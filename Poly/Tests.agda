module Tests where

open import Prelude
open import Map
open import Core
open import Dep

data Reader {α} (A : Set α) : Set α -> Set where
  Get : Reader A A

data Writer {α} (A : Set α) : Set -> Set α where
  Put : A -> Writer A ⊤

runReader : ∀ {α} {A B : Set α} -> A -> Reader A B -> B
runReader x Get = x

runWriter : ∀ {α} {A : Set α} {B : Set} -> Writer A B -> B × A
runWriter (Put x) = tt , x

ask : ∀ {n α} {αβs : Levels n} {A : Set α}
        {Fs : Effects αβs} {{p : Reader A ∈ Fs}}
    -> Eff Fs A _
ask = invoke Get

-- Or with ({Fs = Fs}). What's the problem with inference?
-- Are instance arguments blocking it somehow?
tell : ∀ {n α} {αβs : Levels n} {A : Set α}
         {Fs : Effects αβs} {{p : Writer A ∈ Fs}}
     -> A -> Eff Fs ⊤ _
tell {{p}} x = invoke {{p}} (Put x)

execReader : ∀ {m n α γ} {αβs : Levels n} {A : Set α}
               {Fs : Effects αβs} {C : Set γ} {is : Fin (suc n) ^ m}
           -> A -> Eff (Reader A , Fs) C is -> Eff Fs C (shift is)
execReader x = execEff id id (λ r -> runReader x r , id)

execWriter : ∀ {m n α γ} {αβs : Levels n} {A : Set α}
               {Fs : Effects αβs} {C : Set γ} {is : Fin (suc n) ^ m}
           -> Eff (Writer A , Fs) C is -> Eff Fs (List A × C) (shift is)
execWriter = execEff (List _ ×_) (_,_ []) (second (first ∘ _∷_) ∘ runWriter)

eff₁ : Eff (Writer Set , Reader ℕ , tt) ℕ _
eff₁ = ask >>= λ n -> tell (Fin n) >> tell (Fin (suc n)) >> return n

-- Fin 3 ∷ Fin 4 ∷ [] , 3
test₁ : List Set × ℕ
test₁ = runEff $ execReader 3 $ execWriter eff₁

open import Data.Fin

-- tell {{inj₁ hrefl}} (fromℕ n) >> return 0
effₜ : ask {Fs = Reader ℕ , tt} ↓>>= λ n -> Eff (Writer (Fin (suc n)) , tt) ℕ (zero , tt)
effₜ = call λ n -> invokeᵢ zero (Put (fromℕ n)) >> return 2

effₜ′ : ⟨ Reader ℕ , tt ⟩ λ n -> Eff (Writer (Fin (suc n)) , tt) ℕ (zero , tt)
effₜ′ = ask ↑>>= λ n -> invokeᵢ zero (Put (fromℕ n)) >> return 2

-- zero ∷ suc (suc (suc (suc zero))) ∷ [] , 2
test₂ : List (Fin 5) × ℕ
test₂ = runEff
      $ execWriter
      $ execᵗ (runEff ∘ execReader 4)
      $ (λ e -> invokeᵢ zero (Put zero) >> e) <$>ᵗ effₜ

-- suc (suc (suc (suc zero))) ∷ [] , 2
test₃ : List (Fin 5) × ℕ
test₃ = runEff $ execᵗ (runEff ∘ execReader 4) $ execWriter <$>ᵗ effₜ

open import Data.Vec as V

effₜ₂ : ⟨ Reader ℕ   , tt ⟩ λ n ->
        ⟨ Reader Set , tt ⟩ λ A ->
        Eff (Writer (Vec Set n) , tt) ℕ (zero , tt)
effₜ₂ = ask                 ↑>>= λ n ->
        ask  {{inj₁ hrefl}} ↑>>= λ A ->
        tell {{inj₁ hrefl}} (V.replicate {n = n} A) >>
        return 2

test₄ : List (Vec Set 4) × ℕ
test₄ = runEff
      $ execᵗ (runEff ∘ execReader ℕ)
      $ execᵗ (runEff ∘ execReader 4)
      $ (execWriter <$>ᵗ_) <$>ᵗ effₜ₂
