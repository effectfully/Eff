module Resources.Effect.Error where

open import Resources

data Error {ε} (E : Set ε) : Effectful lzero ε where
  Throw : E -> Error E ⊥ (const E)

-- TODO: describe why this is bad:
-- data Error {β ε} (E : Set ε) : Effectful β ε where
--   Throw : {B : Set β} -> E -> Error E B (const E)

throw : ∀ {n β ε} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
          {Ψs : Effects Rs αψs} {B : Set β} {E : Set ε} {rs rs′} {{p : Error , E ∈ Ψs , rs}}
      -> E -> Eff Ψs B rs rs′
throw e = invoke (Throw e) >>= ⊥-elim

self-throw : ∀ {n ε} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
               {Ψs : Effects Rs αψs} {E : Set ε} {rs rs′} {{p : Error , E ∈ Ψs , rs}}
           -> E -> Eff Ψs E rs rs′
self-throw = throw

runError : ∀ {ε} {E : Set ε} -> Error E ⊥ (const E) -> E
runError (Throw e) = e

{-# TERMINATING #-}
catchError : ∀ {n β ε} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
               {Ψs : Effects Rs αψs} {B : Set β} {E : Set ε} {rs rs′}
           -> Eff (Error , Ψs) B (E , rs) rs′
           -> (∀ {rs} -> E -> Eff Ψs B rs (tailʰ n ∘ rs′))
           -> Eff Ψs B rs (tailʰ n ∘ rs′)
catchError (return y) h = return y
catchError (call i p) h with runLifts i p
... | , , a , f with i
... | suc i' = call′ i' a (flip catchError h ∘′ f)
... | zero   with a
... | Throw e = h e

{-# TERMINATING #-}
handleError : ∀ {n β ε ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
                {Ψs : Effects Rs αψs} {B : Set β} {E : Set ε} {rs rs′}
                {R : Set ρ} {Ψ : Effect R α ψ} {r}
            -> Eff (Error , Ψs) B (E , rs) rs′
            -> (∀ {rs} -> E -> Eff (Ψ , Ψs) B (r , rs) (λ y -> r , tailʰ n (rs′ y)))
            -> Eff (Ψ , Ψs) B (r , rs) (λ y -> r , tailʰ n (rs′ y))
handleError (return y) h = return y
handleError (call i p) h with runLifts i p
... | , , a , f with i
... | suc i' = call′ (suc i') a (flip handleError h ∘′ f)
... | zero   with a
... | Throw e = h e
