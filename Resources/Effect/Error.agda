module Resources.Effect.Error where

open import Resources

data Error {β ε} (E : Set ε) : Effectful β ε where
  Throw : {B : Set β} -> E -> Error E B (const E)

throw : ∀ {n β ε} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
          {Ψs : Effects Rs αψs} {B : Set β} {E : Set ε} {rs} {{p : Error , E ∈ Ψs , rs}}
      -> E -> Eff Ψs B rs _
throw = invoke′ ∘ Throw

self-throw : ∀ {n ε} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
               {Ψs : Effects Rs αψs} {E : Set ε} {rs} {{p : Error , E ∈ Ψs , rs}}
           -> E -> Eff Ψs E rs _
self-throw = throw

postulate
  fake : ∀ {n β} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
           {Ψs : Effects Rs αψs} {B : Set β} {rs rs′}
       -> B -> Eff Ψs B rs rs′

throw′ : ∀ {n β ε} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs} {Ψs : Effects Rs αψs}
           {B : Set β} {E : Set ε} {rs rs′} {{p : Error {β} , E ∈ Ψs , rs}}
       -> E -> Eff Ψs B rs rs′
throw′ e = throw e >>= fake

runError : ∀ {ε β} {E : Set ε} {B : Set β} -> Error E B (const E) -> E
runError (Throw e) = e

{-# TERMINATING #-}
catchError : ∀ {n β ε} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
               {Ψs : Effects Rs αψs} {B : Set β} {E : Set ε} {rs rs′}
           -> Eff (Error {β} , Ψs) B (E , rs) rs′
           -> (∀ {rs} -> E -> Eff Ψs B rs (tailʰ n ∘ rs′))
           -> Eff Ψs B rs (tailʰ n ∘ rs′)
catchError (return y) h = return y
catchError (call i p) h with runLifts i p
... | , , a , f with i
... | suc i' = call′ i' a (flip catchError h ∘′ f)
... | zero   with a
... | Throw e = h e

{-# TERMINATING #-}
catchError′ : ∀ {n β ε ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
                {Ψs : Effects Rs αψs} {B : Set β} {E : Set ε} {rs rs′}
                {R : Set ρ} {Ψ : Effect R α ψ} {r}
            -> Eff (Error {β} , Ψs) B (E , rs) rs′
            -> (∀ {rs} -> E -> Eff (Ψ , Ψs) B (r , rs) (λ y -> r , tailʰ n (rs′ y)))
            -> Eff (Ψ , Ψs) B (r , rs) (λ y -> r , tailʰ n (rs′ y))
catchError′ (return y) h = return y
catchError′ (call i p) h with runLifts i p
... | , , a , f with i
... | suc i' = call′ (suc i') a (flip catchError′ h ∘′ f)
... | zero   with a
... | Throw e = h e
