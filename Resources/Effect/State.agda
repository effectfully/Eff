module Resources.Effect.State where

open import Resources
 
data State {α} (A : Set α) : Effectful (Set α) α (lsuc α) where
  Get : State A A (const A)
  Put : ∀ {B} -> B -> State A ⊤ (const B)

get : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
        {Ψs : Effects Rs αψs} {rs} {A : Set α} {{p : State , A ∈ Ψs , rs}}
    -> Eff Ψs A rs _
get = invoke Get

zap : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n}
        {Rs : Sets ρs} {Ψs : Effects Rs αψs} {rs}
        (A {B} : Set α) {{p : State , A ∈ Ψs , rs}}
    -> B -> Eff Ψs ⊤ rs _
zap _ {{p}} = invoke′ {{p}} ∘ Put

put : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
        {Ψs : Effects Rs αψs} {rs} {A : Set α} {{p : State , A ∈ Ψs , rs}}
    -> A -> Eff Ψs ⊤ rs _
put = zap _

{-# TERMINATING #-}
execState : ∀ {n α β} {ρs : Level ^ n} {αψs : Level ²^ n} {A : Set α}
              {Rs : Sets ρs} {Ψs : Effects Rs αψs} {B : Set β} {rs rs′}
          -> A
          -> Eff (State , Ψs)  B                    (A , rs)  rs′
          -> Eff  Ψs          (Σ B (headʰ n ∘ rs′))  rs      (tailʰ n ∘ rs′ ∘ proj₁)
execState s (return y) = return (y , s)
execState s (call i p) with runLifts i p
... | , , a , f with i
... | suc i' = call′ i' a (execState s ∘′ f)
... | zero   with a
... | Get    = execState s  (f s)
... | Put s' = execState s' (f tt)
