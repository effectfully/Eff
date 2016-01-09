module Resources.Effect.LiftM where

open import Resources

data Lift[_] {α β} (M : Set α -> Set β) : Simple α (lsuc α ⊔ β) where
  LiftM : ∀ {A} -> M A -> Lift[ M ] tt A _

liftM : ∀ {n α β} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
          {Ψs : Effects Rs αψs} {A : Set α} {rs}
      -> (M : Set α -> Set β) {{p : Lift[ M ] , tt ∈ Ψs , rs}} -> M A -> Eff Ψs A rs _
liftM M = invoke ∘ LiftM
