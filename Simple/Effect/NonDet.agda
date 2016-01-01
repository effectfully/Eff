module Simple.Effect.NonDet where

open import Prelude
open import Map
open import Simple.Core
open import Simple.Membership

data NonDet {α} : Effect α α where
  MZero : ∀ {A} -> NonDet A
  MPlus :          NonDet Bool

⟨⟩ : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {{p : NonDet ∈ Ψs}}
   -> Eff Ψs B
⟨⟩ = invoke MZero

_<>_ : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {{p : NonDet {β} ∈ Ψs}}
     -> Eff Ψs B -> Eff Ψs B -> Eff Ψs B
m₁ <> m₂ = invoke MPlus >>= m₁ <∨> m₂

{-# TERMINATING #-}
execNonDet : ∀ {n α β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β}
           -> Eff (NonDet {α} , Ψs) B -> Eff  Ψs (List B)
execNonDet {Ψs = Ψs} {B} = execEff (return ∘ [_]) k where
  k : ∀ {A} -> NonDet A -> (A -> Eff Ψs (List B)) -> Eff Ψs (List B)
  k MZero f = return []
  k MPlus f = _++ₗ_ <$> f false <*> f true

open TrustMe

{-# TERMINATING #-}
msplit : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {{p : NonDet {β} ∈ Ψs}}
       -> Eff Ψs B -> Eff Ψs (Maybe (B × Eff Ψs B))
msplit       (return y) = return (just (y , ⟨⟩))
msplit {{q}} (call i p) with runLifts i p
... | , a , f with proj i q a
... | nothing = call′ i a (msplit ∘ f)
... | just nd with uncoerce-cong NonDet nd
... | MZero = return nothing
... | MPlus = msplit (f false) >>= maybe′ (return ∘′ just ∘′ second (_<> f true)) (msplit (f true))
