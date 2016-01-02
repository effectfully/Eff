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
execNonDet : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β}
           -> Eff (NonDet {β} , Ψs) B -> Eff  Ψs (List B)
execNonDet {Ψs = Ψs} {B} = execEff (return ∘ [_]) k where
  k : ∀ {A} -> NonDet A -> (A -> Eff Ψs (List B)) -> Eff Ψs (List B)
  k MZero f = return []
  k MPlus f = _l++_ <$> f false <*> f true
  
dguard : ∀ {n α β} {αψs : Level ²^ n} {A : Set α} {Ψs : Effects αψs} {{p : NonDet {β} ∈ Ψs}}
       -> Dec A -> Eff Ψs (⊤ {β})
dguard (yes _) = return tt
dguard (no  _) = ⟨⟩

msum : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {{p : NonDet {β} ∈ Ψs}}
     -> List (Eff Ψs B) -> Eff Ψs B
msum = lfoldr _<>_ ⟨⟩

module _ where
  open TrustMe

  {-# TERMINATING #-}
  mutual
    msplit : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {{p : NonDet {β} ∈ Ψs}}
           -> Eff Ψs B -> Eff Ψs (Maybe (B × Eff Ψs B))
    msplit       (return y) = return (just (y , ⟨⟩))
    msplit {{q}} (call i p) with runLifts i p
    ... | , a , f with proj i q a
    ... | nothing = call′ i a (msplit ∘ f)
    ... | just nd with uncoerce-cong NonDet nd
    ... | MZero = return nothing
    ... | MPlus = rec-msplit (return ∘′ just ∘′ second (_<> f true)) (msplit (f true)) (f false)

    rec-msplit : ∀ {n β γ} {αψs : Level ²^ n} {Ψs : Effects αψs}
                   {B : Set β} {C : Set γ} {{p : NonDet {β} ∈ Ψs}}
               -> (B × Eff Ψs B -> Eff Ψs C) -> Eff Ψs C -> Eff Ψs B -> Eff Ψs C
    rec-msplit g c b = msplit b >>= maybe′ g c

{-# TERMINATING #-}
interleave : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B : Set β} {{p : NonDet {β} ∈ Ψs}}
           -> Eff Ψs B -> Eff Ψs B -> Eff Ψs B
interleave b₁ b₂ = rec-msplit (return [> _<>_ <] interleave b₂) b₂ b₁

-- `B' and `C' are in the same universe, because `NonDet' is instantiated to `β'.
-- Should we consider something like (∀Effect : ∀ {α} -> Set α -> Set α)?
{-# TERMINATING #-}
_>>-_ : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B C : Set β} {{p : NonDet {β} ∈ Ψs}}
      -> Eff Ψs B -> (B -> Eff Ψs C) -> Eff Ψs C
b >>- g = rec-msplit (g [> interleave <] (_>>- g)) ⟨⟩ b

ifte : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B C : Set β} {{p : NonDet {β} ∈ Ψs}}
     -> Eff Ψs B -> (B -> Eff Ψs C) -> Eff Ψs C -> Eff Ψs C
ifte b g c = rec-msplit (g [> _<>_ <] (_>>= g)) c b

once : ∀ {n β} {αψs : Level ²^ n} {Ψs : Effects αψs} {B C : Set β} {{p : NonDet {β} ∈ Ψs}}
     -> Eff Ψs B -> Eff Ψs B
once = rec-msplit (return ∘ proj₁) ⟨⟩
