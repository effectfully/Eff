{-# OPTIONS --type-in-type #-}

module Loop.Effect.General where

open import Loop

data General A (B : A -> Set) : Effect ⊤ where
  Rec : ∀ x -> General A B tt (B x) (const tt)

grec : ∀ {Φs Rs rs A} {Ψs : Effects Rs} {B : A -> Set} {{p : General A B , tt ∈² Ψs , rs}}
     -> ∀ x -> EffOver Φs Ψs rs (B x) _
grec = invoke ∘′ Rec

Generalᴱ : (A : Set) -> (A -> Set) -> Set -> Set
Generalᴱ A B C = Eff (General A B , tt) _ C _

Π : (A : Set) -> (A -> Set) -> Set
Π A B = ∀ x -> Generalᴱ A B (B x)

rec : ∀ {A} {B : A -> Set} -> Π A B
rec = invoke₀ ∘′ Rec

_⇒_ : Set -> Set -> Set
A ⇒ B = Π A λ _ -> B

runGeneralM : ∀ {A B C} {M : Set -> Set}
            -> (∀ {A} -> A -> M A)
            -> (∀ {A B} -> M A -> (A -> M B) -> M B)
            -> (∀ x -> M (B x))
            -> Generalᴱ A B C
            -> M C
runGeneralM {A} {B} {M = M} ret bind h = runEffM ret bind hₑ where
  hₑ : ∀ {r C r′} -> Unionᵉ (General A B , tt) r C r′ -> M C
  hₑ (hereᵉ (Rec x)) = h x
  hₑ (thereᵉ ())

petrol : ∀ {A B} -> ℕ -> Π A B -> ∀ x -> Maybe (B x)
petrol  0      f x = nothing
petrol (suc n) f x = runGeneralM just _>>=ₘ_ (petrol n f) (f x)
