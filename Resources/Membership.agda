module Resources.Membership where

open import Prelude
open import Map
open import Resources.Core

infix 3 _∈_

open TrustMe

private
  Subst : ∀ {α₁ α₂ ψ₁ ψ₂ ρ} {R : Set ρ} {A : Set α₁} {r f}
            {Ψ₁ : Effect R α₁ ψ₁} {Ψ₂ : Effect R α₂ ψ₂}
        -> Ψ₁ ≅ Ψ₂
        -> Ψ₁ r  A          f
        -> Ψ₂ r (Coerce A) (f ∘ uncoerce)
  Subst {α₁} {α₂} {ψ₁} {ψ₂} p rewrite trustMe α₁ α₂ | trustMe ψ₁ ψ₂ = subst (λ F -> F _ _ _) (≅→≡ p)

_∈_ : ∀ {n ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {R : Set ρ} {Rs : Sets ρs}
    -> Effect R α ψ × R -> Effects Rs αψs × Resources Rs -> Set
_∈_ {0}     (Φ , s) ( tt      ,  tt)      = ⊥
_∈_ {suc n} (Φ , s) ((Ψ , Ψs) , (r , rs)) = Φ ≅ Ψ × s ≅ r ⊎ Φ , s ∈ Ψs , rs 

∈→Fin : ∀ {n ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {R : Set ρ} {Rs : Sets ρs}
          {Ψr : Effect R α ψ × R} {Ψrs : Effects Rs αψs × Resources Rs}
      -> Ψr ∈ Ψrs -> Fin n
∈→Fin {0}     ()
∈→Fin {suc n} (inj₁ _) = zero
∈→Fin {suc n} (inj₂ p) = suc (∈→Fin p)

coerce : ∀ {n ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {R : Set ρ}
           {Rs : Sets ρs} {r rs} {Ψ : Effect R α ψ} {Ψs : Effects Rs αψs}
       -> (p : Ψ , r ∈ Ψs , rs) -> R -> lookupᵐ (∈→Fin p) Rs
coerce {0}     ()                 r
coerce {suc n} (inj₁ (_ , hrefl)) r = r
coerce {suc n} (inj₂  p)          r = coerce p r

invoke′ : ∀ {n ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n}
            {R : Set ρ} {Ψ : Effect R α ψ} {Rs : Sets ρs}
            {r A r′ rs} {Ψs : Effects Rs αψs} {{p : Ψ , r ∈ Ψs , rs}}
        -> Ψ r A r′ -> Eff Ψs A rs (λ x -> replaceʰ (∈→Fin p) (coerce p (r′ x)) rs)
invoke′ {0}     {{()}}               a
invoke′ {suc n} {{inj₁ (q , hrefl)}} a = call′ zero (Subst q a) (return ∘′ uncoerce)
invoke′ {suc n} {{inj₂  p}}          a = shiftᵉ (invoke′ a)

invoke : ∀ {n ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {R : Set ρ} {Ψ : Effect R α ψ}
           {Rs : Sets ρs} {r A rs} {Ψs : Effects Rs αψs} {{p : Ψ , r ∈ Ψs , rs}}
       -> Ψ r A (const r) -> Eff Ψs A rs (const rs)
invoke {0}     {{()}}               a
invoke {suc n} {{inj₁ (q , hrefl)}} a = call′ zero (Subst q a) (return ∘ uncoerce)
invoke {suc n} {{inj₂  p}}          a = shiftᵉ (invoke a)

unfold-lookupᵐ : ∀ {n ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {R : Set ρ}
                   {Rs : Sets ρs} {Ψ : Effect R α ψ} {Ψs : Effects Rs αψs} {r rs}
               -> (p : Ψ , r ∈ Ψs , rs) -> R -> lookupᵐ (∈→Fin p) Rs
unfold-lookupᵐ {0}     ()                 r
unfold-lookupᵐ {suc n} (inj₁ (q , hrefl)) r = r
unfold-lookupᵐ {suc n} (inj₂  p)          r = unfold-lookupᵐ p r

unfold-lookupᵉ : ∀ {n ρ α ψ} {ρs : Level ^ n} {αψs : Level ²^ n} {R : Set ρ}
                   {Rs : Sets ρs} {Ψ : Effect R α ψ} {Ψs : Effects Rs αψs} {r rs}
               -> ∀ (p : Ψ , r ∈ Ψs , rs) {A r′}
               -> Ψ r A r′
               -> lookupᵉ (∈→Fin p)
                           Ψs
                          (lookupʰ (∈→Fin p) rs) (Coerce A)
                          (unfold-lookupᵐ p ∘ r′ ∘ uncoerce)
unfold-lookupᵉ {0}     ()                 a
unfold-lookupᵉ {suc n} (inj₁ (q , hrefl)) a = Subst q a
unfold-lookupᵉ {suc n} (inj₂  p)          a = unfold-lookupᵉ p a
