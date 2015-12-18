module Eff.Core where

open import Eff.Prelude
open import Eff.Zip

infixl 1 _>>=_
infixr 2 _>>_
infixl 6 _<$>_

Effect : ∀ α β -> Set (lsuc (α ⊔ β))
Effect α β = Set α -> Set β

Effects : ∀ {n} -> (αs βs : Level ^ n) -> Set _
Effects = Zip Effect

effˡ : ∀ {m n} -> (αs βs : Level ^ n) -> Level -> Fin n ^ m -> Level
effˡ {0}     αs βs γ  tt      = γ
effˡ {suc m} αs βs γ (i , is) = lsuc (lookup i αs) ⊔ lookup i βs ⊔ effˡ αs βs γ is

Eff⁻ : ∀ {m n γ} {αs βs : Level ^ n}
     -> Effects αs βs -> Set γ -> (is : Fin n ^ m) -> Set (effˡ αs βs γ is)
Eff⁻ {0}     Fs C  tt      = C
Eff⁻ {suc m} Fs C (i , is) = ∃ λ A -> lookupᶻ i Fs A × (A -> Eff⁻ Fs C is)

record Eff {m n γ} {αs βs : Level ^ n} (Fs : Effects αs βs) (C : Set γ)
           (is : Fin n ^ m) : Set (effˡ αs βs γ is) where
  constructor wrap
  field unwrap : Eff⁻ Fs C is
open Eff

return : ∀ {n γ} {αs βs : Level ^ n} {Fs : Effects αs βs} {C : Set γ} -> C -> Eff Fs C tt
return = wrap

runEff : ∀ {γ} {C : Set γ} -> Eff tt C tt -> C
runEff = unwrap

bind : ∀ {m p n γ δ} {αs βs : Level ^ n} {Fs : Effects αs βs}
         {C : Set γ} {D : Set δ} {js : Fin n ^ p}
     -> (is : Fin n ^ m) -> Eff⁻ Fs C is -> (C -> Eff⁻ Fs D js) -> Eff⁻ Fs D (is ++ js)
bind {0}      tt      z h = h z
bind {suc m} (i , is) c h = third (λ f x -> bind is (f x) h) c

_>>=_ : ∀ {m p n γ δ} {αs βs : Level ^ n} {Fs : Effects αs βs}
          {C : Set γ} {D : Set δ} {is : Fin n ^ m} {js : Fin n ^ p}
      -> Eff Fs C is -> (C -> Eff Fs D js) -> Eff Fs D (is ++ js)
_>>=_ {is = is} c h = wrap (bind is (unwrap c) (unwrap ∘ h))

_>>_ : ∀ {m p n γ δ} {αs βs : Level ^ n} {Fs : Effects αs βs}
         {C : Set γ} {D : Set δ} {is : Fin n ^ m} {js : Fin n ^ p}
      -> Eff Fs C is -> Eff Fs D js -> Eff Fs D (is ++ js)
c >> d = c >>= const d

-- Just don't want to prove (n + 0 ≡ 0).
fmap⁻ : ∀ {m n γ δ} {αs βs : Level ^ n} {Fs : Effects αs βs} {C : Set γ} {D : Set δ}
      -> (is : Fin n ^ m) -> (C -> D) -> Eff⁻ Fs C is -> Eff⁻ Fs D is
fmap⁻ {0}      tt      h z = h z
fmap⁻ {suc m} (i , is) h c = third (fmap⁻ is h ∘_) c 

_<$>_ : ∀ {m n γ δ} {αs βs : Level ^ n} {Fs : Effects αs βs}
          {C : Set γ} {D : Set δ} {is : Fin n ^ m}
      -> (C -> D) -> Eff Fs C is -> Eff Fs D is
_<$>_ {is = is} h = wrap ∘ fmap⁻ is h ∘ unwrap

invokeᵢ : ∀ {n} {αs βs : Level ^ n} {Fs : Effects αs βs}
        -> (i : Fin n) -> ∀ {A} -> lookupᶻ i Fs A -> Eff Fs A (i , tt)
invokeᵢ i a = wrap (, a , id)

invoke⁻ : ∀ n {α β} {αs βs : Level ^ n} {A : Set α} {F : Effect α β} {Fs : Effects αs βs}
        -> (p : F ∈ Fs) -> F A -> Eff⁻ Fs A (∈→Fin n p , tt)
invoke⁻  0      ()       a
invoke⁻ (suc n) (inj₁ r) a = , hSubst r a , uncoerce
invoke⁻ (suc n) (inj₂ p) a = invoke⁻ n p a

invoke : ∀ {n α β} {αs βs : Level ^ n} {A : Set α} {F : Effect α β}
           {Fs : Effects αs βs} {{p : F ∈ Fs}}
       -> F A -> Eff Fs A (∈→Fin n p , tt)
invoke {n} {{p}} = wrap ∘ invoke⁻ n p 

non-zeros : ∀ {m n} -> Fin (suc n) ^ m -> ℕ
non-zeros {0}      tt          = 0
non-zeros {suc m} (zero  , is) = non-zeros is
non-zeros {suc m} (suc i , is) = suc (non-zeros is)

shift : ∀ {m n} -> (is : Fin (suc n) ^ m) -> Fin n ^ non-zeros is
shift {0}      tt          = tt
shift {suc m} (zero  , is) = shift is
shift {suc m} (suc i , is) = i , shift is

execEff⁻ : ∀ {m n α β γ δ} {αs βs : Level ^ n} {F : Effect α β}
             {Fs : Effects αs βs} {C : Set γ}
         -> (is : Fin (suc n) ^ m)
         -> (G : Set γ -> Set δ)
         -> (C -> G C)
         -> (∀ {A} -> F A -> A × (G C -> G C))
         -> Eff⁻ (F , Fs)  C     is
         -> Eff⁻  Fs      (G C) (shift is)
execEff⁻ {0}      tt          G ret out  c        = ret c
execEff⁻ {suc m} (zero  , is) G ret out (, a , f) =
  let x , g = out a in fmap⁻ (shift is) g (execEff⁻ is G ret out (f x))
execEff⁻ {suc m} (suc i , is) G ret out (, a , f) =
  , a , λ x -> execEff⁻ is G ret out (f x)

execEff : ∀ {m n α β γ δ} {αs βs : Level ^ n} {F : Effect α β}
            {Fs : Effects αs βs} {C : Set γ} {is : Fin (suc n) ^ m}
        -> (G : Set γ -> Set δ)
        -> (C -> G C)
        -> (∀ {A} -> F A -> A × (G C -> G C))
        -> Eff (F , Fs)  C     is
        -> Eff  Fs      (G C) (shift is)
execEff {is = is} G ret out = wrap ∘ execEff⁻ is G ret out ∘ unwrap
