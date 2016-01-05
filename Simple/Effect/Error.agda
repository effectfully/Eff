module Simple.Effect.Error where

open import Simple

data Error {ε} (E : Set ε) : ∀ {β} -> Set β -> Set ε where
  Throw : ∀ {β} {B : Set β} -> E -> Error E B

throw : ∀ {n ε β} {αψs : Level ²^ n} {Ψs : Effects αψs}
          {B : Set β} {E : Set ε} {{p : Error E ∈ Ψs}}
      -> E -> Eff Ψs B
throw = invoke ∘ Throw

runError : ∀ {ε β} {E : Set ε} {B : Set β} -> Error E B -> E
runError (Throw e) = e

catch : ∀ {n ε β} {αψs : Level ²^ n} {Ψs : Effects αψs}
          {B : Set β} {E : Set ε} {{p : Error E {β} ∈ Ψs}}
      -> Eff Ψs B -> (E -> Eff Ψs B) -> Eff Ψs B
catch {{p}} b h = procEff {{p}} return (const ∘ h ∘ runError) b

execError : ∀ {n ε β} {αψs : Level ²^ n} {Ψs : Effects αψs} {E : Set ε} {B : Set β}
          -> Eff (Error E {β} , Ψs) B -> Eff Ψs (E ⊎ B)
execError = execEff (return ∘ inj₂) (const ∘ return ∘ inj₁ ∘ runError)

catchError : ∀ {n ε β} {αψs : Level ²^ n} {Ψs : Effects αψs} {E : Set ε} {B : Set β}
           -> Eff (Error E {β} , Ψs) B -> (E -> Eff Ψs B) -> Eff Ψs B
catchError b h = execEff return (const ∘ h ∘ runError) b
