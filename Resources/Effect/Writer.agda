module Resources.Effect.Writer where

open import Resources
 
data Writer {α} (A : Set α) : Effectful α α where
  Tell : A -> Writer A ⊤ (const A)

tell : ∀ {n α} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
         {Ψs : Effects Rs αψs} {rs} {A : Set α} {{p : Writer , A ∈ Ψs , rs}}
     -> A -> Eff Ψs ⊤ rs _
tell = invoke ∘ Tell

{-# TERMINATING #-}
execWriter : ∀ {n α β} {ρs : Level ^ n} {αψs : Level ²^ n} {A : Set α}
               {Rs : Sets ρs} {Ψs : Effects Rs αψs} {B : Set β} {rs rs′}
           -> Eff (Writer , Ψs)  B           (A , rs)  rs′
           -> Eff  Ψs           (B × List A)  rs      (tailʰ n ∘ rs′ ∘ proj₁)
execWriter (return y) = return (y , [])
execWriter (call i p) with runLifts i p
... | , , a , f with i
... | suc i' = call′ i' a (execWriter ∘′ f)
... | zero   with a
... | Tell x = execWriter (f tt) >>= return ∘′ second (x ∷_)
