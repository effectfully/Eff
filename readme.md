# Eff

It's an attempt to construct a fully universe polymorphic effect system in Agda.

Effects are represented exactly like in the Idris [Effects](https://github.com/edwinb/Eff-dev/blob/master/effects/Effects.idr) library:

```
Effectful : ∀ α ρ ε -> Set (lsuc (α ⊔ ρ ⊔ ε))
Effectful α ρ ε = (A : Set α) -> (A -> Set ρ) -> Set ε

Effect : ∀ ρ α ε -> Set (lsuc (ρ ⊔ α ⊔ ε))
Effect ρ α ε = Set ρ -> Effectful α ρ ε
```

`Eff` is morally

```
Resource : ∀ ρ -> Set (lsuc ρ)
Resource ρ = Set ρ

Resources : ∀ ρ -> ℕ -> Set (lsuc ρ)
Resources ρ = Vec (Resource ρ)

data Eff {n ρ α ε β} (Ψs : Effects ρ α ε n) (B : Set β) :
       Resources ρ n -> (B -> Resources ρ n) -> Set (lsuc (ρ ⊔ α) ⊔ β ⊔ ε) where
  return : ∀ {Rs′} y -> Eff Ψs B (Rs′ y) Rs′
  call   : ∀ {A R′ Rs Rs′} i
         -> (a : lookup i Ψs (lookup i Rs) A R′)
         -> (f : ∀ x -> Eff Ψs B (Rs [ i ]≔ R′ x) Rs′)
         -> Eff Ψs B Rs Rs′
```

I.e. it's a [Freer](http://okmij.org/ftp/Haskell/extensible/more.pdf) monad with an additional notion of resources, which are dependent in the same style as effects in the Idris library. So while a computation can't change the set of effects like in in Idris, it can change the resources. A canonical example is the indexed `State`:

```
eff : Eff (State , tt) (ℕ , tt) ℕ (λ n -> V.Vec Bool n , tt) _
eff = get >>= λ n -> put (V.replicate true) >> return n
```

(`put` is `zap ℕ` actually, because instance search needs an additional hint in this case)

So we start from `State ℕ` and get `State (Vec Bool n)`, where `n` comes from `State ℕ`.

We can run this computation:

```
-- 3 , true ∷ true ∷ true ∷ []
test : ∃ (V.Vec Bool)
test = runEff $ execState 3 eff
```

The actual definition of `Eff` is more entangled:

```
data Eff {n β} {ρs : Level ^ n} {αεs : Level ²^ n} (Ψs : Effects ρs αεs) (B : Set β)
         : Resources ρs -> (B -> Resources ρs) -> Set (effˡ ρs αεs β) where
  return : ∀ {Rs′} y -> Eff Ψs B (Rs′ y) Rs′
  call   : ∀ {Rs Rs′} i
         -> (Lift∃ᵐ (lsuc ∘ proj₁) i αεs λ A ->
               Lift∃ᶻ r′ˡ i αεs ρs λ R′ ->
                 Lift∃ᵐ proj₂ i αεs {lookupᶻ i Ψs (lookupᵐ i Rs) A R′} λ _ ->
                   Lift∀ᵐ  proj₁ i αεs λ x ->
                     Eff Ψs B (replaceᵐ i (R′ x) Rs) Rs′)
         -> Eff Ψs B Rs Rs′
```

It's the same `Eff` as before, but with some ugly lifting to make all `call`s lie in the same universe.

For a readable, but not fully universe polymorphic machinery look [here](https://github.com/effectfully/random-stuff/tree/master/MonoEff).