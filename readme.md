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

I.e. it's a [Freer](http://okmij.org/ftp/Haskell/extensible/more.pdf) monad with the additional notion of resources, which are dependent in the same style as effects in the Idris library. So while a computation can't change the set of effects like in in Idris, it can change the resources. An immediate example is the indexed `State`:

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
Eff⁻ : ∀ {m n β} {ρs : Level ^ n} {αεs : Level ²^ n}
     -> Effects ρs αεs
     -> Resources ρs
     -> (B : Set β)
     -> (B -> Resources ρs)
     -> (is : Fin n ^ m)
     -> Set (effˡ ρs αεs β is)
Eff⁻ {0}     Ψs Rs B Rs′  tt      = ∃ λ y -> Rs ≡ Rs′ y
Eff⁻ {suc m} Ψs Rs B Rs′ (i , is) =
  ∃ λ A -> ∃ λ R′ -> lookupᶻ i Ψs (lookupᵐ i Rs) A R′
                       × ∀ x -> Eff⁻ Ψs (replaceᵐ i (R′ x) Rs) B Rs′ is

record Eff {m n β} {ρs : Level ^ n} {αεs : Level ²^ n}
           (Ψs : Effects ρs αεs) (Rs : Resources ρs)
           (B : Set β) (Rs′ : B -> Resources ρs)
           (is : Fin n ^ m) : Set (effˡ ρs αεs β is) where
  constructor wrap
  field unwrap : Eff⁻ Ψs Rs B Rs′ is
open Eff public
```

It's the same `Eff` as before, but defined as a function (like in the case of fully universe polymorphic [`HList`](http://lpaste.net/145163)) parametrised by eta-friendly vectors of levels (I always make vectors of levels eta-friendly, even if it's not needed right now).

With the current definition we can't express non-determinism, because `Eff⁻` is defined by induction on `is`.

```
mplus : Eff Ψs Rs A Rs′ is -> Eff Ψs Rs A Rs′ js -> Eff Ψs Rs A Rs′ {!!}
```

What's there in `{!!}`? It's either `is` or `js`, but we can't even say that, because it immediately causes the Setω error.

I'm revising the implementation, but stuck due to [this](https://github.com/agda/agda/issues/1757) bug.

For a readable, but not fully universe polymorphic machinery look [here](https://github.com/effectfully/random-stuff/tree/master/MonoEff).