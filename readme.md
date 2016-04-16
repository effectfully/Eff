# Eff

Most of the code is about constructing a fully universe polymorphic effect system in Agda. It's unreadable as always with generic universe polymorphic stuff.

`Loop.Core` is the most readable version as it enables `--type-in-type`, so I'll describe its content rather than the content of `Resources.Core`, which is properly universe polymorphic and less powerful ("for historical reasons").

Effects are represented like in the Idris [Effects](https://github.com/edwinb/Eff-dev/blob/master/effects/Effects.idr) library, but resources are values rather than types:

```
Effect : Set -> Set
Effect R = R -> (A : Set) -> (A -> R) -> Set
```

Instead of defining `Eff` directly, we define the indexed version of the Oleg Kiselyov's [`Freer`](http://okmij.org/ftp/Haskell/extensible/more.pdf) monad, which is an effect transformer:

```
data IFreer {R : Set} (Ψ : Effect R) : Effect R where
  return : ∀ {B r′} y -> IFreer Ψ (r′ y) B r′
  call   : ∀ {r A r′ B r′′} -> Ψ r A r′ -> (∀ x -> IFreer Ψ (r′ x) B r′′) -> IFreer Ψ r B r′′
```

As well as `Eff` in Idris it's a Hoare state monad (HST in [Verifying Higher-order Programs with the Dijkstra Monad](http://research.microsoft.com/en-us/um/people/nswamy/papers/dijkstra-submitted-pldi13.pdf)) as witnessed by

```
_>>=_ : ∀ {R Ψ r B r′ C r′′}
      -> IFreer {R} Ψ r B r′ -> (∀ y -> IFreer Ψ (r′ y) C r′′) -> IFreer Ψ r C r′′
return y >>= g = g y
call a f >>= g = call a λ x -> f x >>= g
```

We also have higher effects which operate on lists of simple effects and transform heterogeneous lists of resources:

```
Resources = HList

Effects : Sets -> Set
Effects = List₁ Effect

HigherEffect : Set
HigherEffect = ∀ {Rs} -> Effects Rs -> Effect (Resources Rs)
```

The union of a list of effects is a higher effect:

```
data Unionᵉ : HigherEffect where
  hereᵉ  : ∀ {R Rs r A r′ rs}  {Ψ : Effect R} {Ψs : Effects Rs}
         -> Ψ r A r′ -> Unionᵉ (Ψ , Ψs) (r , rs) A (λ x -> r′ x , rs)
  thereᵉ : ∀ {R Rs r A rs rs′} {Ψ : Effect R} {Ψs : Effects Rs}
         -> Unionᵉ Ψs rs A rs′ -> Unionᵉ (Ψ , Ψs) (r , rs) A (λ x -> r , rs′ x)
```

`Unionʰᵉ` unions a list of higher effects:

```
data Unionʰᵉ : HigherEffects -> HigherEffect where
  hereʰᵉ   : ∀ {Φs Rs rs A rs′} {Φ : HigherEffect} {Ψs : Effects Rs}
           -> Φ {Rs} Ψs rs A rs′ -> Unionʰᵉ (Φ ∷ Φs) Ψs rs A rs′
  thereʰᵉ  : ∀ {Φs Rs rs A rs′} {Φ : HigherEffect} {Ψs : Effects Rs}
           -> Unionʰᵉ Φs Ψs rs A rs′ -> Unionʰᵉ (Φ ∷ Φs) Ψs rs A rs′
```

Here is the main definition:

```
EEffOver : HigherEffects -> HigherEffect
EffOver Φs Ψs = IFreer (Unionʰᵉ (Unionᵉ ∷ Φs) Ψs)
```

`EffOver` describes computations over a list of higher effects `Φs` and a list of simple effects `Ψs`.

The usual `Eff` is recovered by

```
Eff : HigherEffect
Eff = EffOver []
```

I.e. no higher effects except for the union of simple effects.

So while a computation can't change the set of effects like in in Idris, it can change the resources. A canonical example is the indexed `State`:

```
test : Eff (State , tt) (ℕ , tt) ℕ (λ n -> V.Vec Bool n , tt)
test = get >>= λ n -> put (V.replicate true) >> return n
```

(`put` is `zap ℕ` actually, because instance search needs an additional hint in this case)

So we start from `State ℕ` and get `State (Vec Bool n)`, where `n` comes from `State ℕ`.

We can run this computation:

```
test-test : runEff (execState 3 test) ≡ (3 , true ∷ true ∷ true ∷ [])
test-test = refl
```

There is also an effectful [tic-tac-toe](https://github.com/effectfully/Eff/blob/master/Examples/Resources/TicTacToe/UnsafeGame.agda) game that [compiles](https://github.com/effectfully/Eff/blob/master/Examples/Resources/TicTacToe/Main.agda).