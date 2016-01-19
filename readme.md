# Eff

Most of the code is about constructing a fully universe polymorphic effect system in Agda. It's unreadable as always with generic universe polymorphic stuff.

`Loop.Core` is the most readable version as it enables `--type-in-type`, so I'll describe its content rather than the content of `Resources.Core`, which is properly universe polymorphic and less powerful ("for historical reasons").

Effects are represented like in the Idris [Effects](https://github.com/edwinb/Eff-dev/blob/master/effects/Effects.idr) library, but resources are values rather than types:

```
Effect : Set -> Set
Effect R = R -> (A : Set) -> (A -> R) -> Set
```

Instead of defining `Eff` directly, we define the indexed version of the Oleg Kiselyov's [`Freer`](http://okmij.org/ftp/Haskell/extensible/more.pdf)) monad, which is an effect transformer:

```
data IFreer {R : Set} (Ψ : Effect R) : Effect R where
  return : ∀ {B r′} y -> IFreer Ψ (r′ y) B r′
  call   : ∀ {r A r′ B r′′} -> Ψ r A r′ -> (∀ x -> IFreer Ψ (r′ x) B r′′) -> IFreer Ψ r B r′′
```

As well as `Eff` in Idris it's a Hoare state monad (HST in [Verifying Higher-order Programs with the Dijkstra Monad](http://research.microsoft.com/en-us/um/people/nswamy/papers/dijkstra-submitted-pldi13.pdf) as witnessed by

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
Unionᵉ : HigherEffect
Unionᵉ {[]}     tt       tt      A rs′ = ⊥
Unionᵉ {_ ∷ _} (Ψ , Ψs) (r , rs) A rs′ =        Ψ  r  A (head₁ ∘ rs′)
                                       ⊎ Unionᵉ Ψs rs A (tail₁ ∘ rs′)
```

`Unionᵒᵉ` unions a list of higher effects:

```
_⊎ᵒᵉ_ : HigherEffect -> HigherEffect -> HigherEffect
(Φ ⊎ᵒᵉ Ξ) Ψs rs A rs′ = Φ Ψs rs A rs′ ⊎ Ξ Ψs rs A rs′

Unionᵒᵉ : HigherEffects -> HigherEffect
Unionᵒᵉ = lfoldr _⊎ᵒᵉ_ (λ _ _ _ _ -> ⊥)
```

Here is the main definition (`WUnionᵒᵉ` is a dummy wraper over `Unionᵒᵉ` that helps inference):

```
EffOver : HigherEffects -> HigherEffect
EffOver Φs Ψs = IFreer (WUnionᵒᵉ (Unionᵉ ∷ Φs) Ψs)
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

There is also an effectful [tic-tac-toe](https://github.com/effectfully/Eff/blob/master/Examples/Resources/TicTacToe/UnsafeGame.agda) game that [compiles](https://github.com/effectfully/Eff/blob/master/Examples/Resources/TicTacToe/Main.agda).