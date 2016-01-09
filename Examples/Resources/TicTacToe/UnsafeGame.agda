open import Examples.Resources.TicTacToe.Prelude

module Examples.Resources.TicTacToe.UnsafeGame (n m : ℕ) where

open import Examples.Resources.TicTacToe.Core n m public

open import Resources.Effect.Error
open import Resources.Effect.LiftM

data GetCoord s : Set where
  Interrupted : GetCoord s 
  Bounds      : ∀ {c}
              ->  (Σ (InBounds n c) λ ib -> Contents (get (runInBounds ib) (board s)))
                 ⊎ OutOfBounds n c
              -> GetCoord s

data Raised : Set where
  InterruptedR : Raised
  OutOfBoundsR : ∀ {c} -> OutOfBounds n c -> Raised
  FilledR      : ∀ c b -> Filled (get c b) -> Raised

prettyRaised : Raised -> String
prettyRaised  InterruptedR     = "interrupted"
prettyRaised (OutOfBoundsR ob) = "out of bounds"
prettyRaised (FilledR c b f)   = "this cell is already filled"

runGetCoord : ∀ {s} -> Moveable s -> GetCoord s -> GameState
runGetCoord     m (Bounds (inj₁ (inBounds c _ , inj₁ e))) = moveMoveable m (emptyAt c e)
runGetCoord {s} m  _                                      = s

data Game (s : GameState) : Effectful lzero lzero where
  Move : (m : Moveable s) -> Game s (GetCoord s) (runGetCoord m)

move : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
         {Ψs : Effects Rs αψs} {rs : Resources Rs} {s} {{q : Game , s ∈ Ψs , rs}}
     -> (m : Moveable s) -> Eff Ψs (GetCoord s) rs _
move = invoke′ ∘′ Move

Play : GameState -> Set₁
Play s = Eff (       Error {lzero} , Game    , tt)
              GameOver
             (       Raised        , s       , tt)
             (λ g -> Raised        , state g , tt)

{-# TERMINATING #-}
game : ∀ s -> Play s
game s with moveability s
... | inj₁ nm = return $ gameOver $ Draw nm
... | inj₂  m = move m >>= k where
  k : ∀ gc -> Play (runGetCoord m gc)
  k  Interrupted                            = throw′  InterruptedR
  k (Bounds (inj₂  ob))                     = throw′ (OutOfBoundsR ob)
  k (Bounds (inj₁ (inBounds c _ , inj₂ f))) = throw′ (FilledR c _ f)
  k (Bounds (inj₁ (inBounds c _ , inj₁ e))) =
    if′ checkAround c _
      then return ∘′ gameOver ∘ Victory c
      else const (game _)

new : Play _
new = game $ State: (n * n) x (replicate (replicate empty))

Played : GameState -> Set₁
Played s = Eff (       Lift[ IO ] , Game    , tt)
                GameOver
               (       tt         , s       , tt)
               (λ g -> tt         , state g , tt)

{-# NON_TERMINATING #-}
play : ∀ {s} -> Play s -> Played s
play g = handleError g λ{ {s , _} r -> liftM IO (putStrLn (prettyRaised r)) >> play (game s) }

{-# NON_TERMINATING #-}
getCoord : IO (ℕ × ℕ)
getCoord = putStrLn "enter coordinates" >>ᵢₒ
           getLine >>=ᵢₒ λ s ->
             maybe′  returnᵢₒ
                    (putStrLn "wrong input, try again" >>ᵢₒ getCoord)
                    (List→× (lmap fromDigits (groupMaybe charToℕ (fromColist s))))

{-# NON_TERMINATING #-}
runPlayed : ∀ {s} -> Played s -> IO GameOver
runPlayed = runEffM returnᵢₒ _>>=ᵢₒ_ k where
  k : ∀ i {r A r′} -> lookupᵉ i (Lift[ IO ] , Game , tt) r A r′ -> IO A
  k  zero          (LiftM a) = a
  k (suc zero)     (Move m)  =
    getCoord >>=ᵢₒ λ p ->
      returnᵢₒ $ Bounds $
        [ inj₂
        , inj₁ ∘ < id , contents ∘′ flip get _ ∘′ runInBounds >
        ]′ (inBounds? n p)
  k (suc (suc ()))  a
