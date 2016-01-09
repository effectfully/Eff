open import Examples.Resources.TicTacToe.Prelude

module Examples.Resources.TicTacToe.SafeGame (n : ℕ) (m : ℕ) where

open import Examples.Resources.TicTacToe.Core n m public

data Game (s : GameState) : Effectful lzero lzero where
  Move : (m : Moveable s) -> Game s (EmptyCoord s) (moveMoveable m)

move : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
         {Ψs : Effects Rs αψs} {rs : Resources Rs} {s} {{q : Game , s ∈ Ψs , rs}}
     -> (m : Moveable s) -> Eff Ψs _ rs _
move = invoke′ ∘′ Move

Play : GameState -> Set₁
Play s = Eff (Game , tt) GameOver (s , tt) (λ g -> state g , tt)

{-# TERMINATING #-}
game : ∀ s -> Play s
game s with moveability s
... | inj₁ nm = return $ gameOver $ Draw nm
... | inj₂  m = move m >>= k where
  k : ∀ ec -> Play (moveMoveable m ec)
  k (emptyAt c _) = if′ checkAround c _
                      then return ∘′ gameOver ∘ Victory c
                      else const (game _)

new : Play _
new = game $ State: (n * n) x (replicate (replicate empty))

{-# TERMINATING #-}
execGame : ∀ {s} -> List (ℕ × ℕ) -> Play s -> Maybe GameOver
execGame     [] (return g) = just g
execGame     _  (return g) = nothing
execGame {s} ms (call i p) with runLifts i p
... | , , a , f with i
... | suc ()
... | zero   with a
... | Move _ with ms
... | []      = nothing
... | m ∷ ms' with inBounds? n m
... | inj₁  _             = nothing
... | inj₂ (inBounds c _) with contents (get c (board s))
... | inj₁ e = execGame ms' (f (emptyAt c e))
... | inj₂ _ = nothing

simulate : List (ℕ × ℕ) -> Maybe GameOver
simulate ms = execGame ms new
