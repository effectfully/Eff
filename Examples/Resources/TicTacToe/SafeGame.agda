open import Resources hiding ([_])

module Examples.Resources.TicTacToe.SafeGame (n : ℕ) (m : ℕ) where

open import Examples.Resources.TicTacToe.Core n m public

import Data.Vec as V
import Data.String.Base

data Game (s : GameState) : Effectful lzero lzero where
  Move : Game s Coord (moveOnDef s)

move : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
         {Ψs : Effects Rs αψs} {rs : Resources Rs}
     -> ∀ s {{q : Game , s ∈ Ψs , rs}} -> Eff Ψs Coord rs _
move _ = invoke′ Move

Play : GameState -> Set₁
Play s = Eff (Game , tt) GameOver (s , tt) (λ g -> state g , tt)

{-# TERMINATING #-}
game : ∀ s -> Play s
game (State:  0      p b) = return $ record { result = Draw refl }
game (State: (suc n) p b) = move s >>= k where
  s = State: (suc n) p b

  k : ∀ c -> Play (moveOnDef s c)
  k c = if′ checkAround c (set c p b)
          then (λ ch -> return $ record { result = Victory c ch })
          else (λ _  -> game _)

new : Play _
new = game $ State: (n * n) x (V.replicate (V.replicate empty))

{-# TERMINATING #-}
execGame : ∀ {s} -> List (ℕ × ℕ) -> Play s -> Maybe GameOver
execGame     [] (return g) = just g
execGame     _  (return g) = nothing
execGame {s} ms (call i p) with runLifts i p
... | , , a , f with i
... | suc ()
... | zero   with a
... | Move with ms
... | []      = nothing
... | m ∷ ms' with attempt m (board s)
... | InBoundsA c _ (inj₂ _) = execGame ms' (f c)
... | _                      = nothing

simulate : List (ℕ × ℕ) -> Maybe GameOver
simulate ms = execGame ms new

postulate
  IO : Set -> Set
  _`bind`_ : ∀ {A B} -> IO A -> (A -> IO B) -> IO B
  readLn : ∀ {A} -> IO A
  print  : {A : Set} -> A -> IO ⊤

{-# NON_TERMINATING #-}
execGameIO : ∀ {b} -> Play b -> IO ⊤
execGameIO     (return y) = print y
execGameIO {s} (call i p) with runLifts i p
... | , , a , f with i
... | suc ()
... | zero   with a
... | Move = readLn `bind` λ m -> case attempt m (board s) of λ
  { (InBoundsA c _ (inj₂ _)) -> execGameIO (f c)
  ;  _                       -> print "You and your friends are dead."
  }
