open import Resources

module Examples.Resources.TicTacToe.SafeGame (n : ℕ) (m : ℕ) where

open import Examples.Resources.TicTacToe.Core n m public

import Data.Vec as V
import Data.String.Base

data Moved p b : Set where
  moved : (c : Coord) -> Is (set c p b) -> Moved p b

runMoved : ∀ {p b} -> Moved p b -> Board
runMoved (moved c !b) = ¡ !b

data Game (b : Board) : Effectful Board lzero lzero where
  Move : ∀ p -> Game b (Moved p b) runMoved

move : ∀ {n} {ρs : Level ^ n} {αψs : Level ²^ n} {Rs : Sets ρs}
         {Ψs : Effects Rs αψs} {rs : Resources Rs}
     -> ∀ p b {{q : Game , b ∈ Ψs , rs}} -> Eff Ψs (Moved p b) rs _
move p b = invoke′ (Move p)

Play : Board -> Set₁
Play b = Eff (Game , tt) GameOver (b , tt) (λ g -> board g , tt)

postulate
  undefined : {A : Set} -> A

game-go : ℕ -> Player -> (b : Board) -> Play b
game-go  0      p b = return $ record { result = Draw undefined }
game-go (suc n) p b = move p b >>= k where
  k : ∀ {p} -> (m : Moved p b) -> Play (runMoved m)
  k (moved c !b) = if′ checkAround c (¡ !b)
                     then (λ ch -> return $ record { result = Victory c ch })
                     else (λ _ -> game-go n (switch p) (¡ !b))

game : Play _
game = game-go (n * n) x (V.replicate (V.replicate empty))

{-# TERMINATING #-}
execGame : ∀ {b} -> List (ℕ × ℕ) -> Play b -> GameOver
execGame     ms (return g) = g
execGame {b} ms (call i p) with runLifts i p
... | , , a , f with i
... | suc ()
... | zero   with a
... | Move q with ms
... | []      = undefined
... | m ∷ ms' with attempt {b} {q} m
... | InBoundsA c _ (inj₂ _) = execGame ms' (f (moved c _))
... | _                      = undefined

play : List (ℕ × ℕ) -> GameOver
play ms = execGame ms game

postulate
  IO : Set -> Set
  _`bind`_ : ∀ {A B} -> IO A -> (A -> IO B) -> IO B
  readLn : ∀ {A} -> IO A
  print  : {A : Set} -> A -> IO ⊤

{-# NON_TERMINATING #-}
execGameIO : ∀ {b} -> Play b -> IO ⊤
execGameIO     (return y) = print y
execGameIO {b} (call i p) with runLifts i p
... | , , a , f with i
... | suc ()
... | zero   with a
... | Move q = readLn `bind` λ m -> case attempt {b} {q} m of λ
  { (InBoundsA c _ (inj₂ _)) -> execGameIO (f (moved c _))
  ;  _                       -> print "You and your friends are dead."
  }
