module Examples.Resources.TicTacToe.TestSafe where

open import Prelude
open import Examples.Resources.TicTacToe.SafeGame 3 3

open import Examples.Resources.TicTacToe.Core using (board)

-- x--
-- ox-
-- o-x
test₁ : GameOver
test₁ = play $ (0 , 0) ∷ (1 , 0) ∷ (1 , 1) ∷ (2 , 0) ∷ (2 , 2) ∷ []

-- xox
-- oxx
-- oxo
test₂ : GameOver
test₂ = play $
  (0 , 0) ∷ (1 , 0) ∷ (1 , 1) ∷ (2 , 0) ∷ (2 , 1) ∷ (2 , 2) ∷ (1 , 2) ∷ (0 , 1) ∷ (0 , 2) ∷ []

-- xox
-- oxx
-- xoo
test₃ : GameOver
test₃ = play $
  (0 , 0) ∷ (1 , 0) ∷ (1 , 1) ∷ (2 , 1) ∷ (2 , 0) ∷ (2 , 2) ∷ (1 , 2) ∷ (0 , 1) ∷ (0 , 2) ∷ []

-- oo-
-- xxx
-- ---
test₄ : GameOver
test₄ = play $ (1 , 0) ∷ (0 , 0) ∷ (1 , 2) ∷ (0 , 1) ∷ (1 , 1) ∷ []
