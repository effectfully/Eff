module Examples.Resources.TicTacToe.TestSafe where

open import Examples.Resources.TicTacToe.Prelude
open import Examples.Resources.TicTacToe.SafeGame 3 3

-- x--
-- ox-
-- o-x
test₁ : Maybe GameOver
test₁ = simulate $ (0 , 0) ∷ (1 , 0) ∷ (1 , 1) ∷ (2 , 0) ∷ (2 , 2) ∷ []

-- xox
-- oxx
-- oxo
test₂ : Maybe GameOver
test₂ = simulate $
  (0 , 0) ∷ (1 , 0) ∷ (1 , 1) ∷ (2 , 0) ∷ (2 , 1) ∷ (2 , 2) ∷ (1 , 2) ∷ (0 , 1) ∷ (0 , 2) ∷ []

-- xox
-- oxx
-- xoo
test₃ : Maybe GameOver
test₃ = simulate $
  (0 , 0) ∷ (1 , 0) ∷ (1 , 1) ∷ (2 , 1) ∷ (2 , 0) ∷ (2 , 2) ∷ (1 , 2) ∷ (0 , 1) ∷ (0 , 2) ∷ []

-- oo-
-- xx-
-- ---
test₄ : Maybe GameOver
test₄ = simulate $ (1 , 0) ∷ (0 , 0) ∷ (1 , 2) ∷ (0 , 1) ∷ []

-- oo-
-- xxx
-- ---
test₅ : Maybe GameOver
test₅ = simulate $ (1 , 0) ∷ (0 , 0) ∷ (1 , 2) ∷ (0 , 1) ∷ (1 , 1) ∷ []
