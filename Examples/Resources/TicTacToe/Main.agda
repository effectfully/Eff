module Examples.Resources.TicTacToe.Main where

open import Examples.Resources.TicTacToe.Prelude
open import Examples.Resources.TicTacToe.UnsafeGame 3 3

main = runPlayed (play new) >>=ᵢₒ putStrLn ∘ showGameOver
