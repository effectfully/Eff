open import Examples.Resources.TicTacToe.Prelude

module Examples.Resources.TicTacToe.Core (n m : ℕ) where

data Player : Set where
  x o : Player

data Cell : Set where
  empty  : Cell
  filled : Player -> Cell

data Empty : Cell -> Set where
   really : Empty empty

data Filled : Cell -> Set where
  player : ∀ p -> Filled (filled p)

Contents : Cell -> Set
Contents c = Empty c ⊎ Filled c

data Δ : Set where
  -1ᵈ 0ᵈ +1ᵈ : Δ

Board     = Vec (Vec Cell n) n
Coord     = Fin n × Fin n
Direction = Δ × Δ

switch : Player -> Player
switch x = o
switch o = x

_==ᵖ_ : Player -> Player -> Bool
x ==ᵖ x = true
o ==ᵖ o = true
_ ==ᵖ _ = false

contents : ∀ c -> Contents c
contents  empty     = inj₁  really
contents (filled p) = inj₂ (player p)

revert : Δ -> Δ
revert -1ᵈ = +1ᵈ
revert  0ᵈ = 0ᵈ
revert +1ᵈ = -1ᵈ

opposite : Direction -> Direction
opposite = pmap revert revert

add : ∀ {n} -> Δ -> Fin n -> Maybe (Fin n)
add -1ᵈ i = mpred i
add  0ᵈ i = just  i
add +1ᵈ i = msuc  i

next : Direction -> Coord -> Maybe Coord
next (δᵢ , δⱼ) (i , j) = _,_ <$>ₘ add δᵢ i <*>ₘ add δⱼ j

get : Coord -> Board -> Cell
get (i , j) = vlookup j ∘ vlookup i

set : Coord -> Player -> Board -> Board
set (i , j) = mapᵢ i ∘ mapᵢ j ∘ const ∘ filled

{-# TERMINATING #-}
line : Direction -> Coord -> Board -> List Cell
line d c b = maybe′ (λ c' -> get c' b ∷ line d c' b) [] (next d c)

lineOf : Player -> Direction -> Coord -> Board -> List Cell
lineOf p d c b = takeWhile (λ{ empty -> false ; (filled q) -> p ==ᵖ q }) (line d c b)

checkDirection : Coord -> Board -> Direction -> Bool
checkDirection c b d with get c b
... | empty    = false
... | filled p = ⌊ m ≤? length cs ⌋ where
  cs = lineOf p d c b l++ [ filled p ] l++ lineOf p (opposite d) c b

directions : List Direction
directions = (-1ᵈ , -1ᵈ)
           ∷ (-1ᵈ ,  0ᵈ)
           ∷ (-1ᵈ , +1ᵈ)
           ∷ ( 0ᵈ , +1ᵈ)
           ∷ []

checkAround : Coord -> Board -> Bool
checkAround c b = any (checkDirection c b) directions

--------------------

record GameState : Set where
  constructor State:
  field
    moves : ℕ
    turn  : Player
    board : Board
open GameState public

data Non-moveable : GameState -> Set where
  non-moveable : ∀ p b -> Non-moveable (State: 0 p b)

data Moveable : GameState -> Set where
  moveable : ∀ n p b -> Moveable (State: (suc n) p b)

Moveability : GameState -> Set
Moveability s = Non-moveable s ⊎ Moveable s

data EmptyCoord s : Set where
  emptyAt : ∀ c -> Empty (get c (board s)) -> EmptyCoord s

data Outcome s : Set where
  Victory : ∀ c -> True (checkAround c (board s)) -> Outcome s
  Draw    : Non-moveable s -> Outcome s

record GameOver : Set where
  constructor gameOver
  field
    {state} : GameState
    result  : Outcome state
open GameOver public

moveability : ∀ s -> Moveability s
moveability (State:  0      p b) = inj₁ (non-moveable p b)
moveability (State: (suc n) p b) = inj₂ (moveable n p b)

moveMoveable : ∀ {s} -> Moveable s -> EmptyCoord s -> GameState
moveMoveable (moveable n p b) (emptyAt c _) = State: n (switch p) (set c p b)

--------------------

showPlayer : Player -> Char
showPlayer x = 'x'
showPlayer o = 'o'

showCell : Cell -> Char
showCell  empty     = '-'
showCell (filled p) = showPlayer p

showBoard : Board -> String
showBoard = unlines ∘ vtoList ∘ vmap (vecToString ∘ vmap showCell)

showGameOver : GameOver -> String
showGameOver (gameOver {s} (Victory c _)) =
      "the winner is "
  s++ fromList (showCell (get c (board s)) ∷ '\n' ∷ '\n' ∷ [])
  s++ showBoard (board s)
showGameOver (gameOver {s} (Draw _))      =
      "it's draw\n\n"
   s++ showBoard (board s)
