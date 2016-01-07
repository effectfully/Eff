module Examples.Resources.TicTacToe.Core where

open import Resources

open import Relation.Nullary.Decidable hiding (True)
open import Relation.Binary.PropositionalEquality renaming ([_] to hide) using ()
open import Data.Fin using (toℕ; inject₁)
open import Data.Vec as V hiding ([_]; _>>=_; _⊛_)

suc-inj : ∀ {n} {i j : Fin n} -> Fin.suc i ≡ suc j -> i ≡ j
suc-inj refl = refl

fromInj₂ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ}
             {f : A -> C} {g : B -> D} {z}
         -> ∀ s -> smap f g s ≡ inj₂ z -> B
fromInj₂ (inj₁ x) ()
fromInj₂ (inj₂ y) p  = y

uninj₂ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ} {g : B -> D} {z}
       -> (f : A -> C) -> ∀ s -> (p : smap f g s ≡ inj₂ z) -> g (fromInj₂ s p) ≡ z
uninj₂ f (inj₁ x) ()
uninj₂ f (inj₂ y) refl = refl

back-inj₂ : ∀ {α β γ δ} {A : Set α} {B : Set β} {C : Set γ} {D : Set δ}
              {f : A -> C} {g : B -> D} {z w}
          -> ∀ s -> (p : smap f g s ≡ inj₂ z) -> fromInj₂ s p ≡ w -> s ≡ inj₂ w
back-inj₂ (inj₁ x) () q
back-inj₂ (inj₂ y) p  refl = refl

mpred : ∀ {n} -> Fin n -> Maybe (Fin n)
mpred  zero   = nothing
mpred (suc i) = just (inject₁ i)

msuc : ∀ {n} -> Fin n -> Maybe (Fin n)
msuc {1}            zero   = nothing
msuc {suc (suc _)}  zero   = just (suc zero)
msuc               (suc i) = fmap suc (msuc i)

sfromℕ : ∀ {n} m -> n ≤ m ⊎ Fin n
sfromℕ {0}      m      = inj₁ z≤n
sfromℕ {suc n}  0      = inj₂ zero
sfromℕ {suc n} (suc m) = smap s≤s suc (sfromℕ m)

sfromℕ→toℕ : ∀ {n i} m -> sfromℕ {n} m ≡ inj₂ i -> m ≡ toℕ i
sfromℕ→toℕ {i = zero}   0      p  = refl
sfromℕ→toℕ {i = suc i}  0      ()
sfromℕ→toℕ {i = zero}  (suc m) p  = case uninj₂ s≤s (sfromℕ m) p of λ()
sfromℕ→toℕ {i = suc i} (suc m) p  =
  cong suc (sfromℕ→toℕ m (back-inj₂ (sfromℕ m) p (suc-inj (uninj₂ s≤s (sfromℕ m) p))))

data OutOfBounds n p : Set where
  outOfBoundsₗ : n ≤ proj₁ p -> OutOfBounds n p
  outOfBoundsᵣ : n ≤ proj₂ p -> OutOfBounds n p

data InBounds n p : Set where
  inBounds : (pᵢ : Fin n × Fin n) -> p ≡ pmap toℕ toℕ pᵢ -> InBounds n p

inBounds? : ∀ n p -> OutOfBounds n p ⊎ InBounds n p
inBounds? n (m , p) with sfromℕ {n} m | inspect (sfromℕ {n}) m
... | inj₁ le₁ | hide r = inj₁ (outOfBoundsₗ le₁)
... | inj₂ i   | hide r with sfromℕ {n} p | inspect (sfromℕ {n}) p
... | inj₁ le₂ | hide s = inj₁ (outOfBoundsᵣ le₂)
... | inj₂ j   | hide s = inj₂ (inBounds (i , j) (cong₂ _,_ (sfromℕ→toℕ m r) (sfromℕ→toℕ p s)))

mapᵢ : ∀ {n α} {A : Set α} -> Fin n -> (A -> A) -> Vec A n -> Vec A n
mapᵢ  zero   f (x ∷ xs) = f x ∷ xs
mapᵢ (suc i) f (x ∷ xs) = x   ∷ mapᵢ i f xs

--------------------

module InitGame (n m : ℕ) where

  data Player : Set where
    x o : Player

  data Cell : Set where
    empty  : Cell
    filled : Player -> Cell

  data Empty : Cell -> Set where
     really : Empty empty

  data Filled : Cell -> Set where
    player : ∀ p -> Filled (filled p)

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

  empty? : ∀ c -> Empty c ⊎ Filled c
  empty?  empty     = inj₁  really
  empty? (filled p) = inj₂ (player p)

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
  next (δᵢ , δⱼ) (i , j) = _,_ ⟨$⟩ add δᵢ i ⊛ add δⱼ j where
    open import Data.Maybe
    open import Category.Monad
    open RawMonad {lzero} monad renaming (_<$>_ to _⟨$⟩_)

  get : Coord -> Board -> Cell
  get (i , j) = V.lookup j ∘ V.lookup i

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

  moveable? : ∀ s -> Non-moveable s ⊎ Moveable s
  moveable? (State:  0      p b) = inj₁ (non-moveable p b)
  moveable? (State: (suc n) p b) = inj₂ (moveable n p b)

  moveMoveable : ∀ {s} -> Moveable s -> EmptyCoord s -> GameState
  moveMoveable (moveable n p b) (emptyAt c _) = State: n (switch p) (set c p b)
