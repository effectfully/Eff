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
  RInterrupted : Raised
  ROutOfBounds : ∀ {c} -> OutOfBounds n c -> Raised
  RFilled      : ∀ c b -> Filled (get c b) -> Raised

prettyRaised : Raised -> String
prettyRaised  RInterrupted     = "interrupted"
prettyRaised (ROutOfBounds ob) = "out of bounds"
prettyRaised (RFilled c b f)   = "this cell is already filled"

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
  k  Interrupted                            = throw  RInterrupted
  k (Bounds (inj₂  ob))                     = throw (ROutOfBounds ob)
  k (Bounds (inj₁ (inBounds c _ , inj₂ f))) = throw (RFilled c _ f)
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
               
{-# TERMINATING #-}
play : ∀ {s} -> Play s -> Played s
play g = handleError g λ
  { {s , _} r -> (case r of λ
       { RInterrupted -> liftM IO $ putStrLn
           "naughty boy, you can't interrupt the game -- that's what the type signature says"
       ; _            -> liftM IO $ putStrLn $ prettyRaised r
       }) >> play (game s)
  }

data Command s : Set where
  CShow  : Command s
  CCoord : GetCoord s -> Command s

parseCommand : ∀ {s} -> List Char -> Maybe (Command s)
parseCommand cs = case ws of λ
  { ("show" ∷ [])           -> just  CShow
  ; ("interrupt" ∷ [])      -> just (CCoord Interrupted)
  ; ("move" ∷ w1 ∷ w2 ∷ []) ->
    (λ m1 m2 -> CCoord ∘ Bounds $
         [ inj₂
         , inj₁ ∘ < id , contents ∘′ flip get _ ∘′ runInBounds >
         ]′ (inBounds? n (m1 , m2)))
       <$>ₘ readℕ w1
       <*>ₘ readℕ w2
  ; _                       -> nothing
  } where ws = lmap fromList $ words cs

mutual
  {-# NON_TERMINATING #-}
  getCoord : ∀ {s} -> IO (GetCoord s)
  getCoord = putStrLn "enter command" >>ᵢₒ
             getLine                  >>=ᵢₒ λ s ->
             maybe′  runCommand
                    (putStrLn "wrong input, try again" >>ᵢₒ getCoord)
                    (parseCommand (fromColist s))
             
  runCommand : ∀ {s} -> Command s -> IO (GetCoord s)
  runCommand {s}  CShow     = putStr (showBoard (board s)) >>ᵢₒ getCoord
  runCommand     (CCoord c) = returnᵢₒ c

{-# NON_TERMINATING #-}
runPlayed : ∀ {s} -> Played s -> IO GameOver
runPlayed {s} = runEffM returnᵢₒ _>>=ᵢₒ_ k where
  k : ∀ i {s' A r′} -> lookupᵉ i (Lift[ IO ] , Game , tt) s' A r′ -> IO A
  k  zero          (LiftM a) = a
  k (suc zero)     (Move m)  = getCoord
  k (suc (suc ()))  a
