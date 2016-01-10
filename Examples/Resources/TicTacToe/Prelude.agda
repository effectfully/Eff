module Examples.Resources.TicTacToe.Prelude where

open import Resources hiding (replicate) public

open import Relation.Nullary.Decidable using (⌊_⌋) public
open import Data.Char.Base public
open import Data.Vec as Vec using (Vec; []; _∷_; replicate)
  renaming (toList to vtoList; map to vmap; lookup to vlookup) public
open import Data.String using (String; Costring; toCostring; toList; fromList; unlines)
  renaming (_++_ to _s++_) public
open import IO.Primitive
  renaming (return to returnᵢₒ; _>>=_ to _>>=ᵢₒ_;
            putStr to putCostr; putStrLn to putCostrLn) public

open import Coinduction
open import Relation.Binary.PropositionalEquality renaming ([_] to hide) using ()
open import Data.Char
open import Data.Fin using (toℕ; inject₁)
open import Data.Colist hiding (fromList)

postulate getLine : IO Costring
{-# COMPILED getLine getLine #-}

infixr 2 _>>ᵢₒ_
infixl 6 _<$>ᵢₒ_

{-# NON_TERMINATING #-}
fromColist : ∀ {α} {A : Set α} -> Colist A -> List A
fromColist  []      = []
fromColist (x ∷ xs) = x ∷ fromColist (♭ xs)

_>>ᵢₒ_ : ∀ {α β} {A : Set α} {B : Set β} -> IO A -> IO B -> IO B
a >>ᵢₒ b = a >>=ᵢₒ const b

_<$>ᵢₒ_ : ∀ {α β} {A : Set α} {B : Set β} -> (A -> B) -> IO A -> IO B
f <$>ᵢₒ a = a >>=ᵢₒ returnᵢₒ ∘ f

putStrLn : String -> IO _
putStrLn = putCostrLn ∘ toCostring

putStr : String -> IO _
putStr = putCostr ∘ toCostring

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
msuc               (suc i) = suc <$>ₘ msuc i

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

record InBounds n p : Set where
  constructor inBounds
  field
    runInBounds : Fin n × Fin n
    isInBounds  : p ≡ pmap toℕ toℕ runInBounds
open InBounds public

inBounds? : ∀ n p -> OutOfBounds n p ⊎ InBounds n p
inBounds? n (m , p) with sfromℕ {n} m | inspect (sfromℕ {n}) m
... | inj₁ le₁ | hide r = inj₁ (outOfBoundsₗ le₁)
... | inj₂ i   | hide r with sfromℕ {n} p | inspect (sfromℕ {n}) p
... | inj₁ le₂ | hide s = inj₁ (outOfBoundsᵣ le₂)
... | inj₂ j   | hide s = inj₂ (inBounds (i , j) (cong₂ _,_ (sfromℕ→toℕ m r) (sfromℕ→toℕ p s)))

mapᵢ : ∀ {n α} {A : Set α} -> Fin n -> (A -> A) -> Vec A n -> Vec A n
mapᵢ  zero   f (x ∷ xs) = f x ∷ xs
mapᵢ (suc i) f (x ∷ xs) = x   ∷ mapᵢ i f xs

vecToString : ∀ {n} -> Vec Char n -> String
vecToString = fromList ∘ Vec.toList

fromDigits : List ℕ -> ℕ
fromDigits = foldl (λ a d -> a * 10 + d) 0

_∺_ : ∀ {α} {A : Set α} -> List A -> List (List A) -> List (List A)
[] ∺ xss = xss
xs ∺ xss = xs ∷ xss

groupMaybe : ∀ {α β} {A : Set α} {B : Set β} -> (A -> Maybe B) -> List A -> List (List B)
groupMaybe {A = A} {B} f = uncurry′ _∺_ ∘ lfoldr step ([] , []) where
  step : A -> List B × List (List B) -> List B × List (List B)
  step x (ys , yss) = maybe′ (λ y -> y ∷ ys , yss) ([] , ys ∺ yss) (f x)

List→× : ∀ {α} {A : Set α} -> List A -> Maybe (A × A)
List→× (x ∷ y ∷ []) = just (x , y)
List→×  _           = nothing

charToℕ : Char -> Maybe ℕ
charToℕ '0' = just 0
charToℕ '1' = just 1
charToℕ '2' = just 2
charToℕ '3' = just 3
charToℕ '4' = just 4
charToℕ '5' = just 5
charToℕ '6' = just 6
charToℕ '7' = just 7
charToℕ '8' = just 8
charToℕ '9' = just 9
charToℕ  _  = nothing

readℕ : String -> Maybe ℕ
readℕ = (fromDigits <$>ₘ_) ∘ sequence monad ∘ lmap charToℕ ∘ toList where
  open import Data.List  using (sequence)
  open import Data.Maybe using (monad)

words : List Char -> List (List Char)
words = groupMaybe (λ c -> if c == ' ' then nothing else just c)
