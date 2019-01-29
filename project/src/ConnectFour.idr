module Main
import Data.Vect
import IdrisScript
import IdrisScript.Arrays
-- import ConnectFour.Structures.Square

%default total
%access public export


-- 1 2 3
-- 4 5 6
-- 7 8 9

-- the two transformations

-- x x 1 2 3
-- x 4 5 6 x
-- 7 8 9 x x 

-- 1 2 3 x x
-- x 4 5 6 x
-- x x 7 8 9

-- Generalizable sanity check

-- 1  2  3  4  
-- 5  6  7  8
-- 9  10 11 12
-- 13 14 15 16

-- 1  2  3  4  x  x  x
-- x  5  6  7  8  x  x
-- x  x  9  10 11 12 x
-- x  x  x  13 14 15 16


-- Or broken up into more steps
-- 1  2  3  4  x  x  x
-- 5  6  7  8  x  x  x
-- 9  10 11 12 x  x  x
-- 13 14 15 16 x  x  x

-- 1  2  3  4  x  x  x
-- roll 5  6  7  8  x  x  x
-- roll roll 9  10 11 12 x  x  x
-- roll roll roll 13 14 15 16 x  x  x

-- 1  2  3  4  x  x  x
-- x  5  6  7  8  x  x
-- x  x  9  10 11 12 x 
-- x  x  x  13 14 15 16

||| Roll a vector, transposing the last element to the front of the list.
roll : Vect (S n) t -> Vect (S n) t
roll vec = (last vec) :: (init vec)

||| Roll a vector, transposing the last element to the front of the list.
||| Has a more permissive signature.
roll' : {n : Nat} -> {auto smaller : LTE 1 n} -> Vect n t -> Vect n t
roll' {n} = case n of
  (S x) => roll {n = x}

-- -- Turning Vect n (Vect n x)
-- -- to Vect n (Vect (n + (n - 1)) (Maybe x))
-- -- where (n + (n - 1)) = (2n - 1)
-- -- first step: Make a blank board of nothing,
-- -- that the board will later be added to

||| Take a number, and return one less than twice that number
||| @ n a number that is greater than one
formula : (n : Nat) -> {auto smaller : LTE 1 n} -> Nat
formula (S n) = (S n) + n

-- 1 <= n
-- Multiply both sides by two
-- 2 <= 2n
-- Subtract one from each side
-- 1 <= 2n - 1

||| A lemma stating that when 1 is less than or equal to n,
||| 1 is less than or equal to n plus one
%hint
fstFortioriLTE : {n : Nat} -> LTE 1 n -> LTE 1 (n + 1)
fstFortioriLTE {n} pf = lteTransitive pf $ lteAddRight n

||| A lemma stating that when 1 is less than or equal to n,
||| 1 is less than or equal to one less than twice n
%hint
sndFortioriLTE : {n : Nat} -> LTE 1 n -> LTE 1 (formula n)
sndFortioriLTE {n} pf = case n of
  (S x) => lteTransitive pf $ lteAddRight (S x)

||| A lemma stating that when 1 is less than or equal to n,
||| 1 is less than or equal to n plus n
%hint
trdFortioriLTE : {n : Nat} -> LTE 1 n -> LTE 1 (n + n)
trdFortioriLTE {n} pf = lteTransitive pf $ lteAddRight n

||| Create a square of a size 1x1 or greater
||| @ n The size of the square, which must be greater than one.
Square : (n : Nat) -> {auto smaller : LTE 1 n} -> Type -> Type
Square n t = Vect n (Vect n t)

||| Roll a vector defined in terms of formula
rollf : {n : Nat} -> 
        {auto smaller : LTE 1 n} -> 
        Vect (formula n) t -> 
        Vect (formula n) t
rollf = roll'

||| A rectangle whose width is one less than twice its height
||| @ n the height of the rectangle
ExtendedSquare : (n : Nat) -> {auto smaller : LTE 1 n} -> Type -> Type
ExtendedSquare n t = Vect n (Vect (formula n) (Maybe t))

||| Wrap every element of a square into a just
toJustSquare : {auto smaller : LTE 1 n} -> Square n t -> Square n (Maybe t)
toJustSquare = map (\x => Just <$> x)

||| Extend a square of Justs into an ExtendedSquare
toExtendedSquare : {n : Nat} -> {auto smaller : LTE 1 n} -> 
                   Square n (Maybe t) -> ExtendedSquare n t
toExtendedSquare {n} = case n of
  (S plusSize) => ((\x => x ++ (replicate plusSize Nothing)) <$>)

||| Take a square, and extend it into an ExtendedSquare
addPlaceHolders : {auto smaller : LTE 1 n} -> Square n t -> ExtendedSquare n t
addPlaceHolders = toExtendedSquare . toJustSquare

||| Repeat a function n times.
dotimes : (a -> a) -> Nat -> (a -> a)
dotimes f Z = id
dotimes f (S n) = f . (dotimes f n)

||| Take the first n elements of a stream as a vector
||| @ n the amount of elements to take
||| @ xs the stream
takeve : (n : Nat) -> (xs : Stream a) -> Vect n a
takeve Z _ = []
takeve (S n) (x :: xs) = x :: (takeve n xs)

||| The numbers zero and over
nats : Stream Nat
nats = iterate (\x => S x) Z

||| The numbers from zero to a ceartain number
||| @ n the length of the vector; one greater 
||| than the final number in the vector
upfrom : (n : Nat) -> Vect n Nat
upfrom n = takeve n nats

||| The numbers from a certain number to zero
||| @ n the length of the vector; one greater 
||| than the first number in the vector
downfrom : (n : Nat) -> Vect n Nat
downfrom n = reverse $ upfrom n

||| Roll each line a different number of times
||| so that the columns represent diagonals.
rollSlope : {n : Nat} ->
            {auto smaller : LTE 1 n} ->
            ((m : Nat) -> Vect m Nat) ->
            ExtendedSquare n t -> ExtendedSquare n t
rollSlope {n} f = let fns = (dotimes rollf) <$> (f n) in
    zipWith (\x, y => x y) fns
            
||| Roll each line an increasing amount of times
||| so that the columns represent diagonals with a positive slope.
rollPSlope : {n : Nat} ->
             {auto smaller : LTE 1 n} ->
             ExtendedSquare n t -> ExtendedSquare n t
rollPSlope = rollSlope upfrom

||| Roll each line a decreasing amount of times
||| so that the columns represent diagonals with a negative slope.
rollNSlope : {n : Nat} ->
             {auto smaller : LTE 1 n} ->
             ExtendedSquare n t -> ExtendedSquare n t
rollNSlope = rollSlope downfrom

||| A rectangle whose height is one less than twice its width
||| @ n the width of the rectangle
TransposedExtendedSquare : (n : Nat) -> {auto smaller : LTE 1 n} -> Type -> Type
TransposedExtendedSquare n t = Vect (formula n) (Vect n (Maybe t))

||| Convert from an extended square to a transposed extended square
toTransposedExtendedSquare : {n : Nat} -> {auto smaller : LTE 1 n} ->
                             ExtendedSquare n t -> TransposedExtendedSquare n t
toTransposedExtendedSquare = transpose


toPositiveSlope : {n : Nat} ->
                  {auto smaller : LTE 1 n} ->
                  Square n t -> TransposedExtendedSquare n t
toPositiveSlope = toTransposedExtendedSquare . rollPSlope . addPlaceHolders

toNegativeSlope : {n : Nat} ->
                  {auto smaller : LTE 1 n} ->
                  Square n t -> TransposedExtendedSquare n t
toNegativeSlope = toTransposedExtendedSquare . rollNSlope . addPlaceHolders


-- Now that we have the manipulations we want on the board, we
-- can start moving towards the actual model for the board

-- ser : {a : Type} -> {auto b : a -> String} -> (x : a) -> String
-- ser {b} x = b x

||| Player types
data Player = PlayerOne | PlayerTwo

||| Types that may be in the cell
data Cell = IsPlayer Player | Empty

||| The type of the board.
||| @ n half the size of the board, and the size of the winning streak of tokens
Board : (n : Nat) -> {auto smaller : LTE 1 n} -> Type
Board n = Square (n + n) Cell

||| An empty board
newBoard : (n : Nat) -> {auto smaller : LTE 1 n} -> Board n
newBoard n = replicate (n + n) (replicate (n + n) Empty)

||| The board, transposed and extended
||| @ n the winning streak of tokens, and half the size of the board.
TransposedExtendedBoard : (n : Nat) -> {auto smaller : LTE 1 n} -> Type
TransposedExtendedBoard n = TransposedExtendedSquare (n + n) Cell

||| A diagonal board of Cells
||| @ n the winning streak of tokens, and half the size of the board
DiagonalizedBoard : (n : Nat) -> {auto smaller : LTE 1 n} -> Type
DiagonalizedBoard n = Vect (formula (n + n)) (Vect (n + n) Cell)

||| After doing the manipulations to the board, make it
||| scannable by converting all the Nothings to Emptys
toDiagonalizedBoard : {n : Nat} ->
                      {auto smaller : LTE 1 n} ->
                      TransposedExtendedBoard n -> DiagonalizedBoard n
toDiagonalizedBoard = (map (map f)) where
  f : Maybe Cell -> Cell
  f (Just x) = x
  f Nothing = Empty

||| The guts of a state machine for counting the lengths
||| of token streaks
record RowScanner where
  constructor MakeRowScanner
  pOnes : List (List Player)
  pTwos : List (List Player)
  current : Cell

||| The default value of a row scanner
newRowScanner : RowScanner
newRowScanner = MakeRowScanner [] [] Empty

||| Add to the newest old list
pushOld : a -> List (List a) -> List (List a)
pushOld a (x :: ys) = (a :: x) :: ys
pushOld a _ = [[a]]

||| Start a new list
pushNew : a -> List (List a) -> List (List a)
pushNew a = ([a] ::)

||| Start a new list upon each switch in cell type.
scanCell : RowScanner -> Cell -> RowScanner
scanCell r c = case (current r) of
  Empty => case c of
    Empty => r
    IsPlayer p => case p of
      PlayerOne => record {pOnes $= (pushNew p), current = c} r
      PlayerTwo => record {pOnes $= (pushNew p), current = c} r
  IsPlayer PlayerOne => case c of
    Empty => record {current = c} r
    IsPlayer p => case p of
      PlayerOne => record {pOnes $= (pushOld p)} r
      PlayerTwo => record {pTwos $= (pushNew p), current = c} r
  IsPlayer PlayerTwo => case c of
    Empty => record {current = c} r
    IsPlayer p => case p of
      PlayerOne => record {pOnes $= (pushNew p), current = c} r
      PlayerTwo => record {pTwos $= (pushOld p)} r

||| Eat a vector of cells, producing a row scanner
eatVect : RowScanner -> Vect n Cell -> RowScanner
eatVect r (c :: cs) = eatVect (scanCell r c) cs
eatVect r [] = r

||| Get the longest chain in a list
mostXs : List (List x) -> Nat
mostXs = (foldl max Z) . (map length)

||| Get the longest chain of ones in a rowscanner.
mostOnes : RowScanner -> Nat
mostOnes = mostXs . pOnes

||| Get the longest chain of twos in a rowscanner
mostTwos : RowScanner -> Nat
mostTwos = mostXs . pTwos


||| Check the winning condition on a vect of cells
isWin : Nat -> RowScanner -> Maybe Player
isWin n r =  case (mostOnes r) >= n of
  True => Just PlayerOne
  False => case (mostTwos r) >= n of
    True => Just PlayerTwo
    False => Nothing

||| Condense from a whole bunch of Maybe xs to a single
||| Maybe x
condense : Vect n (Maybe x) -> Maybe x
condense ((Just x) :: xs) = Just x
condense (Nothing :: xs) = condense xs
condense [] = Nothing

||| Find a win across
isWinHorz: Nat -> Vect n (Vect m Cell) -> Maybe Player
isWinHorz n v = condense $ map (isWin n) $ map (eatVect newRowScanner) v

||| Find a win up and down
isWinVert : Nat -> Vect n (Vect m Cell) -> Maybe Player
isWinVert n v = (isWinHorz n) $ transpose v

||| Find a win, or a lack of one, on the positive slope
isWinPos : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> Maybe Player
isWinPos {n} = (isWinHorz n) . toDiagonalizedBoard . toPositiveSlope

||| Fin a win, or a lack of one, on the negative slope
isWinNeg : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> Maybe Player
isWinNeg {n} = (isWinHorz n) . toDiagonalizedBoard . toPositiveSlope

||| Drop a token into the board
dropToken : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> Fin (n + n) -> Player -> Board n
dropToken b n p = transpose (updateAt n f (transpose b)) where
  f : Vect m Cell -> Vect m Cell
  f x = (reverse . g . reverse) x where
    g : Vect m Cell -> Vect m Cell
    g (c :: cs) = case c of
      Empty => (IsPlayer p) :: cs
      _ => c :: (f cs)
    g [] = []


Cast Cell Int where
  cast Empty = 0
  cast (IsPlayer PlayerOne) = 1
  cast (IsPlayer PlayerTwo) = 2

Cast Int Cell where
  cast 1 = IsPlayer PlayerOne
  cast 2 = IsPlayer PlayerTwo
  cast _ = Empty


toListsBoard : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> List (List Cell)
toListsBoard = toList . (map toList)

toIntssBoard : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> List (List Int)
toIntssBoard = (map (map cast)) . toList . (map toList)

toIntsBoard : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> (List Int, Int)
toIntsBoard {n} b = (((join . toIntssBoard) b), toIntNat (n + n))

forExternal : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> JS_IO (JSValue JSArray)
forExternal = (toJSArray {from = Int} {to = JSNumber}) . fst . toIntsBoard

forExternalSize : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> JSValue JSNumber
forExternalSize = toJS . snd . toIntsBoard

record Enumerable (a : Type -> Type) where
  constructor MakeEnumerable
  enumerate : {x : Type} -> a x -> a (x, Nat)

vectEnumerable : {n : Nat} -> Enumerable (Vect n)
vectEnumerable = MakeEnumerable f where
  f : {x : Type} -> Vect n x -> Vect n (x, Nat)
  f {n} vec = zip vec (takeve n nats)

vectvectEnumerable : {n : Nat} -> {m : Nat} -> Enumerable ((Vect n) . (Vect m))
vectvectEnumerable = MakeEnumerable f where
  f : {x : Type} -> Vect n (Vect m x) -> Vect n (Vect m (x, Nat))
  f vec = g Z vec where
    g : Nat -> Vect n (Vect m x) -> Vect n (Vect m (x, Nat))
    g a {m} (x :: xs) = (zip x (map (a +) (takeve m nats))) :: (g (a + m) xs)
    g a [] = []

record PredEnumerable (x : Type) where
  constructor MakePredEnumerable
  pred : (x, Nat) -> Either x x -- Either something new (left) or the old value (right)


basePred : PredEnumerable x
basePred = MakePredEnumerable f where
  f : (x, Nat) -> Either x x
  f (x, _) = Right x

combinePreds : PredEnumerable x -> PredEnumerable x -> PredEnumerable x
combinePreds a b = MakePredEnumerable (\c => case (pred a) c of
  Left d => Left d
  Right _ => (pred b) c)

intoPreds : Vect n x -> Vect n (PredEnumerable x)
intoPreds vec = map (MakePredEnumerable . f) ((enumerate vectEnumerable) vec) where
  f : (x, Nat) -> (x, Nat) -> Either x x
  f (x, n) = \(y, o) => case (n == o) of
    True => Left x
    False => Right y

unify : {x : Type} -> Either x x -> x
unify (Left x) = x
unify (Right x) = x

intoPred : Vect n x -> PredEnumerable x
intoPred = (foldl combinePreds basePred) . intoPreds

intoUnified : {x : Type} -> Vect n x -> (x, Nat) -> x
intoUnified vec tup = unify ((pred (intoPred vec)) tup)

mapNothing : Maybe a -> a -> Maybe a
mapNothing _ a = Just a

squarify : a -> (n : Nat) -> Vect (n * n) a -> Vect n (Vect n a)
squarify a n vec = let blank = replicate n (replicate n a) in -- : Vect n (Vect n Maybe a)
  let blankenumd = (enumerate vectvectEnumerable) blank in -- Vect n (Vect n (Maybe a, Nat))
    let bigpred = intoUnified vec in -- (x, Nat) -> x
      map (map bigpred) blankenumd

sqrt : (n : Nat) -> Maybe (m : Nat ** (m * m) = n)
sqrt n = f n n where
  f : (n : Nat) -> (m : Nat) -> Maybe (m : Nat ** (m * m) = n)
  f n (S o) = case decEq (o * o) n of
    Yes pf => Just (o ** pf)
    No _ => f n o
  f Z Z = Just (Z ** Refl)
  f (S n) Z = Nothing

patternLen : {n : Nat} -> Vect n a -> Nat
patternLen {n} _ = n

-- maybeSquareList : (lst : List a) -> (map (\n => Vect ((fst n) * (fst n)) a) (Main.sqrt (length lst)))
-- maybeSquareList lst {a} = (sqrt (patternLen (fromList lst))) <$> f where
--   f : {n : Nat} -> (m : Nat ** (m * m) = n) -> (map (\n => Vect ((fst n) * (fst n)) a) (Main.sqrt (length lst)))
--   f (m ** pf) = the (Vect (m * m) a) (fromList lst)
  
-- maybeSquareList : (lst : List a) -> Maybe (Vect (n * n) a)
-- maybeSquareList = case sqrt (length ls) of
--   Just (n ** _) => replicate n (replicate n Nothing)

-- maybeSquareList : (lst : List a) -> Maybe (Vect (n * n) a)
-- maybeSquareList lst {a} = (sqrt (patternLen (fromList lst))) <$> f where
--   f : {n : Nat} -> (m : Nat ** (m * m) = n) -> Maybe (Vect (n * n) a)
--   f (m ** pf) = the (Vect (m * m) a) (fromList lst)

-- fromStored : (i : Int) ->
--              (is : List Int) ->
--              {auto sq : ((cast i) * (cast i)) =
--                         (length (map (cast {to = Cell}) is))} ->
--              Vect (cast i) (Vect (cast i) Cell)
-- fromStored i is = f (cast i) (map cast is) where
--   f : (n : Nat) -> (cs : List Cell) ->
--       {auto ok : (n * n) = (length cs)} -> 
--       Vect n (Vect n Cell)
--   f n cs = (squarify Empty n (fromList cs))
  -- map fromList (fromList (squarify Empty n cs))

-- fromStored : (i : Int) -> (is : List Int) -> Board (cast i)
-- fromStored i is = squarify (cast i) (believe_me (fromList is))

-- toMaybeSquare : n -> Maybe (m : Nat ** (m * m) = n)
-- toMaybeSquare n = f n Z where
--   f : 

-- fromStored : (i : Int) -> 
--              (is : List Int) -> 
--              {auto square : (cast i) * (cast i) = (length is)} ->
--              Vect (cast i) (Vect (cast i) Cell)
-- fromStored i is = 

-- fromStored : (i : Int) -> (is : List Int) -> Maybe (Vect (n * n) Cell) where
--   n = 



-- fromStored : Int -> List Int -> Vect m (Vect o Cell)
-- fromStored i is = f (cast i) (map cast is) where
--   f : Nat -> List Cell -> Vect m (Vect o Cell)
--   f n cs = map fromList (fromList (squarify Empty n cs))


-- map (map fromList) (squarify Empty (cast i) (map cast is))


partial
setIncrementer : (Int -> Int) -> JS_IO ()
setIncrementer f = jscall "setIncrementer(%0)"
                          ((JsFn (Int -> Int)) -> JS_IO ())
                          (MkJsFn f)

anIncrementer : Int -> Int
anIncrementer = (1 +)

amain : JS_IO ()
amain = jscall "amain()" (JS_IO ())

-- storeboard : {n : Nat} -> {auto smaller : LTE 1 n} -> Board n -> JS_IO ()
-- storeboard {n} b = jscall "storeboard(%0)" (Board n -> JS_IO ()) b

partial
main : JS_IO ()
main = setIncrementer anIncrementer >>= (\_ => amain)


-- testBoard : Board 1
-- testBoard = [[IsPlayer PlayerOne, IsPlayer PlayerTwo],
--              [IsPlayer PlayerOne, IsPlayer PlayerTwo]]

--- Printing our board

-- ||| When printed, this character will clear the screen.
-- clearscreen : String
-- clearscreen = """[3J[H[2J"""

-- ||| When printed, this character will clear the colors.
-- clearcolors : String
-- clearcolors = """[m"""

-- ||| When printed, this character will set the color to red
-- redcolor : String
-- redcolor = """[91m"""

-- ||| When printed, this character will set the color to green
-- greencolor : String
-- greencolor = """[92m"""

-- ||| When printed, this character will set the font to bold
-- bolden : String
-- bolden = """[1m"""

