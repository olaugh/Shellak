-------------------------------------------------------------------
-- |
-- Copyright   : (c) John O'Laughlin 2010
-- License     : GPL2
--
-- Maintainer  : olaughlin@gmail.com
-- Stability   : unstable
-- Portability : ?
--
-- shellak, a crossword game AI
--
-------------------------------------------------------------------

import Control.Arrow
import Control.Monad
import Control.Monad.ST
import Data.Array as A
import Data.Array.IO
import Data.Array.ST
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Char
import Data.List (map, sortBy, zip, intersperse)
import qualified Data.List as List
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Maybe
import Data.Numbers.Primes as Primes
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as Set
import System.Random.Mersenne
import Math.Combinatorics.Multiset (Multiset, kSubsets, permutations, toList)
import qualified Math.Combinatorics.Multiset as Multi

twlFile :: FilePath
twlFile = "data/lexica/twl.txt"

freqs :: FilePath -> IO [(Char,Int)]
freqs file = do
  content <- B.readFile file
  let counts = runST (runCount content)
  return (assocs counts)
    where
      doCount b a i = if i < B.length b then
                          do let c = B.index b i
                             oldCount <- readArray a c
                             writeArray a c (oldCount + 1)
                             doCount b a (i + 1)
                      else return a
      runCount b = do a <- newArray (chr 0,chr 255) 0
                        :: ST s (STArray s Char Int)
                      (doCount b a 0 >>= freeze)

letterPrimesFromWordFile :: FilePath -> IO (Map Char Integer)
letterPrimesFromWordFile file = do
  counts <- freqs file
  let sorted = map fst $ reverse $ sortBy (comparing snd) counts
  let ascii = filter isAscii sorted
  let letters = filter isUpper ascii
  let assocs = zip letters Primes.primes
  return $ fromList assocs

unsafeLookup :: (Ord k) => k -> Map k a -> a
unsafeLookup x = fromJust . Map.lookup x

unpackWith :: (Char -> a) -> (ByteString -> [a])
unpackWith f = map f . B.unpack

wordProduct :: Map Char Integer -> ByteString -> Integer
wordProduct ps = product . unpackWith (`unsafeLookup` ps)

stringWordProduct :: Map Char Integer -> String -> Integer
stringWordProduct ps = product . map (`unsafeLookup` ps)

wordProductIn :: Lexicon -> String -> Integer
wordProductIn = stringWordProduct . lexiconPrimes

wordsetFromWords :: Map Char Integer -> [ByteString] -> Set Integer
wordsetFromWords ps = Set.fromList . map (wordProduct ps)

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

inverseMap :: Ord b => Map a b -> Map b a
inverseMap = fromList . map swap . Map.assocs

data Lexicon = Lexicon (Map Char Integer) [ByteString] (Set Integer)
lexiconPrimes  (Lexicon ps _     _  ) = ps
lexiconWords   (Lexicon _  words _  ) = words
lexiconSet     (Lexicon _  _     set) = set
lexiconLetters                        = inverseMap . lexiconPrimes

lexiconFromFile :: FilePath -> IO (Lexicon)
lexiconFromFile file = do
  letterPrimes <- letterPrimesFromWordFile file
  contents <- B.readFile file
  let words = B.lines contents
  let wordset = wordsetFromWords letterPrimes words
  return $ Lexicon letterPrimes words wordset

isGoodIn :: Lexicon -> [Integer] -> Bool
isGoodIn lex word = Set.member (product word) (lexiconSet lex)

type Tile = Char
type Bag = Array Int Char

data TileDist = TileDist (Map Integer Int)
tileScores (TileDist scores) = scores

englishScores :: Lexicon -> (Map Integer Int)
englishScores lexicon = fromList $ zip ps scores
    where
      ps = lookupPrimes lexicon ['A'..'Z']
      scores = [1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,1,10]

listBounds :: [a] -> (Int,Int)
listBounds s = (0,len-1) where len = length s

stringArray :: String -> Array Int Char
stringArray s = listArray (listBounds s) s

standardText :: [String]
standardText =  ["3W .. .. 2L .. .. .. 2W .. .. .. 2L .. .. 3W"
                ,".. 2W .. .. .. 3L .. .. .. 3L .. .. .. 2W .."
                ,".. .. 2W .. .. .. 2L .. 2L .. .. .. 2W .. .."
                ,"2L .. .. 2W .. .. .. 2L .. .. .. 2W .. .. 2L"
                ,".. .. .. .. 2W .. .. .. .. .. 2W .. .. .. .."
                ,".. 3L .. .. .. 3L .. .. .. 3L .. .. .. 3L .."
                ,".. .. 2L .. .. .. 2L .. 2L .. .. .. 2L .. .."
                ,"3W .. .. 2L .. .. .. 2W .. .. .. 2L .. .. 3W"
                ,".. .. 2L .. .. .. 2L .. 2L .. .. .. 2L .. .."
                ,".. 3L .. .. .. 3L .. .. .. 3L .. .. .. 3L .."
                ,".. .. .. .. 2W .. .. .. .. .. 2W .. .. .. .."
                ,"2L .. .. 2W .. .. .. 2L .. .. .. 2W .. .. 2L"
                ,".. .. 2W .. .. .. 2L .. 2L .. .. .. 2W .. .."
                ,".. 2W .. .. .. 3L .. .. .. 3L .. .. .. 2W .."
                ,"3W .. .. 2L .. .. .. 2W .. .. .. 2L .. .. 3W"]

type IntGrid = Array (Int,Int)
textMuls :: [String] -> Char -> (IntGrid Int)
textMuls grid c = listsArray $ map stringMul grid
    where
      stringMul = map parseMul . words
      parseMul ['2',x] = if x == c then 2 else 1
      parseMul ['3',x] = if x == c then 3 else 1
      parseMul _       = 1

gridSize :: IntGrid a -> (Int,Int)
gridSize grid = (xmax+1,ymax+1)
    where (_,(xmax,ymax)) = bounds grid

textGridSize :: [[a]] -> (Int,Int)
textGridSize grid = (rows,cols)
    where
      rows = length grid
      cols = case grid of 
               (r:rs) -> length r
               _      -> 0

listsArray :: [[a]] -> Array (Int,Int) a
listsArray grid = listArray bounds (concat grid)
    where
      bounds = ((0,0),(rows-1,cols-1))
      (rows,cols) = textGridSize grid

splitAtEach :: Int -> [a] -> [[a]]
splitAtEach n []  = []
splitAtEach n abc = a:splitAtEach n bc
    where (a,bc) = splitAt n abc

data Board = Board Bool (IntGrid Integer)
boardIsEmpty (Board empty _      ) = empty
boardPrimes  (Board _      primes) = primes

emptyBoard :: Layout -> Board
emptyBoard layout = Board True (listArray (bounds (layoutXWS layout)) (repeat 0))

data Layout = Layout (IntGrid Int) (IntGrid Int) (Int,Int)
layoutXWS   (Layout xws _ s) = xws
layoutXLS   (Layout _ xls s) = xls
layoutStart (Layout _ _   s) = s

both :: (a -> b) -> (a,a) -> (b,b)
both f (x,y) = (f x, f y)
  
textLayout :: [String] -> Layout
textLayout grid = Layout xws xls start
    where
      xws = textMuls grid 'W'
      xls = textMuls grid 'L'
      start = both (`div` 2) (gridSize xws)

standard :: Layout
standard = textLayout standardText

drawRack :: Bag -> MTGen -> IO String
drawRack bag g = drawTiles 7 []
    where
      drawTiles :: Int -> [Int] -> IO String
      drawTiles 0 drawn = return ""
      drawTiles n drawn = do
        r <- random g :: IO Int
        let i = r `mod` 98
        let tile = bag ! i
        let drawn' = i : drawn
        rest <- drawTiles (n-1) drawn'
        if elem i drawn
            then drawTiles n drawn
            else return (tile : rest)

spaceOut :: String -> String
spaceOut = intersperse ' '

prettifyGrid :: [String] -> [String]
prettifyGrid grid = [letters,line] ++ numbers ++ [line,letters]
    where
      (rows,cols) = textGridSize grid
      indent s = "   " ++ s ++ " "
      letters = indent $ spaceOut $ take cols ['a'..]
      line = indent $ replicate (cols*2-1) '-'
      numbers = zipWith numberRow [1..] grid
      numberRow n row = pad (show n) ++ "|" ++ spaceOut row ++ "|"
      pad s = replicate (2-length s) ' ' ++ s

layoutPremiumGrids :: Layout -> ([[Int]],[[Int]])
layoutPremiumGrids layout = both (splitAtEach cols) (both elems (xws,xls))
    where
      xws = layoutXWS layout
      xls = layoutXLS layout
      (rows,cols) = gridSize xws

premiumsTextGrid :: ([[Int]],[[Int]]) -> [String]
premiumsTextGrid grid = uncurry (zipWith rowString) grid
    where
      rowString = zipWith square
      square 3 1 = '='
      square 2 1 = '-'
      square 1 3 = '"'
      square 1 2 = '\''
      square _ _ = ' '

labelLayout :: Layout -> [String]
labelLayout = prettifyGrid . premiumsTextGrid . layoutPremiumGrids

letterGrid :: Lexicon -> Board -> [String]
letterGrid lexicon board = splitAtEach cols letters
    where
      primes = boardPrimes board
      letters = map lookup (elems primes)
      lookup 0 = ' '
      lookup p = unsafeLookup p (lexiconLetters lexicon)
      (rows,cols) = gridSize primes

boardGrid :: [String] -> [String] -> [String]
boardGrid = zipWith rowString
    where
      rowString = zipWith square
      square x ' ' = x -- empty  -> premium
      square _ x   = x -- letter -> letter

labelBoard :: Layout -> Lexicon -> Board -> [String]
labelBoard layout lexicon board = prettifyGrid bg
    where
      bg = boardGrid premiums letters
      premiums = premiumsTextGrid (layoutPremiumGrids layout)
      letters = letterGrid lexicon board

isAsciiAlpha :: Char -> Bool
isAsciiAlpha c = isAlpha c && isAscii c

data Direction = Down | Across
data Move = Move [Integer] (Int,Int) Direction

readMove :: Lexicon -> String -> Maybe Move
readMove lexicon s = case parse of
                       Just (Just ps,Just (Just sq,dir)) -> Just $ Move ps sq dir
                       _                                 -> Nothing
    where
      parse = case (words s) of
                (pos:[letters]) -> Just (readLetters letters,readPos pos)
                _               -> Nothing
      readLetters = safeLookupPrimes lexicon
      readPos pos = case (splitPos pos) of
                      Just (sq,dir) -> Just (readSq sq,dir)
                      _             -> Nothing
      splitPos pos = if isAsciiAlpha (head pos) then
                         Just ((tail pos, head pos), Down)
                     else if isAsciiAlpha (last pos) then
                              Just ((init pos, last pos), Across)
                          else Nothing
      readSq (num,alpha) = if not (null num) && all isDigit num then
                               Just (-1+read num::Int,ord lower-ord 'a')
                           else Nothing
          where lower = toLower alpha

lookupLetters :: Lexicon -> [Integer] -> String
lookupLetters lexicon = map lookup
    where lookup p = unsafeLookup p (lexiconLetters lexicon)

safeLookupPrimes :: Lexicon -> String -> Maybe [Integer]
safeLookupPrimes _       []     = Just []
safeLookupPrimes lexicon (x:xs) = case (p,ps) of
                                    (Just p',Just ps') -> Just (p':ps')
                                    _                  -> Nothing
    where p = Map.lookup x (lexiconPrimes lexicon)
          ps = safeLookupPrimes lexicon xs

lookupPrimes :: Lexicon -> String -> [Integer]
lookupPrimes lexicon = map lookup
    where lookup letter = unsafeLookup letter (lexiconPrimes lexicon)

showMove :: Lexicon -> Move -> String
showMove lexicon (Move ps (row,col) dir) = pos ++ " " ++ letters
    where
      pos = case dir of
              Across -> num ++ alpha
              Down   -> alpha ++ num
      num = show (row+1)
      alpha = [chr (col+ord 'a')]
      letters = lookupLetters lexicon ps

makeMove :: Board -> Move -> Board
makeMove (Board _ grid) (Move word pos dir) = Board False grid'
    where
      grid' = grid // assocs
      assocs = zipWith makeAssoc word [0..]
      coordMover = case dir of
                     Down   -> first
                     Across -> second
      makeAssoc letter delta = (pos',letter)
          where pos' = coordMover (+ delta) pos

type Rack = [Integer]

readRack :: Lexicon -> String -> Maybe Rack
readRack = safeLookupPrimes

showRack :: Lexicon -> Rack -> String
showRack = lookupLetters

topOpeners :: Lexicon -> Layout -> TileDist -> Board -> Rack -> [Move]
topOpeners lexicon layout dist board rack = foldl improveLen [] [7,6..2]
  where
    improveLen :: [Move] -> Int -> [Move]
    improveLen tops k = foldl (improveSet k) tops $ kSubsets k rackSet
    rackSet = Multi.fromList rack
    improveSet :: Int -> [Move] -> Multiset Integer -> [Move]
    improveSet k tops set = if isGoodIn lexicon (toList set) then
                              foldl (improveCol set) tops [min..max]
                            else tops
      where min = max-k+1
            max = snd (layoutStart layout)
    improveCol :: Multiset Integer -> [Move] -> Int -> [Move]
    improveCol set tops col = foldl improvePerm tops $ permutations set
      where improvePerm tops perm = tops'
              where tops' = case compare score bestScore of
                      GT -> [move]
                      EQ -> (move:tops)
                      LT -> tops
                    move = Move perm (row,col) Across
                    row = fst (layoutStart layout)
                    score = scoreOpener layout dist board move
                    bestScore = case tops of
                      []    -> -1000
                      (x:_) -> scoreOpener layout dist board x

scoreOpener :: Layout -> TileDist -> Board -> Move -> Int
scoreOpener layout tileDist board (Move word sq dir) = score
    where
      score = bonus+mul*sum letterScores
      mul = product $ map ((layoutXWS layout) !) squares
      letterScores = zipWith (*) xls wordScores
      xls = map ((layoutXLS layout) !) squares
      wordScores = map (`unsafeLookup` scores) word
      squares = map makeSq $ range $ listBounds word
      coordMover = case dir of
                     Down   -> first
                     Across -> second
      makeSq delta = coordMover (+ delta) sq
      bonus = if length word == 7 then 50 else 0
      scores = tileScores tileDist

-- topMoves :: Lexicon -> Layout -> Board -> Rack -> [Move]
-- topMoves lexicon board rack = 
--     if boardIsEmpty board then topOpeners lexicon layout board rack
--     else fail "can't yet find moves on nonempty boards"

-- main :: IO ()
-- main = do
--   putStrLn "Loading..."
--   twl <- lexiconFromFile twlFile
--   putStrLn "Loaded TWL."
--   g <- newMTGen (Just 42)
--   let doRack = do rack <- drawRack english g
--                   putStrLn rack
--                   doRack
--   doRack

main :: IO ()
main = do
  putStrLn "Loading..."
  twl <- lexiconFromFile twlFile
  putStrLn "Loaded TWL."
  -- let moveString = "8D ZOOID"
  -- let move = fromJust $ readMove twl moveString
  -- let board' = makeMove board move
  let board = emptyBoard standard
  let english = TileDist (englishScores twl)
  let rack = fromJust $ readRack twl "ABCDEFG"
  putStrLn $ showRack twl rack
  let tops = topOpeners twl standard english board rack
  putStr $ unlines $ map (showMove twl) tops
  -- print $ scoreOpener standard english board move
  -- putStr $ unlines $ labelBoard standard twl board'
