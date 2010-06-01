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
import Data.List (groupBy, map, sortBy, zip, intersperse)
import qualified Data.List as List
import Data.List.Utils (mergeBy)
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Maybe
import Data.Numbers.Primes as Primes
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as Set
import Math.Combinatorics.Multiset (Multiset, kSubsets, permutations, toList)
import qualified Math.Combinatorics.Multiset as Multi
import qualified Math.Combinat.Permutations as Perm
import System.CPUTime
import System.Random.Mersenne
import Text.Printf

twlFile :: FilePath
twlFile = "data/lexica/twl.txt"

-- Rewrite this using accum
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
  let !wordset = wordsetFromWords letterPrimes words
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
               (r:_) -> length r
               _     -> 0

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

-- So, this is not how you're supposed to use Maybe, but I didn't know any
-- better when I wrote it. At some point when I have nothing exciting to do,
-- I should clean this up.
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

-- rack -> list of opening moves tied for highest score
topOpeners :: Lexicon -> Layout -> TileDist -> Rack -> [Move]
topOpeners lexicon layout dist rack = top openers
  where top [] = []
        top x  = snd $ unzip $ head $ groupBy sameScore x
        openers = scoredOpeners lexicon layout dist rack
        sameScore (x,_) (y,_) = x == y

-- Flatten a list of lists of (Score,Move), each already sorted by
-- descending score, maintaining the ordering.
mergeMoves :: [[(Int,Move)]] -> [(Int,Move)]
mergeMoves = foldl (mergeBy descendingScore) []
  where descendingScore (x,_) (y,_) = compare y x

-- Given a rack, returns a list of opening (scoring) plays, zipped with
-- their scores, from highest to lowest.
scoredOpeners :: Lexicon -> Layout -> TileDist -> Rack -> [(Int,Move)]
scoredOpeners lexicon layout dist rack = scoredMoves
  where rackSet = Multi.fromList rack
        scoredMoves = mergeMoves $ map lengthMoves [7,6..2]
        lengthMoves k = mergeMoves $ map (setMoves k) $ kSubsets k rackSet
        setMoves k set | good = mergeMoves $ map openersAt' [min..max]
                       | otherwise = []
          where good = isGoodIn lexicon (toList set)
                openersAt' = openersAt layout dist set
                min = max-k+1
                max = snd (layoutStart layout)

-- Given a set of tiles and a column, returns a list of opening (scoring)
-- plays, zipped with their scores, from highest to lowest.
openersAt :: Layout -> TileDist -> Multiset Integer -> Int -> [(Int,Move)]
openersAt layout dist set col = map toScoredMove perms
  where perms = descendingPerms dist xls set
        xls = map ((layoutXLS layout) !) squares
        squares = map makeSq $ range $ listBounds $ toList set
        row = fst (layoutStart layout)
        sq = (row,col)
        makeSq delta = first (+ delta) sq
        toScoredMove perm = (score,move)
          where move = Move perm sq Across
                score = scoreOpener layout dist move
    
-- Given a set of tiles and per-square multipliers for positions on the
-- board, returns a list of permutations from highest to lowest score.
descendingPerms :: TileDist -> [Int] -> Multiset Integer -> [[Integer]]
descendingPerms dist muls set = map orderForBoard $ permutations descendingSet
  where
    descendingSet = Multi.fromList descending
    descending = concat $ zipWith number [0..] $ List.group bigToSmall
    number n x = if null x then [] else n:number n (tail x)
    bigToSmall = List.sortBy scoreCmp (toList set)
    scoreCmp x y = compare (score y) (score x)
    score x = unsafeLookup x (tileScores dist)
    ranks = reverse $ map fst $ sortBy (comparing snd) $ zip [1..] muls
    p = Perm.inverse $ Perm.toPermutation ranks
    orderForBoard = Perm.permuteList p . map ((List.nub bigToSmall) !!)

scoreOpener :: Layout -> TileDist -> Move -> Int
scoreOpener layout dist (Move word sq dir) = score
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
      scores = tileScores dist

topMoves :: Lexicon -> Layout -> TileDist -> Board -> Rack -> [Move]
topMoves lexicon layout dist board rack = 
    if boardIsEmpty board then topOpeners lexicon layout dist rack
    else fail "can't yet find moves on nonempty boards"

main :: IO ()
main = do
  putStrLn "Loading..."
  twl <- lexiconFromFile twlFile
  putStrLn "Loaded TWL."
  let board = emptyBoard standard
  let english = TileDist (englishScores twl)
  let rack = fromJust $ readRack twl "QIZAXUJ"
  putStrLn $ showRack twl rack
  start <- getCPUTime
  let !moves = topOpeners twl standard english rack
  end <- getCPUTime
  let diff = fromIntegral (end-start) / (10^12)
  let top = head moves
  let topString = showMove twl top
  printf "found %i top moves (such as %s) in %0.5fs\n"
    (length moves::Int) (topString::String) (diff::Double)
  let board' = makeMove board top
  putStr $ unlines $ labelBoard standard twl board'
