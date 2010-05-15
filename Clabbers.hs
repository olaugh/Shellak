import Control.Arrow
import Control.Monad
import Control.Monad.ST
import Data.Array as A
import Data.Array.IO
import Data.Array.ST
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Char
import Data.List (map, sortBy, zip)
import qualified Data.List as List
import Data.Map (Map, fromList)
import qualified Data.Map as Map
import Data.Maybe
import Data.Numbers.Primes
import Data.Ord (comparing)
import Data.Set (Set)
import qualified Data.Set as Set
import System.Random.Mersenne

twlFile :: FilePath
--twlFile = "/Users/jolaughlin/scrabble/twl.txt"
twlFile = "/home/john/scrabble/twl.txt"

freqs :: FilePath -> IO [(Char,Int)]
freqs file = do
  content <- B.readFile file
  let !counts = runST (runCount content)
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
  let assocs = zip letters primes
  return $ fromList assocs

unsafeLookup :: (Ord k) => k -> Map k a -> a
unsafeLookup x = fromJust . Map.lookup x

unpackWith :: (Char -> a) -> (ByteString -> [a])
unpackWith f = map f . B.unpack

wordProduct :: ByteString -> Map Char Integer -> Integer
wordProduct b ps = product $ unpackWith (`unsafeLookup` ps) b

stringWordProduct :: String -> Map Char Integer -> Integer
stringWordProduct cs ps = product $ map (`unsafeLookup` ps) cs

wordProductIn :: String -> (Lexicon -> Integer)
wordProductIn cs = stringWordProduct cs . lexiconPrimes

wordsetFromWords :: [ByteString] -> Map Char Integer -> Set Integer
wordsetFromWords words ps = Set.fromList $ map (\x -> wordProduct x ps) words

data Lexicon = Lexicon (Map Char Integer) [ByteString] (Set Integer)
lexiconPrimes (Lexicon ps _     _  ) = ps
lexiconWords  (Lexicon _  words _  ) = words
lexiconSet    (Lexicon _  _     set) = set

lexiconFromFile :: FilePath -> IO (Lexicon)
lexiconFromFile file = do
  letterPrimes <- letterPrimesFromWordFile file
  contents <- B.readFile file
  let words = B.lines contents
  let !wordset = wordsetFromWords words letterPrimes
  return $ Lexicon letterPrimes words wordset

isGoodIn :: String -> Lexicon -> Bool
isGoodIn word lex = Set.member (wordProductIn word lex) (lexiconSet lex)

type Tile = Char
type Bag = Array Int Char

englishString :: String
englishString = "AAAAAAAAABBCCDDDDEEEEEEEEEEEEFFGGGHHIIIIIIIIIJKLLLLMMNNNNNN"
              ++ "OOOOOOOOPPQRRRRRRSSSSTTTTTTUUUUVVWWXYYZ" -- no blanks yet

stringBounds :: String -> (Int,Int)
stringBounds s = (0,len-1) where len = length s

stringArray :: String -> Array Int Char
stringArray s = listArray (stringBounds s) s

english :: Bag
english = stringArray englishString

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

listsArray :: [[a]] -> Array (Int,Int) a
listsArray grid = listArray bounds (concat grid)
    where
      bounds = ((0,0),(rows-1,cols-1))
      rows = length grid
      cols = case grid of 
               (r:rs) -> length r
               _      -> 0

splitAtEach :: Int -> [a] -> [[a]]
splitAtEach n []  = []
splitAtEach n abc = a:splitAtEach n bc
    where (a,bc) = splitAt n abc

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

labelTextGrid :: [String] -> [String]
labelTextGrid grid = grid --FIXME

layoutTextGrid :: Layout -> [String]
layoutTextGrid layout = splitAtEach cols grid
    where
      xws = layoutXWS layout
      intGrid = elems xws
      grid = map intToDigit intGrid
      (rows,cols) = gridSize xws

labelLayout :: Layout -> [String]
labelLayout = labelTextGrid . layoutTextGrid

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
main = putStr $ unlines $ layoutTextGrid standard
--main = print $ layoutStart standard
