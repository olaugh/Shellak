-------------------------------------------------------------------
-- |
-- Copyright   : (c) John O'Laughlin 2010
-- License     : GPL2
--
-- Maintainer  : olaughlin@gmail.com
-- Stability   : unstable
-- Portability : ?
--
-- Shellak, a crossword game AI
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
import Data.Set (Set, member)
import qualified Data.Set as Set
import Math.Combinatorics.Multiset (Multiset, kSubsets, permutations, toList,
                                    fromCounts, toCounts)
import qualified Math.Combinat.Permutations as Perm
import qualified Math.Combinatorics.Multiset as Multi
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
    where doCount b a i = if i < B.length b then
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
isGoodIn lex word = member (product word) (lexiconSet lex)

isGoodWith :: Lexicon -> Integer -> [Integer] -> Bool
isGoodWith lex through word = member (through*(product word)) (lexiconSet lex)

isGoodWithProd :: Lexicon -> Integer -> Integer -> Bool
isGoodWithProd lex through prod = member (through*prod) (lexiconSet lex)

type TileSet = Multiset Integer

data TileDist = TileDist (Map Integer Int)
tileScores (TileDist scores) = scores

englishScores :: Lexicon -> (Map Integer Int)
englishScores lexicon = fromList $ zip ps scores
  where ps = lookupPrimes lexicon ['A'..'Z']
        scores = [1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10]

listBounds :: [a] -> (Int,Int)
listBounds s = (0,len-1) where len = length s

stringArray :: String -> Array Int Char
stringArray s = listArray (listBounds s) s

standardText :: [String]
standardText =  ["3W .. .. 2L .. .. .. 3W .. .. .. 2L .. .. 3W"
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
                ,"3W .. .. 2L .. .. .. 3W .. .. .. 2L .. .. 3W"]

type IntGrid = Array (Int,Int)
textMuls :: [String] -> Char -> (IntGrid Int)
textMuls grid c = listsArray $ map stringMul grid
  where stringMul = map parseMul . words
        parseMul ['2',x] = if x == c then 2 else 1
        parseMul ['3',x] = if x == c then 3 else 1
        parseMul _       = 1

gridSize :: IntGrid a -> (Int,Int)
gridSize grid = (xmax+1,ymax+1)
    where (_,(xmax,ymax)) = bounds grid

textGridSize :: [[a]] -> (Int,Int)
textGridSize grid = (rows,cols)
  where rows = length grid
        cols = case grid of 
                 (r:_) -> length r
                 _     -> 0

listsArray :: [[a]] -> Array (Int,Int) a
listsArray grid = listArray bounds (concat grid)
  where bounds = ((0,0),(rows-1,cols-1))
        (rows,cols) = textGridSize grid

splitAtEach :: Int -> [a] -> [[a]]
splitAtEach n []  = []
splitAtEach n abc = a:splitAtEach n bc
  where (a,bc) = splitAt n abc

data Board = Board Bool (IntGrid Integer)
boardIsEmpty (Board empty _      ) = empty
boardPrimes  (Board _      primes) = primes

emptyBoard :: Layout -> Board
emptyBoard layout =
  Board True (listArray (bounds (layoutXWS layout)) (repeat 0))

data Layout = Layout (IntGrid Int) (IntGrid Int) (Int,Int)
layoutXWS   (Layout xws _ s) = xws
layoutXLS   (Layout _ xls s) = xls
layoutStart (Layout _ _   s) = s

both :: (a -> b) -> (a,a) -> (b,b)
both f (x,y) = (f x, f y)
  
textLayout :: [String] -> Layout
textLayout grid = Layout xws xls start
  where xws = textMuls grid 'W'
        xls = textMuls grid 'L'
        start = both (`div` 2) (gridSize xws)

standard :: Layout
standard = textLayout standardText

spaceOut :: String -> String
spaceOut = intersperse ' '

prettifyGrid :: [String] -> [String]
prettifyGrid grid = [letters,line] ++ numbers ++ [line,letters]
  where (rows,cols) = textGridSize grid
        indent s = "   " ++ s ++ " "
        letters = indent $ spaceOut $ take cols ['a'..]
        line = indent $ replicate (cols*2-1) '-'
        numbers = zipWith numberRow [1..] grid
        numberRow n row = pad (show n) ++ "|" ++ spaceOut row ++ "|"
        pad s = replicate (2-length s) ' ' ++ s

layoutPremiumGrids :: Layout -> ([[Int]],[[Int]])
layoutPremiumGrids layout = both (splitAtEach cols) (both elems (xws,xls))
  where xws = layoutXWS layout
        xls = layoutXLS layout
        (rows,cols) = gridSize xws

premiumsTextGrid :: ([[Int]],[[Int]]) -> [String]
premiumsTextGrid grid = uncurry (zipWith rowString) grid
  where rowString = zipWith square
        square 3 1 = '='
        square 2 1 = '-'
        square 1 3 = '"'
        square 1 2 = '\''
        square _ _ = ' '

labelLayout :: Layout -> [String]
labelLayout = prettifyGrid . premiumsTextGrid . layoutPremiumGrids

letterGrid :: Lexicon -> Board -> [String]
letterGrid lexicon board = splitAtEach cols letters
  where primes = boardPrimes board
        letters = map lookup (elems primes)
        lookup 0 = ' '
        lookup p = unsafeLookup p (lexiconLetters lexicon)
        (rows,cols) = gridSize primes

boardGrid :: [String] -> [String] -> [String]
boardGrid = zipWith rowString
  where rowString = zipWith square
        square x ' ' = x -- empty  -> premium
        square _ x   = x -- letter -> letter

labelBoard :: Layout -> Lexicon -> Board -> [String]
labelBoard layout lexicon board = prettifyGrid bg
  where bg = boardGrid premiums letters
        premiums = premiumsTextGrid (layoutPremiumGrids layout)
        letters = letterGrid lexicon board

isAsciiAlpha :: Char -> Bool
isAsciiAlpha c = isAlpha c && isAscii c

data Dir = Down | Across
instance Show Dir where
  show Down   = "Down"
  show Across = "Acrs"
  
data Move = Move [Integer] (Int,Int) Dir

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

markThrough :: Board -> [(Int,Char)] -> [(Int,Char)] -> String
markThrough board new old = concat $ map renderChunk chunks
  where renderChunk :: ([Bool],[Char]) -> [Char]
        renderChunk (True:_,x)  = x
        renderChunk (False:_,x) = "(" ++ x ++ ")"
        all = zip new (repeat True) ++ zip old (repeat False)
        (sorted,isNew) = unzip $ sortBy (comparing (fst . fst)) all
        letters = snd $ unzip sorted
        chunks = map unzip $ groupBy sameGroup $ zip isNew letters
        sameGroup (x,_) (y,_) = x == y
    
showMove :: Lexicon -> Board -> Move -> String
showMove lexicon board (Move word sq@(row,col) dir) = pos ++ " " ++ letters
  where pos = case dir of
                Across -> num ++ alpha
                Down   -> alpha ++ num
        num = show (row+1)
        alpha = [chr (col+ord 'a')]
        letters = markThrough board new old
        axis = case dir of
                 Down   -> fst
                 Across -> snd
        new = zip newSqs' newLetters
        newSqs' = map axis newSqs
        Just newSqs = squaresAt board sq dir $ length word
        newLetters = lookupLetters lexicon word
        old = zip oldSqs' oldLetters
        oldSqs' = map axis oldSqs
        oldSqs = throughSqsAt board sq dir $ length word
        oldLetters = lookupLetters lexicon oldTiles
        oldTiles = throughTilesAt board sq dir $ length word

makeMove :: Board -> Move -> Board
makeMove (Board _ grid) (Move word pos dir) = Board False grid'
  where grid' = grid // assocs
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

descendingScore :: (Int,a) -> (Int,b) -> Ordering
descendingScore (x,_) (y,_) = compare y x

-- Flatten a list of lists of (Score,Move), each already sorted by
-- descending score, maintaining the ordering.
mergeMoves :: [[(Int,Move)]] -> [(Int,Move)]
mergeMoves = foldl (mergeBy descendingScore) []

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
openersAt :: Layout -> TileDist -> TileSet -> Int -> [(Int,Move)]
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
    
onBoard :: Board -> (Int,Int) -> Maybe (Int,Int)
onBoard board (row,col) | row < 0      = Nothing
                        | col < 0      = Nothing
                        | row > maxRow = Nothing
                        | col > maxCol = Nothing
                        | otherwise    = Just (row,col)
  where (_,(maxRow,maxCol)) = bounds $ boardPrimes board

isOnBoard :: Board -> (Int,Int) -> Bool
isOnBoard board sq = isJust $ onBoard board sq

safeSquare :: Board -> (Int,Int) -> Maybe [(Int,Int)]
safeSquare board sq = do
  sq' <- onBoard board sq
  return $ if ((boardPrimes board) ! sq) == 0 then [sq] else []

crossDir :: Dir -> Dir
crossDir Down = Across
crossDir Across = Down

prevSq :: (Int,Int) -> Dir -> (Int,Int)
prevSq (row,col) Down   = (row-1,col)
prevSq (row,col) Across = (row,col-1)

nextSq :: (Int,Int) -> Dir -> (Int,Int)
nextSq (row,col) Down   = (row+1,col)
nextSq (row,col) Across = (row,col+1)

squaresAt :: Board -> (Int,Int) -> Dir -> Int -> Maybe [(Int,Int)]
squaresAt _     _  _   0   = Just []
squaresAt board sq dir len = do
  sqHere <- safeSquare board sq
  let sqHereLen = if null sqHere then 0 else 1
  let sq' = nextSq sq dir
  let len' = len-sqHereLen
  moreSqs <- squaresAt board sq' dir len' 
  return $ sqHere ++ moreSqs
  
mulAt :: Layout -> Board -> Dir -> (Int,Int) -> Int
mulAt layout board dir sq = ways * xls
  where ways = if (hooksAt board dir sq) then 2 else 1
        xls = (layoutXLS layout) ! sq
        
mulsAt :: Layout -> Board -> Dir -> [(Int,Int)] -> [Int]
mulsAt layout board dir sqs = map (mulAt layout board dir) sqs

fitsAt :: Lexicon -> Integer -> Integer -> Bool
fitsAt _   1     _ = True
fitsAt lex cross p = member (p*cross) (lexiconSet lex)
  
fits :: Lexicon -> [Integer] -> [Integer] -> Bool
fits _   []       _    = True
fits lex cs ps = and $ zipWith (fitsAt lex) cs ps

throughSqsAt :: Board -> (Int,Int) -> Dir -> Int -> [(Int,Int)]
throughSqsAt _     _  _   (-1) = []
throughSqsAt board sq dir len  = if isOnBoard board sq then throughs else []
  where throughs = sqHere ++ throughSqsAt board sq' dir len'
        prime = (boardPrimes board) ! sq
        (sqHere,len') = if prime == 0 then ([],len-1) else ([sq],len)
        sq' = nextSq sq dir

throughTilesAt :: Board -> (Int,Int) -> Dir -> Int -> [Integer]
throughTilesAt board sq dir len = map ((boardPrimes board) !) sqs
  where sqs = throughSqsAt board sq dir len

throughAt :: Board -> (Int,Int) -> Dir -> Int -> Integer
throughAt board sq dir len = product $ throughTilesAt board sq dir len

sqTiles :: Board -> [(Int,Int)] -> [Integer]
sqTiles board sqs = map ((boardPrimes board) !) sqs

sqProd :: Board -> [(Int,Int)] -> Integer
sqProd board sqs = product $ sqTiles board sqs

-- rack -> list of moves tied for highest score
topMoves :: Lexicon -> Layout -> Board -> TileDist -> Rack -> [Move]
topMoves lexicon layout board dist rack = top moves
  where top [] = []
        top x  = snd $ unzip $ head $ groupBy sameScore x
        moves = if boardIsEmpty board then openers else nonOpeners
        openers = scoredOpeners lexicon layout dist rack
        nonOpeners = scoredNonOpeners lexicon layout board dist rack
        sameScore (x,_) (y,_) = x == y

scoredNonOpeners :: Lexicon -> Layout -> Board -> TileDist -> Rack
                            -> [(Int,Move)]
scoredNonOpeners lex layout board dist rack = mergeMoves $ map sqLenMoves' sqs
  where sqs = [(r,c,d,len) | len <- [7], r <- [0], c <- [0], d <- dirs]
        bounds' x = ((r,r'),(c,c')) where ((r,c),(r',c')) = bounds x
        (rows,cols) = both range $ bounds' $ boardPrimes board
        lens = [7,6..1]
        dirs = [Down, Across]
        sqLenMoves' (r,c,d,len) =
          sqLenMoves layout lex dist board rack (r,c) d len

touch :: Board -> ((Int,Int),Dir,Int) -> Bool
touch board (sq,dir,len) = (isJust squares) && touches
  where squares = squaresAt board sq dir len
        touches = (through > 1) || (hooks board (fromJust squares) dir)
        through = throughAt board sq dir len

addThrough :: Board -> ((Int,Int),Dir,Int) -> ((Int,Int),Dir,Int,Integer)
addThrough board (sq,dir,len) = (sq,dir,len,through)
  where through = throughAt board sq dir len

sqsThatTouch :: Board -> Int -> [((Int,Int),Dir,Int,Integer)]
sqsThatTouch board rackSize =
  map (addThrough board) $ filter (touch board) sqs
  where sqs = [((r,c),d,len) | len <- lens, r <- rows, c <- cols, d <- dirs]
        bounds' x = ((r,r'),(c,c')) where ((r,c),(r',c')) = bounds x
        (rows,cols) = both range $ bounds' $ boardPrimes board
        lens = [7,6..1]
        dirs = [Down, Across]
        
nonOpenerSpots :: Board -> TileDist -> Rack
                        -> [((Int,Int),Dir,[[Int]],Integer)]
nonOpenerSpots board dist rack = map kSpots' sqs
  where maxLen = length rack
        sqs = sqsThatTouch board maxLen
        kSpots' (sq,dir,len,thru) = (sq,dir,kSpots len dist rack,thru)

nonOpenerSetSpots :: Board -> TileDist -> Rack
                           -> [((Int,Int),Dir,Int,[(Integer,Multiset Int)],Integer)]
nonOpenerSetSpots board dist rack = map kSetSpots' sqs
  where maxLen = length rack
        sqs = sqsThatTouch board maxLen
        kSetSpots' (sq,dir,len,thru) = (sq,dir,len,kSets len dist rack,thru)

scoredSpots :: Layout -> Board -> TileDist -> Rack
                      -> [(Int,((Int,Int),Dir,[Int],Integer))]
scoredSpots layout board dist rack = sortBy descendingScore scored
  where scored = concatMap spotInfo spots
        spots = nonOpenerSpots board dist rack
        spotInfo (sq,dir,xs,thru) = map scoredSpot xs
          where
            scoredSpot x = (score,(sq,dir,x,thru))
              where
                score = scoreSpot baseScore wMul muls x
                wMul = product $ map ((layoutXWS layout) !) newSqs
                baseScore = bonus+hookScore+wMul*oldScore
                len = length x
                bonus = if len >= 7 then 50 else 0
                hookScore = scoreHooks layout board dist dir newSqs
                oldScore = sum $ map (`unsafeLookup` scores) oldTiles
                oldTiles = throughTilesAt board sq dir len
                scores = tileScores dist                
                newSqs = fromJust $ squaresAt board sq dir len
                muls = mulsAt layout board dir newSqs

couldFit :: Lexicon -> TileDist -> [Integer] -> Rack -> Multiset Int -> Bool
couldFit lex dist crosses rack set = all anyFits crosses
  where anyFits cross = cross==1 || any (isGoodWithProd lex cross) rack


countsHas :: (Eq a) => [(a,Int)] -> a -> Bool
countsHas counts x = any (\(y,n) -> y==x && n>0) counts

countsMinus :: (Eq a) => [(a,Int)] -> a -> [(a,Int)]
countsMinus ((y,n):cs) x = if x==y then (x,n-1):cs
                           else (y,n):(countsMinus cs x)

msHas :: (Eq a) => Multiset a -> a -> Bool
msHas set x = countsHas (toCounts set) x

nonZero :: (Eq a) => (a,Int) -> Bool
nonZero (_,0) = False
nonZero _     = True

msMinus :: (Eq a) => Multiset a -> a -> Multiset a
msMinus set x = fromCounts $ filter nonZero $ countsMinus (toCounts set) x

permsStartingWith :: (Eq a) => Multiset a -> [[a]] -> a -> [[a]]
permsStartingWith set cs x = if msHas set x then perms' x else []
  where perms' x = map ((:) x) $ Multi.permutations (msMinus set x)

constrainedPerms :: (Eq a) => Multiset a -> [[a]] -> [[a]]
constrainedPerms set []     = []
constrainedPerms set (c:cs) = concatMap perms c
  where perms x = if msHas set x then perms' x else []
        perms' x = if null cs then [[x]]
                   else map ((:) x) $ constrainedPerms (msMinus set x) cs

scoredSetSpots :: Lexicon -> Layout -> Board -> TileDist -> Rack
                          -> [(Int,((Int,Int),Dir,[Int]))]
scoredSetSpots lex layout board dist rack = sortBy descendingScore scored
  where scored = concatMap spotInfo spots
        spots = nonOpenerSetSpots board dist rack
        spotInfo :: ((Int,Int),Dir,Int,[(Integer,Multiset Int)],Integer)
                    -> [(Int,((Int,Int),Dir,[Int]))]
        spotInfo (sq,dir,len,xs,thru) = concatMap scoredSpots' $ filter good xs
          where
            good (prod,_) = isGoodWithProd lex thru prod
            scoredSpots' (_,set) = if couldFit' set then
                                     map scoredSpot $ Multi.permutations set
                                   else []
              where scoredSpot x = (scoreSpot baseScore wMul muls x,(sq,dir,x))
            couldFit' = couldFit lex dist crosses rack
            newSqs = fromJust $ squaresAt board sq dir len
            crosses = crossProdsAt board dir newSqs
            muls = mulsAt layout board dir newSqs
            wMul = product $ map ((layoutXWS layout) !) newSqs
            baseScore = bonus+hookScore+wMul*oldScore
            bonus = if len >= 7 then 50 else 0
            hookScore = scoreHooks layout board dist dir newSqs
            oldScore = sum $ map (`unsafeLookup` scores) oldTiles
            oldTiles = throughTilesAt board sq dir len
            scores = tileScores dist                
     
sqLenMoves :: Layout -> Lexicon -> TileDist -> Board -> Rack -> (Int,Int)
                     -> Dir -> Int -> [(Int,Move)]
sqLenMoves layout lex dist board rack sq dir len =
  mergeMoves $ map spotMoves' spots
  where spots = if (isJust squares) && touches then
                  kSpots len dist rack
                else []  
        squares = squaresAt board sq dir len
        touches = (through > 1) || (hooks board (fromJust squares) dir)
        through = throughAt board sq dir len
        crosses = crossProdsAt board dir (fromJust squares)
        wMul = product $ map ((layoutXWS layout) !) newSqs
        muls = mulsAt layout board dir newSqs
        newSqs = fromJust $ squaresAt board sq dir len
        oldScore = sum $ map (`unsafeLookup` scores) oldTiles
        oldTiles = throughTilesAt board sq dir len
        bonus = if len >= 7 then 50 else 0        
        hookScore = scoreHooks layout board dist dir newSqs
        scores = tileScores dist
        baseScore = bonus+hookScore+wMul*oldScore
        spotMoves' = spotMoves layout lex dist board sq dir through crosses
                               rack baseScore wMul muls

kSpots :: Int -> TileDist -> Rack -> [[Int]]
kSpots k dist rack = concat $ map Multi.permutations subsets
  where subsets = kSubsets k $ Multi.fromList scores
        scores = map (`unsafeLookup` (tileScores dist)) rack

kSetSpots :: Int -> TileDist -> Rack -> [(Integer,[[Int]])]
kSetSpots k dist rack = map prodSet rackSets
  where rackSets = kSubsets k $ Multi.fromList rack
        prodSet set = (product $ toList set,spots set)
        spots set = Multi.permutations $ Multi.fromList $ setScores $ toList set
        setScores set = map (`unsafeLookup` (tileScores dist)) set

kSets :: Int -> TileDist -> Rack -> [(Integer,Multiset Int)]
kSets k dist rack = map prodSet rackSets
  where rackSets = kSubsets k $ Multi.fromList rack
        prodSet set = (product $ toList set,scoreSet set)
        scoreSet set = Multi.fromList $ setScores $ toList set
        setScores set = map (`unsafeLookup` (tileScores dist)) set

combine' :: Array Int Integer -> [([[Integer]],[Int])] -> [Int] -> [Integer]
                              -> [Array Int Integer]
combine' filled []                       indices perm = [filled']
  where filled' = filled // (zip indices perm)
combine' filled ((perms',indices'):subs) indices perm =
  concat $ map (combine' filled' subs indices') perms'
  where filled' = filled // (zip indices perm)
  
combine :: Int -> [([[Integer]],[Int])] -> [[Integer]]
combine n ((perms,indices):subs) = map elems (concat combined)
  where combined :: [[Array Int Integer]]
        combined = map combine'' perms
        combine'' = combine' (listArray (0,n-1) (repeat 0)) subs indices

subPerms :: TileDist -> [Int] -> Rack -> [([[Integer]],[Int])]
subPerms dist spot rack = map subPerms $ List.nub . List.sort $ spot
  where subPerms x = (ofScore x,List.elemIndices x spot)
        ofScore x = Perm.permuteMultiset $ filter ((== x) . score) rack
        score x = unsafeLookup x (tileScores dist)

spotPerms :: TileDist -> [Int] -> Rack -> [[Integer]]
spotPerms dist spot rack = combine (length spot) $ subPerms dist spot rack

spotSetPerms :: TileDist -> [Int] -> TileSet -> [[Integer]]
spotSetPerms dist spot set = combine (length spot) $ subPerms dist spot set'
  where set' = toList set

count :: [Int] -> Int -> Int
count []     _ = 0
count (x:xs) y = (count xs y) + (if (x==y) then 1 else 0)

subSets :: TileDist -> [Int] -> Rack -> [[TileSet]]
subSets dist spot rack = map xSubSets $ List.nub . List.sort $ spot
  where xSubSets x = kSubsets (count spot x) $ ofScore x
        ofScore x = Multi.fromList $ filter ((== x) . score) rack
        score x = unsafeLookup x (tileScores dist)

combineSets :: [[TileSet]] -> [TileSet]
combineSets []           = []
combineSets [sets]       = sets
combineSets (sets:sets') = map Multi.disjUnions pairs
  where pairs = [[set,set'] | set <- sets, set' <- combineSets sets']

spotSets :: TileDist -> [Int] -> Rack -> [TileSet]
spotSets dist spot rack = combineSets $ subSets dist spot rack

spotMoves :: Layout -> Lexicon -> TileDist -> Board -> (Int,Int) -> Dir
                    -> Integer -> [Integer] -> Rack -> Int -> Int -> [Int]
                    -> [Int] -> [(Int,Move)]
spotMoves layout lex dist board sq dir through crosses rack
                 baseScore wMul muls spot =
  mergeMoves $ map movesAt $ filter good sets
  where sets = spotSets dist spot rack
        good set = isGoodWith lex through $ toList set
        movesAt = setMovesAt layout lex dist board sq dir through
                             crosses score spot
        score = scoreSpot baseScore wMul muls spot

covered :: Board -> (Int,Int) -> Bool
covered board sq = ((boardPrimes board) ! sq) > 1

safeCovered :: Board -> (Int,Int) -> Bool
safeCovered board sq = isOnBoard board sq && covered board sq

hooksAt :: Board -> Dir -> (Int,Int) -> Bool
hooksAt board dir sq = before || after
  where before = safeCovered board beforeSq
        after = safeCovered board afterSq
        beforeSq = prevSq sq $ crossDir dir
        afterSq = nextSq sq $ crossDir dir
        
hooks :: Board -> [(Int,Int)] -> Dir -> Bool
hooks board sqs dir = any (hooksAt board dir) sqs

connected :: Board -> Dir -> Bool -> (Int,Int) -> [(Int,Int)]
connected board dir fwd sq = if safeCovered board next then
                               next:connected board dir fwd next
                             else []  
  where next = if fwd then nextSq sq dir else prevSq sq dir
        
crossAt :: Board -> Dir -> (Int,Int) -> [(Int,Int)]
crossAt board dir sq = before ++ after
  where before = connected board (crossDir dir) False sq
        after = connected board (crossDir dir) True sq
        
crossesAt :: Board -> Dir -> [(Int,Int)] -> [[(Int,Int)]]
crossesAt board dir sqs = map (crossAt board dir) sqs

crossProdsAt :: Board -> Dir -> [(Int,Int)] -> [Integer]
crossProdsAt board dir sqs = map (sqProd board) $ crossesAt board dir sqs

scoreHook :: Layout -> Board -> TileDist -> Dir -> (Int,Int) -> Int
scoreHook layout board dist dir sq = sum crossScores
  where crossScores = map (`unsafeLookup` scores) $ sqTiles board crossSqs
        crossSqs = crossAt board dir sq
        scores = tileScores dist
        
scoreHooks :: Layout -> Board -> TileDist -> Dir -> [(Int,Int)] -> Int
scoreHooks layout board dist dir sqs =
  sum $ map (scoreHook layout board dist dir) sqs

setMovesAt :: Layout -> Lexicon -> TileDist -> Board -> (Int,Int) -> Dir 
                     -> Integer -> [Integer] -> Int -> [Int] -> TileSet
                     -> [(Int,Move)]
setMovesAt layout lex dist board sq dir through crosses score spot set =
  map toScoredMove validPerms
  where validPerms = filter fits' perms
        perms = if good then spotSetPerms dist spot set else []
        good = isGoodWith lex through $ toList set
        len = length spot
        fits' = fits lex crosses
        toScoredMove perm = (score,Move perm sq dir)

unfold1 :: (a -> Maybe a) -> a -> [a]
unfold1 f x = case f x of 
  Nothing -> [x] 
  Just y  -> x : unfold1 f y

-- | Generates all permutations of a multiset 
--   (based on \"algorithm L\" in Knuth; somewhat less efficient). 
--   The order is lexicographic.  
permuteBy :: (Eq a, Ord a) => (a -> a -> Ordering) -> [a] -> [[a]] 
permuteBy cmp xs = unfold1 next (sortBy cmp xs) where
  -- next :: [a] -> Maybe [a]
  next xs = case findj (reverse xs,[]) of 
    Nothing -> Nothing
    Just ( (l:ls) , rs) -> Just $ inc l ls (reverse rs,[]) 
    Just ( [] , _ ) -> error "permute: should not happen"

  -- we use simple list zippers: (left,right)
  -- findj :: ([a],[a]) -> Maybe ([a],[a])   
  findj ( xxs@(x:xs) , yys@(y:_) ) = case cmp x y of
    LT        -> Just ( xxs , yys )    
    otherwise -> findj ( xs , x : yys )

  findj ( x:xs , [] ) = findj ( xs , [x] )  
  findj ( [] , _ ) = Nothing
  
  -- inc :: a -> [a] -> ([a],[a]) -> [a]
  inc u us ( (x:xs) , yys ) = case cmp u x of
    LT        -> reverse (x:us)  ++ reverse (u:yys) ++ xs
    otherwise -> inc u us ( xs , x : yys ) 
  inc _ _ ( [] , _ ) = error "permute: should not happen"
      
-- Given a set of tiles and per-square multipliers for positions on the
-- board, returns a list of permutations from highest to lowest score.
descendingPerms :: TileDist -> [Int] -> TileSet -> [[Integer]]
descendingPerms dist muls set =
  map orderForBoard $ permuteBy (descendingUniq dist) (toList set)
  where
    ranks = reverse $ map fst $ sortBy (comparing snd) $ zip [1..] muls
    p = if (length muls) == 7 then Perm.toPermutation [2,7,3,4,1,5,6]
        else Perm.inverse $ Perm.toPermutation ranks
    orderForBoard = Perm.permuteList p

scoreOpener :: Layout -> TileDist -> Move -> Int
scoreOpener layout dist (Move word sq dir) = score
  where score = bonus+mul*sum letterScores
        mul = product $ map ((layoutXWS layout) !) squares
        letterScores = zipWith (*) xls wordScores
        xls = map ((layoutXLS layout) !) squares
        wordScores = map (`unsafeLookup` scores) word
        squares = map makeSq $ range $ listBounds word
        coordMover = case dir of
                       Down   -> first
                       Across -> second
        makeSq delta = coordMover (+ delta) sq
        bonus = if length word >= 7 then 50 else 0
        scores = tileScores dist

scoreMove :: Layout -> Board -> TileDist -> Move -> Int
scoreMove layout board dist (Move word sq dir) = score
  where score = bonus+hookScore+wMul*(newScore+oldScore)
        wMul = product $ map ((layoutXWS layout) !) newSqs
        newScore = sum $ zipWith (*) muls newScores
        muls = mulsAt layout board dir newSqs
        newScores = map (`unsafeLookup` scores) word
        newSqs = fromJust $ squaresAt board sq dir $ length word
        oldScore = sum $ map (`unsafeLookup` scores) oldTiles
        oldTiles = throughTilesAt board sq dir $ length word
        bonus = if length word >= 7 then 50 else 0
        hookScore = scoreHooks layout board dist dir newSqs
        scores = tileScores dist

scoreSpot :: Int -> Int -> [Int] -> [Int] -> Int
scoreSpot baseScore wMul muls spot = score
  where score = baseScore+wMul*newScore
        newScore = sum $ zipWith (*) muls spot

descendingUniq dist x y = case compare (score x) (score y) of
                            LT -> GT
                            GT -> LT
                            EQ -> compare x y
  where score x = unsafeLookup x (tileScores dist)
        
-- main :: IO ()
-- main = do
-- --  print $ permsStartingWith (Multi.fromList "ABC") ["B","C"] 'C'
--   mapM_ print $ constrainedPerms (Multi.fromList "ABCDEFG")
--     ["ABCDEFG","B","ABCDEFG","D","ABCDEFG","ABCDEFG","ABCDEFG"]
  
main :: IO ()
main = do
  putStrLn "Loading..."
  twl <- lexiconFromFile twlFile
  putStrLn "Loaded TWL."
  let !board = emptyBoard standard
  let !english = TileDist (englishScores twl)
  let !rack = fromJust $ readRack twl "QUIZJAX"
  putStrLn $ showRack twl rack
  start <- getCPUTime
  let !moves = topMoves twl standard board english rack
  end <- getCPUTime
  let diff = fromIntegral (end-start) / (10^12)
  let !top = head moves
  let !topString = showMove twl board top
  let !score = scoreMove standard board english top    
  -- printf "found %i top moves (such as %s for %i) in %0.5fs\n"
  --   (length moves::Int) (topString::String) (score::Int) (diff::Double)
  let !board' = makeMove board top
  putStr $ unlines $ labelBoard standard twl board'
  -- let !rack' = fromJust $ readRack twl "PHOBIAS"
  let !rack' = fromJust $ readRack twl "JIGABOO"
  putStrLn $ showRack twl rack'
  start' <- getCPUTime
  --let !moves' = topMoves twl standard board' english rack'
  --let !spots = nonOpenerSpots board' english rack'
  --let !nSpots = sum $ map (\(_,_,x) -> length x) spots
  --let !scored = scoredSpots standard board' english rack'
  --let !spots = nonOpenerSetSpots board' english rack'
  let !scored = scoredSetSpots twl standard board' english rack'
  end' <- getCPUTime
  let diff' = fromIntegral (end'-start') / (10^12)
  printf "found %i in %0.5fs\n"
    (length scored::Int) (diff'::Double)
  mapM_ print $ take 5 scored
  --let !top' = head moves'      
  --let !diff' = fromIntegral (end'-start') / (10^12)
  --let !topString' = showMove twl board' top'
  --let !score' = scoreMove standard board' english top'
  --printf "found %i top moves (such as %s for %i) in %0.5fs\n"
  --  (length moves'::Int) (topString'::String) (score'::Int) (diff'::Double)
  --printf "found the top move (%s for %i) in %0.5fs\n"
  --  (topString'::String) (score'::Int) (diff'::Double)      
  --putStrLn "top moves:"
  --mapM_ print $ map (showMove twl board') moves'
