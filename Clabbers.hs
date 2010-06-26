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

module Main (
             main
            ,loadLex
            ,blankHack'
            ,blankHack
            ,blankify 
            ,readRack
            ,showRack 
            ) where

import Control.Arrow
import Control.Monad
import Control.Monad.ST
import Data.Array as A
import Data.Array.IO
import Data.Array.ST
import Data.Binary
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Lazy as LazyB
import Data.Char
import Data.List (groupBy, intersperse, map, nub, sort, sortBy, zip)
import qualified Data.List as List
import Data.List.Utils (mergeBy)
import Data.Map (Map, fromList, keys)
import qualified Data.Map as Map
import Data.Maybe
import Data.Numbers
import Data.Numbers.Primes as Primes
import Data.Ord (comparing)
import Data.Set (Set, member)
import qualified Data.Set as Set
import Debug.Trace (trace)
import Math.Combinatorics.Multiset (Multiset, kSubsets, permutations, toList,
                                    fromCounts, toCounts)
import qualified Math.Combinat.Permutations as Perm
import qualified Math.Combinatorics.Multiset as Multi
import System.CPUTime
import System.Directory
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

primesFromRawLex :: String -> IO (Map Char Letter)
primesFromRawLex name = do
  putStrLn $ "Computing tile-to-prime mapping for " ++ name ++ " lexicon..."
  counts <- freqs $ rawLexFile name
  let sorted = map fst $ reverse $ sortBy (comparing snd) counts
  let ascii = filter isAscii sorted
  let letters = filter isUpper ascii
  let assocs = zip (letters ++ "?") Primes.primes
  let ps = fromList assocs
  writeFile (lexPrimesFile name) (show ps)
  return ps

unsafeLookup :: (Ord k) => k -> Map k a -> a
unsafeLookup x = fromJust . Map.lookup x

unpackWith :: (Char -> a) -> (ByteString -> [a])
unpackWith f = map f . B.unpack

wordProduct :: Map Char Letter -> ByteString -> Prod
wordProduct ps = product . unpackWith (`unsafeLookup` ps)

stringWordProduct :: Map Char Letter -> String -> Prod
stringWordProduct ps = product . map (`unsafeLookup` ps)

wordProductIn :: Lex -> String -> Prod
wordProductIn = stringWordProduct . lexPrimes

wordsetFromWords :: Map Char Letter -> [ByteString] -> Set Prod
wordsetFromWords ps = Set.fromList . map (wordProduct ps)

swap :: (a,b) -> (b,a)
swap (a,b) = (b,a)

inverseMap :: (Ord b) => Map a b -> Map b a
inverseMap = fromList . map swap . Map.assocs

data Lex = Lex (Map Char Tile) [ByteString] (Set Prod) Tile
lexPrimes (Lex ps _     _   _    ) = ps
lexWords  (Lex _  words _   _    ) = words
lexSet    (Lex _  _     set _    ) = set
lexBlank  (Lex _  _     _   blank) = blank
lexLetters  = inverseMap . lexPrimes
lexBLetters = Map.fromList . map (second toLower) . Map.assocs . lexLetters
lexLetter  lex x = unsafeLookup x (lexLetters lex)
lexBLetter lex x = unsafeLookup x (lexBLetters lex)
lexTiles lex = keys $ lexLetters lex
lexNonBlanks lex = filter (/= (lexBlank lex)) (lexTiles lex)

rawLexFile    name = "data/lexica/" ++ name ++ ".txt"
lexPrimesFile name = "data/lexica/" ++ name ++ ".shp"
lexSetFile    name = "data/lexica/" ++ name ++ ".shs"

primesFromFile :: String -> IO (Map Char Tile)
primesFromFile name = do
  contents <- readFile $ lexPrimesFile name
  return $ read contents
  
loadPrimes :: String -> IO (Map Char Tile)
loadPrimes name = do
  exists <- doesFileExist $ lexPrimesFile name
  if exists then primesFromFile name else primesFromRawLex name

wordsetFromFile :: String -> IO (Set Prod)
wordsetFromFile name = do
  contents <- LazyB.readFile $ lexSetFile name
  return $ decode contents

wordsetFromRawLex :: String -> Map Char Letter -> [ByteString] -> IO (Set Prod)
wordsetFromRawLex name primes words = do
  putStrLn $ "Creating wordset for " ++ name ++ " lexicon..."
  let set = wordsetFromWords primes words
  LazyB.writeFile (lexSetFile name) (encode set)
  return set

loadWordset :: String -> Map Char Letter -> [ByteString] -> IO (Set Prod)
loadWordset name primes words = do
  exists <- doesFileExist $ lexSetFile name
  if exists then wordsetFromFile name else wordsetFromRawLex name primes words
  
loadLex :: String -> IO (Lex)
loadLex name = do
  letterPrimes <- loadPrimes name
  contents <- B.readFile $ rawLexFile name
  let words = B.lines contents
  wordset <- loadWordset name letterPrimes words
  let blank = unsafeLookup '?' letterPrimes
  return $ Lex letterPrimes words wordset blank

isGoodIn :: Lex -> [Letter] -> Bool
isGoodIn lex word = member (product word) (lexSet lex)

isGoodWith :: Lex -> Prod -> [Letter] -> Bool
isGoodWith lex through word = member (through*(product word)) (lexSet lex)

showProd :: Lex -> Prod -> String
showProd lex prod = "<" ++ showRack lex (primeFactors prod) ++ ">"

isGoodWithBlank :: Lex -> Prod -> TileSet -> Bool
isGoodWithBlank lex through tileSet =
  trace ("isGoodWithBlank " ++ showProd lex through ++ " "
         ++ showSet lex tileSet
         ++ ": " ++ show (any good prods)) $
  any good prods
  where good prod = member prod (lexSet lex)
        prods = map ((*through) . product . toList) $ blankify lex tileSet

isGoodWithProd :: Lex -> Prod -> Prod -> Bool
isGoodWithProd lex through prod = if prod==lexBlank lex then blank else natural
  where natural = member (through*prod) (lexSet lex)
        blank = any (isGoodWithProd lex through) (lexNonBlanks lex)

type Tile = Integer
type TileSet = Multiset Tile

type Designated = (Letter,Tile)
type Prod = Integer
type Letter = Integer
type LetterSet = Multiset Letter

type Score = Int
type ScoreSet = Multiset Score

-- this needs to have counts too
data Dist = Dist (Map Integer Score)
distScores (Dist scores) = scores

englishScores :: Lex -> (Map Tile Score)
englishScores lex = fromList $ zip ps scores
  where ps = lookupPrimes lex $ '?':['A'..'Z']
        scores = 0:[1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10]

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

type Sq = (Int,Int)
type SqGrid = Array Sq
textMuls :: [String] -> Char -> (SqGrid Int)
textMuls grid c = listsArray $ map stringMul grid
  where stringMul = map parseMul . words
        parseMul ['2',x] = if x == c then 2 else 1
        parseMul ['3',x] = if x == c then 3 else 1
        parseMul _       = 1

gridSize :: SqGrid a -> (Int,Int)
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

data Board = Board Bool (SqGrid Letter) (SqGrid Tile)
boardIsEmpty (Board empty _       _    ) = empty
boardLetters (Board _     letters _    ) = letters
boardTiles   (Board _     _       tiles) = tiles

emptyGrid :: Layout -> SqGrid Integer
emptyGrid layout = listArray (bounds (layoutXWS layout)) (repeat 0)

emptyBoard :: Layout -> Board
emptyBoard layout = Board True (emptyGrid layout) (emptyGrid layout)


data Layout = Layout (SqGrid Int) (SqGrid Int) Sq
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

displayTile :: Lex -> Letter -> Tile -> Char
displayTile _   0      0                           = ' '
displayTile lex letter tile | tile==(lexBlank lex) = lexBLetter lex letter
displayTile lex letter _                           = lexLetter lex letter

letterGrid :: Lex -> Board -> [String]
letterGrid lex board = splitAtEach cols disps
  where disps = zipWith (displayTile lex) letters tiles
        letters = elems $ boardLetters board
        tiles = elems $ boardTiles board
        (rows,cols) = gridSize $ boardLetters board

boardGrid :: [String] -> [String] -> [String]
boardGrid = zipWith rowString
  where rowString = zipWith square
        square x ' ' = x -- empty  -> premium
        square _ x   = x -- letter -> letter

labelBoard :: Layout -> Lex -> Board -> [String]
labelBoard layout lex board = prettifyGrid bg
  where bg = boardGrid premiums letters
        premiums = premiumsTextGrid (layoutPremiumGrids layout)
        letters = letterGrid lex board

isAsciiAlpha :: Char -> Bool
isAsciiAlpha c = isAlpha c && isAscii c

type Pos = (Sq,Dir)
data Dir = Down | Acrs
instance Show Dir where
  show Down = "Down"
  show Acrs = "Acrs"
  
data Move = Move [Letter] [Tile] Pos

-- It would be nice if instead of Maybe Move, this returned something
-- like Either Move ReadMoveException, where the exception explains
-- where the parse went wrong.
readMove :: Lex -> String -> Maybe Move
readMove lex s = readMoveTokens lex (words s)

readMoveTokens :: Lex -> [String] -> Maybe Move
readMoveTokens lex (pos:[letters]) = do
  pos' <- readPos pos
  ps <- safeLookupPrimes lex letters
  return $ Move ps ps pos'
readMoveTokens _   _               = Nothing

readPos :: String -> Maybe Pos
readPos pos = do
  (sq,dir) <- splitPos pos
  sq' <- readSq sq
  return (sq',dir)
  
splitPos :: String -> Maybe ((String,Char),Dir)
splitPos pos = if isAsciiAlpha (head pos) then
                 Just ((tail pos,head pos), Down)
               else if isAsciiAlpha (last pos) then
                      Just ((init pos,last pos), Acrs)
                    else Nothing
                               
readSq :: (String,Char) -> Maybe Sq
readSq (num,alpha) = if not (null num) && all isDigit num then
                       Just (-1+read num::Int,ord (toLower alpha)-ord 'a')
                     else Nothing

lookupLetters :: Lex -> [Letter] -> String
lookupLetters lex = map lookup
  where lookup p = unsafeLookup p (lexLetters lex)

safeLookupPrime :: Lex -> Char -> Maybe Tile
safeLookupPrime lex '?' = Just $ lexBlank lex
safeLookupPrime lex c   = Map.lookup c (lexPrimes lex)

safeLookupPrimes :: Lex -> String -> Maybe [Tile]
safeLookupPrimes _   []     = Just []
safeLookupPrimes lex (x:xs) = do
  p <- safeLookupPrime lex x
  ps <- safeLookupPrimes lex xs
  return (p:ps)
  
lookupPrimes :: Lex -> String -> [Tile]
lookupPrimes lex = map lookup
  where lookup letter = unsafeLookup letter (lexPrimes lex)

markThrough :: Board -> [(Int,Char)] -> [(Int,Char)] -> String
markThrough board new old = concat $ map renderChunk chunks
  where renderChunk (True:_,x)  = x
        renderChunk (False:_,x) = "(" ++ x ++ ")"
        all = zip new (repeat True) ++ zip old (repeat False)
        (sorted,isNew) = unzip $ sortBy (comparing (fst . fst)) all
        letters = snd $ unzip sorted
        chunks = map unzip $ groupBy sameGroup $ zip isNew letters
        sameGroup (x,_) (y,_) = x == y

sqNum :: Sq -> String
sqNum (row,_) = show (row+1)

sqAlpha :: Sq -> String
sqAlpha (_,col) = [chr (col+ord 'a')]

showPos :: Pos -> String
showPos (sq,Acrs) = sqNum sq ++ sqAlpha sq
showPos (sq,Down) = sqAlpha sq ++ sqNum sq

showMove :: Lex -> Board -> Move -> String
showMove lex board (Move letters tiles (sq,dir)) = pos ++ " " ++ disps
  where pos = showPos (sq,dir)
        disps = markThrough board new old
        axis = case dir of
                 Down -> fst
                 Acrs -> snd
        new = zip newSqs' newLetters
        newSqs' = map axis newSqs
        Just newSqs = squaresAt board (sq,dir) $ length letters
        newLetters = lookupLetters lex letters
        old = zip oldSqs' oldLetters
        oldSqs' = map axis oldSqs
        oldSqs = throughSqsAt board (sq,dir) $ length letters
        oldLetters = lookupLetters lex oldTiles
        oldTiles = throughTilesAt board (sq,dir) $ length letters

makeMove :: Board -> Move -> Board
makeMove board (Move wordLetters wordTiles pos) = Board False letters' tiles'
  where letters' = boardLetters board // letterAssocs
        tiles' = boardTiles board // tileAssocs
        Just sqs = squaresAt board pos $ length wordLetters
        letterAssocs = zip sqs wordLetters
        tileAssocs = zip sqs wordTiles

-- Racks should really be of type (Multiset Tile)
type Rack = [Tile]

readRack :: Lex -> String -> Maybe Rack
readRack = safeLookupPrimes

-- would be nice to show this in alphagram order
showRack :: Lex -> Rack -> String
showRack lex = sort . (lookupLetters lex)

type Scored a = (Score,a)

descendingScore :: Scored a -> Scored b -> Ordering
descendingScore (x,_) (y,_) = compare y x

-- Flatten a list of lists of Scored Moves, each already sorted by
-- descending score, maintaining the ordering.
mergeMoves :: [[Scored Move]] -> [Scored Move]
mergeMoves = foldl (mergeBy descendingScore) []

onBoard :: Board -> Sq -> Maybe Sq
onBoard board (row,col) | row < 0      = Nothing
                        | col < 0      = Nothing
                        | row > maxRow = Nothing
                        | col > maxCol = Nothing
                        | otherwise    = Just (row,col)
  where (_,(maxRow,maxCol)) = bounds $ boardLetters board

isOnBoard :: Board -> Sq -> Bool
isOnBoard board sq = isJust $ onBoard board sq

safeSquare :: Board -> Sq -> Maybe [Sq]
safeSquare board sq = do
  sq' <- onBoard board sq
  return $ if ((boardLetters board) ! sq) == 0 then [sq] else []

crossDir :: Dir -> Dir
crossDir Down = Acrs
crossDir Acrs = Down

prevSq :: Sq -> Dir -> Sq
prevSq (row,col) Down = (row-1,col)
prevSq (row,col) Acrs = (row,col-1)

nextSq :: Sq -> Dir -> Sq
nextSq (row,col) Down = (row+1,col)
nextSq (row,col) Acrs = (row,col+1)

squaresAt :: Board -> Pos -> Int -> Maybe [Sq]
squaresAt _     _        0   = Just []
squaresAt board (sq,dir) len = do
  sqHere <- safeSquare board sq
  let sqHereLen = if null sqHere then 0 else 1
  let sq' = nextSq sq dir
  let len' = len-sqHereLen
  moreSqs <- squaresAt board (sq',dir) len' 
  return $ sqHere ++ moreSqs
  
mulAt :: Layout -> Board -> Dir -> Sq -> Int
mulAt layout board dir sq = ways * xls
  where ways = if (hooksAt board dir sq) then 2 else 1
        xls = (layoutXLS layout) ! sq
        
mulsAt :: Layout -> Board -> Dir -> [Sq] -> [Int]
mulsAt layout board dir sqs = map (mulAt layout board dir) sqs

fitsAt :: Lex -> Prod -> Letter -> Bool
fitsAt _   1     _ = True
fitsAt lex cross p = member (p*cross) (lexSet lex)
  
fits :: Lex -> [Prod] -> [Letter] -> Bool
fits _   []       _    = True
fits lex cs ps = and $ zipWith (fitsAt lex) cs ps

throughSqsAt :: Board -> Pos -> Int -> [Sq]
throughSqsAt _     _       (-1) = []
throughSqsAt board (sq,dir) len  = if isOnBoard board sq then throughs else []
  where throughs = sqHere ++ throughSqsAt board (sq',dir) len'
        letter = (boardLetters board) ! sq
        (sqHere,len') = if letter == 0 then ([],len-1) else ([sq],len)
        sq' = nextSq sq dir

throughTilesAt :: Board -> Pos -> Int -> [Letter]
throughTilesAt board pos len = map ((boardLetters board) !) sqs
  where sqs = throughSqsAt board pos len

throughAt :: Board -> Pos -> Int -> Prod
throughAt board pos len = product $ throughTilesAt board pos len

sqTiles :: Board -> [Sq] -> [Letter]
sqTiles board sqs = map ((boardLetters board) !) sqs

sqProd :: Board -> [Sq] -> Prod
sqProd board sqs = product $ sqTiles board sqs

-- rack -> list of moves tied for highest score
topMoves :: Lex -> Layout -> Board -> Dist -> Rack -> [Move]
topMoves lex layout board dist rack = top moves
  where top [] = []
        top x  = snd $ unzip $ head $ groupBy sameScore x
        moves = topScored lex layout board dist rack spots
        spots = if boardIsEmpty board then openers else nonOpeners
        openers = openerSetSpots layout board dist rack
        nonOpeners = nonOpenerSetSpots board dist rack
        sameScore (x,_) (y,_) = x==y

topScored :: Lex -> Layout -> Board -> Dist -> Rack
                 -> [(Pos,Int,[(TileSet,ScoreSet)],Prod)] -> [Scored Move]
topScored lex layout board dist rack spots = mergeMoves $ map spotMoves topSpots
  where topSpots = head $ groupBy sameScore scored
        scored = scoreSetSpots lex layout board dist spots
        sameScore (x,_) (y,_) = x==y
        spotMoves = setSpotMoves lex board dist rack

letterCanHook :: Lex -> Prod -> Letter -> Bool
letterCanHook lex cross letter = isGoodWith lex cross [letter]

lettersThatHook :: Lex -> Prod -> Tile -> [Letter]
lettersThatHook lex cross tile = if tile==lexBlank lex then blank else natural
  where natural = if letterCanHook lex cross tile then [tile] else []
        blank = filter (letterCanHook lex cross) (lexNonBlanks lex)
        
tileConstraints :: Lex -> Dist -> [Tile] -> [Score] -> Rack -> [[Letter]]
tileConstraints lex dist crosses set rack =
  trace ("tileConstraints " ++ show (map (showProd lex) crosses) ++ " "
         ++ show set ++ " " ++ showRack lex rack
         ++ ": " ++ show (map (map (showProd lex)) (zipWith workWith crosses set))) $
  zipWith workWith crosses set
  where
    ofScore x = filter ((== x) . score) rack
    score x = unsafeLookup x (distScores dist)
    workWith cross scr = sortUniq $ if cross==1 then ofScore scr
                                    else working cross $ ofScore scr
    working cross tiles = nub $ concatMap (lettersThatHook lex cross) tiles

setSpotMoves :: Lex -> Board -> Dist -> Rack -> Scored (Pos,TileSet,[Score])
                    -> [Scored Move]
setSpotMoves lex board dist rack (scr,((sq,dir),tileSet,set)) =
  map toScoredMove perms
  where perms = constrainedPerms tileSet (constraints' tileSet)
        constraints' tileSet = tileConstraints lex dist crosses set (toList tileSet)
        crosses = crossProdsAt board dir newSqs
        newSqs = fromJust $ squaresAt board (sq,dir) (length set)
        toScoredMove perm = (scr,Move perm perm (sq,dir))

hitCenter :: Layout -> Board -> (Pos,Int) -> Bool
hitCenter layout board (pos,len) = (isJust squares) && hits
  where squares = squaresAt board pos len
        hits = elem (layoutStart layout) (fromJust squares)
        
touch :: Board -> (Pos,Int) -> Bool
touch board ((sq,dir),len) = (isJust squares) && starts && touches
  where squares = squaresAt board (sq,dir) len
        starts = not $ safeCovered board $ prevSq sq dir
        touches = (through > 1) || (hooks board (fromJust squares) dir)
        through = throughAt board (sq,dir) len

addThrough :: Board -> (Pos,Int) -> (Pos,Int,Prod)
addThrough board (pos,len) = (pos,len,through)
  where through = throughAt board pos len

sqsThatHitCenter :: Layout -> Board -> Int -> [(Pos,Int,Prod)]
sqsThatHitCenter layout board rackSize =
  map (addThrough board) $ filter (hitCenter layout board) sqs
  where sqs = [(((r,c),Acrs),len) | len <- lens, r <- rows, c <- cols]
        bounds' x = ((r,r'),(c,c')) where ((r,c),(r',c')) = bounds x
        (rows,cols) = both range $ bounds' $ boardLetters board
        lens = [7,6..2]

sqsThatTouch :: Board -> Int -> [(Pos,Int,Prod)]
sqsThatTouch board rackSize =
  map (addThrough board) $ filter (touch board) sqs
  where sqs = [(((r,c),d),len) | len <- [7], r <- [6], c <- [2], d <- [Acrs]]
        bounds' x = ((r,r'),(c,c')) where ((r,c),(r',c')) = bounds x
        (rows,cols) = both range $ bounds' $ boardLetters board
        lens = [7,6..1]
        dirs = [Down, Acrs]
        
openerSetSpots :: Layout -> Board -> Dist -> Rack
                         -> [(Pos,Int,[(TileSet,ScoreSet)],Prod)]
openerSetSpots layout board dist rack = map kSets' sqs
  where maxLen = length rack
        sqs = sqsThatHitCenter layout board maxLen
        kSets' (pos,len,thru) = (pos,len,kSets len dist rack,thru)

showStringList' [] = "]"
showStringList' [x] = x ++ "]"
showStringList' (x:xs) = x ++ "," ++ showStringList' (xs)

showStringList [] = "[]"
showStringList x = "[" ++ showStringList' x

showSet lex set = "{" ++ showRack lex (toList set) ++ "}"

showSets lex (tileSet,scoreSet) = "(" ++ tileSet' ++ "," ++ scoreSet' ++ ")"
  where tileSet' = showSet lex tileSet
        scoreSet' = show $ toList scoreSet

showSetSpot :: Lex -> (Pos,Int,[(TileSet,ScoreSet)],Prod) -> String
showSetSpot lex (pos,len,sets,prod) =
  pos' ++ "(" ++ show len ++ ")" ++ " " ++ sets' ++ " " ++ prod'
  where pos' = showPos pos
        sets' = showStringList $ map (showSets lex) sets
        prod' = showProd lex prod
        
nonOpenerSetSpots :: Board -> Dist -> Rack
                           -> [(Pos,Int,[(TileSet,ScoreSet)],Prod)]
nonOpenerSetSpots board dist rack = map kSets' sqs
  where maxLen = length rack
        sqs = sqsThatTouch board maxLen
        kSets' (pos,len,thru) = (pos,len,kSets len dist rack,thru)

couldFit :: Lex -> Dist -> [Prod] -> Rack -> Bool
couldFit lex dist crosses rack =
  trace ("couldFit " ++ show (map (showProd lex) crosses) ++ " "
         ++ showRack lex rack ++ ": " ++ show (all anyFits crosses)) $
  all anyFits crosses
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

--    Letters that hook each cross
-- -> Prod of words' "through" letters
-- -> Tiles to be blank-designated (if applicable) and permuted
-- -> (Letter,Tile) permutations, ready to be turned into moves
-- blankifiedPerms :: [[Letter]] -> Prod -> TileSet -> [[(Letter,Tile)]]

--    Letters that hook each cross
-- -> (Letter,Tile) pairs including designated blanks
-- -> (Letter,Tile) permutations, ready to be turned into moves
-- letterTilePerms :: [[Letter]] -> Multiset (Letter,Tile) -> [[(Letter,Tile)]

constrainedPerms :: (Eq a) => Multiset a -> [[a]] -> [[a]]
constrainedPerms set []     = []
constrainedPerms set (c:cs) = concatMap perms c
  where perms x = if msHas set x then perms' x else []
        perms' x = if null cs then [[x]]
                   else map ((:) x) $ constrainedPerms (msMinus set x) cs

sortUniq :: (Ord a) => [a] -> [a]
sortUniq x = map head $ List.group $ List.sort x

constraints :: Lex -> Dist -> [Prod] -> [Tile] -> [[Score]]
constraints lex dist crosses rack =
  trace ("constraints " ++ show (map (showProd lex) crosses) ++ " "
         ++ showRack lex rack ++ ": " ++ show (map workWith crosses)) $
  map workWith crosses
  where
    scores = map (`unsafeLookup` (distScores dist)) rack
    workWith cross = sortUniq $ if cross==1 then scores else workingScrs cross
    workingScrs cross = map (`unsafeLookup` (distScores dist)) $ working cross
    working cross = filter (\x -> isGoodWithProd lex cross x) rack

showScoredSetSpot :: Lex -> Scored (Pos,TileSet,[Score]) -> String
showScoredSetSpot lex (sc,(pos,set,spot)) =
  "(" ++ show sc ++ "," ++ pos' ++ "," ++ set' ++ "," ++ show spot ++ ")"
  where pos' = showPos pos
        set' = "{" ++ (showRack lex $ toList set) ++ "}"

blankHack' :: Int -> [Tile] -> [[Letter]]
blankHack' 0 _       = [[]]
blankHack' _ []      = []
blankHack' n letters = withHead ++ withTail
  where withHead = map ((head letters) :) $ blankHack' (n-1) letters
        withTail = blankHack' n (tail letters)

blankHack :: Lex -> Int -> [[Letter]]
blankHack lex n = blankHack' n (lexNonBlanks lex)

blankify :: Lex -> TileSet -> [LetterSet]
blankify lex tileSet = map Multi.fromList $ map (++ naturals) blanks
  where tiles = toList tileSet
        naturals = filter (/= lexBlank lex) tiles
        blanks = blankHack lex ((length tiles)-(length naturals))

spotInfo :: Lex -> Layout -> Board -> Dist
                -> (Pos,Int,[(TileSet,ScoreSet)],Integer)
                -> [Scored (Pos,LetterSet,[Score])]
spotInfo lex layout board dist ((sq,dir),len,xs,thru) =
  concatMap scoredSpots' $ filter good xs
  where blankify' (tileSet,s) = map (\x -> (x,s)) $ blankify lex tileSet
        good (tileSet,_) = isGoodWithBlank lex thru tileSet
        scoredSpots' (letterSet,set) = if couldFit' letterSet then
                                         map scoredSpot $ perms letterSet set
                                       else []
          where scoredSpot x = (scoreSpot baseScr wMul muls x,((sq,dir),letterSet,x))
        perms letterSet set = constrainedPerms set (constraints' letterSet)
        constraints' tileSet = constraints lex dist crosses (toList tileSet)
        couldFit' letterSet = couldFit lex dist crosses (toList letterSet)
        newSqs = fromJust $ squaresAt board (sq,dir) len
        crosses = crossProdsAt board dir newSqs
        muls = mulsAt layout board dir newSqs
        wMul = product $ map ((layoutXWS layout) !) newSqs
        baseScr = bonus+hookScr+wMul*oldScr
        bonus = if len >= 7 then 50 else 0
        hookScr = scoreHooks layout board dist dir newSqs
        oldScr = sum $ map (`unsafeLookup` scores) oldTiles
        oldTiles = throughTilesAt board (sq,dir) len
        scores = distScores dist                

scoreSetSpots :: Lex -> Layout -> Board -> Dist
                     -> [(Pos,Int,[(TileSet,ScoreSet)],Prod)]
                     -> [Scored (Pos,LetterSet,[Score])]
scoreSetSpots lex layout board dist spots = sortBy descendingScore scored
  where scored = concatMap spotInfo' spots
        spotInfo' = spotInfo lex layout board dist
        
kSets :: Int -> Dist -> Rack -> [(TileSet,ScoreSet)]
kSets k dist rack = map scoreSet' rackSets
  where rackSets = kSubsets k $ Multi.fromList rack
        scoreSet' set = (set,scoreSet set)
        scoreSet set = Multi.fromList $ setScores $ toList set
        setScores set = map (`unsafeLookup` (distScores dist)) set

covered :: Board -> Sq -> Bool
covered board sq = ((boardLetters board) ! sq) > 1

-- True if on board and containing a tile
-- False if empty or not on the board
safeCovered :: Board -> Sq -> Bool
safeCovered board sq = isOnBoard board sq && covered board sq

hooksAt :: Board -> Dir -> Sq -> Bool
hooksAt board dir sq = before || after
  where before = safeCovered board beforeSq
        after = safeCovered board afterSq
        beforeSq = prevSq sq $ crossDir dir
        afterSq = nextSq sq $ crossDir dir
        
hooks :: Board -> [Sq] -> Dir -> Bool
hooks board sqs dir = any (hooksAt board dir) sqs

connected :: Board -> Dir -> Bool -> Sq -> [Sq]
connected board dir fwd sq = if safeCovered board next then
                               next:connected board dir fwd next
                             else []  
  where next = if fwd then nextSq sq dir else prevSq sq dir
        
crossAt :: Board -> Dir -> Sq -> [Sq]
crossAt board dir sq = before ++ after
  where before = connected board (crossDir dir) False sq
        after = connected board (crossDir dir) True sq
        
crossesAt :: Board -> Dir -> [Sq] -> [[Sq]]
crossesAt board dir sqs = map (crossAt board dir) sqs

crossProdsAt :: Board -> Dir -> [Sq] -> [Prod]
crossProdsAt board dir sqs = map (sqProd board) $ crossesAt board dir sqs

scoreHook :: Layout -> Board -> Dist -> Dir -> Sq -> Score
scoreHook layout board dist dir sq = sum crossScores
  where crossScores = map (`unsafeLookup` scores) $ sqTiles board crossSqs
        crossSqs = crossAt board dir sq
        scores = distScores dist
        
scoreHooks :: Layout -> Board -> Dist -> Dir -> [Sq] -> Score
scoreHooks layout board dist dir sqs =
  sum $ map (scoreHook layout board dist dir) sqs

scoreMove :: Layout -> Board -> Dist -> Move -> Score
scoreMove layout board dist (Move letters tiles (sq,dir)) = score
  where score = bonus+hookScore+wMul*(newScore+oldScore)
        wMul = product $ map ((layoutXWS layout) !) newSqs
        newScore = sum $ zipWith (*) muls newScores
        muls = mulsAt layout board dir newSqs
        newScores = map (`unsafeLookup` scores) letters
        newSqs = fromJust $ squaresAt board (sq,dir) $ length letters
        oldScore = sum $ map (`unsafeLookup` scores) oldTiles
        oldTiles = throughTilesAt board (sq,dir) $ length letters
        bonus = if length letters >= 7 then 50 else 0
        hookScore = scoreHooks layout board dist dir newSqs
        scores = distScores dist

scoreSpot :: Int -> Int -> [Int] -> [Int] -> Int
scoreSpot baseScore wMul muls spot = score
  where score = baseScore+wMul*newScore
        newScore = sum $ zipWith (*) muls spot
        
-- main :: IO ()
-- main = do
--   putStrLn "Loading..."
--   twl <- loadLex "twl"
--   putStrLn "Loaded TWL."

main :: IO ()
main = do
  putStrLn "Loading..."
  twl <- loadLex "twl"
  putStrLn "Loaded TWL."
  let !board = emptyBoard standard
  let !english = Dist (englishScores twl)
  let !rack = fromJust $ readRack twl "QUIZJAX"
  putStrLn $ showRack twl rack
  start <- getCPUTime
  let !moves = topMoves twl standard board english rack
  end <- getCPUTime
  let diff = fromIntegral (end-start) / (10^12)
  let !top = head moves
  let !topString = showMove twl board top
  let !score = scoreMove standard board english top    
  let !board' = makeMove board top
  mapM_ putStrLn $ labelBoard standard twl board'
  let !rack' = fromJust $ readRack twl "J?MJAMS"
  putStrLn $ showRack twl rack' 
  start' <- getCPUTime
  -- let !spots = nonOpenerSetSpots board' english rack'
  -- let !scored = scoreSetSpots twl standard board' english spots    
  let !moves' = topMoves twl standard board' english rack'
  end' <- getCPUTime
  let diff' = fromIntegral (end'-start') / (10^12)
  --mapM_ putStrLn $ map (showSetSpot twl) spots
  --mapM_ print scored    
  let !top' = head moves'      
  let !topString' = showMove twl board' top'
  let !score' = scoreMove standard board' english top'
  printf "found %i top moves (such as %s for %i) in %0.5fs\n"
    (length moves'::Int) (topString'::String) (score'::Int) (diff'::Double)
