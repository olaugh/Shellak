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

letterPrimesFromWordFile :: FilePath -> IO (Map Char Letter)
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

data Lex = Lex (Map Char Letter) [ByteString] (Set Prod)
lexPrimes  (Lex ps _     _  ) = ps
lexWords   (Lex _  words _  ) = words
lexSet     (Lex _  _     set) = set
lexLetters                    = inverseMap . lexPrimes

lexFromFile :: FilePath -> IO (Lex)
lexFromFile file = do
  letterPrimes <- letterPrimesFromWordFile file
  contents <- B.readFile file
  let words = B.lines contents
  let !wordset = wordsetFromWords letterPrimes words
  return $ Lex letterPrimes words wordset

isGoodIn :: Lex -> [Letter] -> Bool
isGoodIn lex word = member (product word) (lexSet lex)

isGoodWith :: Lex -> Prod -> [Letter] -> Bool
isGoodWith lex through word = member (through*(product word)) (lexSet lex)

isGoodWithProd :: Lex -> Prod -> Prod -> Bool
isGoodWithProd lex through prod = member (through*prod) (lexSet lex)

type Tile = Integer
type TileSet = Multiset Tile

type Prod = Integer
type Letter = Integer
type LetterSet = Multiset Letter

type Score = Int
type ScoreSet = Multiset Score

data Dist = Dist (Map Integer Score)
distScores (Dist scores) = scores

englishScores :: Lex -> (Map Tile Score)
englishScores lex = fromList $ zip ps scores
  where ps = lookupPrimes lex ['A'..'Z']
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

data Board = Board Bool (SqGrid Letter)
boardIsEmpty (Board empty _      ) = empty
boardPrimes  (Board _      primes) = primes

emptyBoard :: Layout -> Board
emptyBoard layout =
  Board True (listArray (bounds (layoutXWS layout)) (repeat 0))

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

letterGrid :: Lex -> Board -> [String]
letterGrid lex board = splitAtEach cols letters
  where primes = boardPrimes board
        letters = map lookup (elems primes)
        lookup 0 = ' '
        lookup p = unsafeLookup p (lexLetters lex)
        (rows,cols) = gridSize primes

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
  
data Move = Move [Letter] Pos

-- It would be nice if instead of Maybe Move, this returned something
-- like Either Move ReadMoveException, where the exception explains
-- where the parse went wrong.
readMove :: Lex -> String -> Maybe Move
readMove lex s = readMoveTokens lex (words s)

readMoveTokens :: Lex -> [String] -> Maybe Move
readMoveTokens lex (pos:[letters]) = do
  pos' <- readPos pos
  ps <- safeLookupPrimes lex letters
  return $ Move ps pos'
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

safeLookupPrimes :: Lex -> String -> Maybe [Tile]
safeLookupPrimes _   []     = Just []
safeLookupPrimes lex (x:xs) = do
  p <- Map.lookup x (lexPrimes lex)
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
showMove lex board (Move word (sq,dir)) = pos ++ " " ++ letters
  where pos = showPos (sq,dir)
        letters = markThrough board new old
        axis = case dir of
                 Down -> fst
                 Acrs -> snd
        new = zip newSqs' newLetters
        newSqs' = map axis newSqs
        Just newSqs = squaresAt board (sq,dir) $ length word
        newLetters = lookupLetters lex word
        old = zip oldSqs' oldLetters
        oldSqs' = map axis oldSqs
        oldSqs = throughSqsAt board (sq,dir) $ length word
        oldLetters = lookupLetters lex oldTiles
        oldTiles = throughTilesAt board (sq,dir) $ length word

makeMove :: Board -> Move -> Board
makeMove (Board _ grid) (Move word (sq,dir)) = Board False grid'
  where grid' = grid // assocs
        assocs = zipWith makeAssoc word [0..]
        coordMover = case dir of
                       Down -> first
                       Acrs -> second
        makeAssoc letter delta = (sq',letter)
          where sq' = coordMover (+ delta) sq

type Rack = [Tile]

readRack :: Lex -> String -> Maybe Rack
readRack = safeLookupPrimes

showRack :: Lex -> Rack -> String
showRack = lookupLetters

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
  where (_,(maxRow,maxCol)) = bounds $ boardPrimes board

isOnBoard :: Board -> Sq -> Bool
isOnBoard board sq = isJust $ onBoard board sq

safeSquare :: Board -> Sq -> Maybe [Sq]
safeSquare board sq = do
  sq' <- onBoard board sq
  return $ if ((boardPrimes board) ! sq) == 0 then [sq] else []

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
        prime = (boardPrimes board) ! sq
        (sqHere,len') = if prime == 0 then ([],len-1) else ([sq],len)
        sq' = nextSq sq dir

throughTilesAt :: Board -> Pos -> Int -> [Letter]
throughTilesAt board pos len = map ((boardPrimes board) !) sqs
  where sqs = throughSqsAt board pos len

throughAt :: Board -> Pos -> Int -> Prod
throughAt board pos len = product $ throughTilesAt board pos len

sqTiles :: Board -> [Sq] -> [Letter]
sqTiles board sqs = map ((boardPrimes board) !) sqs

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
        sameScore (x,_) (y,_) = x == y

topScored :: Lex -> Layout -> Board -> Dist -> Rack
                 -> [(Pos,Int,[(TileSet,ScoreSet)],Prod)] -> [Scored Move]
topScored lex layout board dist rack spots = mergeMoves $ map spotMoves topSpots
  where topSpots = head $ groupBy sameScore scored
        scored = scoreSetSpots lex layout board dist spots
        sameScore (x,_) (y,_) = x==y
        spotMoves = setSpotMoves lex board dist rack

tileConstraints :: Lex -> Dist -> [Tile] -> [Score] -> Rack -> [[Tile]]
tileConstraints lex dist crosses set rack = zipWith workWith crosses set
  where
    ofScore x = filter ((== x) . score) rack
    score x = unsafeLookup x (distScores dist)
    workWith cross scr = sortUniq $ if cross==1 then ofScore scr
                                    else working cross $ ofScore scr
    working cross tiles = filter (\x -> isGoodWith lex cross [x]) tiles

setSpotMoves :: Lex -> Board -> Dist -> Rack -> Scored (Pos,TileSet,[Score])
                    -> [Scored Move]
setSpotMoves lex board dist rack (scr,((sq,dir),tileSet,set)) =
  map toScoredMove perms
  where perms = constrainedPerms tileSet (constraints' tileSet)
        constraints' tileSet = tileConstraints lex dist crosses set (toList tileSet)
        crosses = crossProdsAt board dir newSqs
        newSqs = fromJust $ squaresAt board (sq,dir) (length set)
        toScoredMove perm = (scr,Move perm (sq,dir))

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
        (rows,cols) = both range $ bounds' $ boardPrimes board
        lens = [7,6..2]

sqsThatTouch :: Board -> Int -> [(Pos,Int,Prod)]
sqsThatTouch board rackSize =
  map (addThrough board) $ filter (touch board) sqs
  where sqs = [(((r,c),d),len) | len <- lens, r <- rows, c <- cols, d <- dirs]
        bounds' x = ((r,r'),(c,c')) where ((r,c),(r',c')) = bounds x
        (rows,cols) = both range $ bounds' $ boardPrimes board
        lens = [7,6..1]
        dirs = [Down, Acrs]
        
openerSetSpots :: Layout -> Board -> Dist -> Rack
                         -> [(Pos,Int,[(TileSet,ScoreSet)],Prod)]
openerSetSpots layout board dist rack = map kSets' sqs
  where maxLen = length rack
        sqs = sqsThatHitCenter layout board maxLen
        kSets' (pos,len,thru) = (pos,len,kSets len dist rack,thru)

nonOpenerSetSpots :: Board -> Dist -> Rack
                           -> [(Pos,Int,[(TileSet,ScoreSet)],Prod)]
nonOpenerSetSpots board dist rack = map kSets' sqs
  where maxLen = length rack
        sqs = sqsThatTouch board maxLen
        kSets' (pos,len,thru) = (pos,len,kSets len dist rack,thru)

couldFit :: Lex -> Dist -> [Prod] -> Rack -> ScoreSet -> Bool
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

constrainedPerms :: (Eq a) => Multiset a -> [[a]] -> [[a]]
constrainedPerms set []     = []
constrainedPerms set (c:cs) = concatMap perms c
  where perms x = if msHas set x then perms' x else []
        perms' x = if null cs then [[x]]
                   else map ((:) x) $ constrainedPerms (msMinus set x) cs

sortUniq :: (Ord a) => [a] -> [a]
sortUniq x = map head $ List.group $ List.sort x

constraints :: Lex -> Dist -> [Prod] -> [Tile] -> [[Score]]
constraints lex dist crosses rack = map workWith crosses
  where
    scores = map (`unsafeLookup` (distScores dist)) rack
    workWith cross = sortUniq $ if cross==1 then scores else workingScrs cross
    workingScrs cross = map (`unsafeLookup` (distScores dist)) $ working cross
    working cross = filter (\x -> isGoodWith lex cross [x]) rack

showScoredSetSpot :: Lex -> Scored (Pos,TileSet,[Score]) -> String
showScoredSetSpot lex (sc,(pos,set,spot)) =
  "(" ++ show sc ++ "," ++ pos' ++ "," ++ set' ++ "," ++ show spot ++ ")"
  where pos' = showPos pos
        set' = "{" ++ (showRack lex $ toList set) ++ "}"

spotInfo :: Lex -> Layout -> Board -> Dist
                -> (Pos,Int,[(TileSet,ScoreSet)],Integer)
                -> [Scored (Pos,TileSet,[Score])]
spotInfo lex layout board dist ((sq,dir),len,xs,thru) =
  concatMap scoredSpots' $ filter good xs
  where good (tileSet,_) = isGoodWith lex thru $ toList tileSet
        scoredSpots' (tileSet,set) = if couldFit' tileSet set then
                                       map scoredSpot $ perms tileSet set
                                     else []
          where scoredSpot x = (scoreSpot baseScr wMul muls x,((sq,dir),tileSet,x))
        perms tileSet set = constrainedPerms set (constraints' tileSet)
        constraints' tileSet = constraints lex dist crosses (toList tileSet)
        couldFit' tileSet = couldFit lex dist crosses (toList tileSet)
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
                     -> [Scored (Pos,TileSet,[Score])]
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
covered board sq = ((boardPrimes board) ! sq) > 1

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
scoreMove layout board dist (Move word (sq,dir)) = score
  where score = bonus+hookScore+wMul*(newScore+oldScore)
        wMul = product $ map ((layoutXWS layout) !) newSqs
        newScore = sum $ zipWith (*) muls newScores
        muls = mulsAt layout board dir newSqs
        newScores = map (`unsafeLookup` scores) word
        newSqs = fromJust $ squaresAt board (sq,dir) $ length word
        oldScore = sum $ map (`unsafeLookup` scores) oldTiles
        oldTiles = throughTilesAt board (sq,dir) $ length word
        bonus = if length word >= 7 then 50 else 0
        hookScore = scoreHooks layout board dist dir newSqs
        scores = distScores dist

scoreSpot :: Int -> Int -> [Int] -> [Int] -> Int
scoreSpot baseScore wMul muls spot = score
  where score = baseScore+wMul*newScore
        newScore = sum $ zipWith (*) muls spot
        
main :: IO ()
main = do
  putStrLn "Loading..."
  twl <- lexFromFile twlFile
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
  putStr $ unlines $ labelBoard standard twl board'
  let !rack' = fromJust $ readRack twl "AEOULJS"
  putStrLn $ showRack twl rack' 
  start' <- getCPUTime
  --let !scored = scoredSetSpots twl standard board' english rack'
  let !moves' = topMoves twl standard board' english rack'
  end' <- getCPUTime
  let diff' = fromIntegral (end'-start') / (10^12)
  --printf "found %i spots in %0.5fs\n"
  --  (length scored::Int) (diff'::Double)
  --mapM_ putStrLn $ map (showScoredSetSpot twl) scored
  let !top' = head moves'      
  let !topString' = showMove twl board' top'
  let !score' = scoreMove standard board' english top'
  printf "found %i top moves (such as %s for %i) in %0.5fs\n"
    (length moves'::Int) (topString'::String) (score'::Int) (diff'::Double)
