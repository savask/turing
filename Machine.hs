module Machine where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (nub, isPrefixOf)
import Data.Maybe (mapMaybe)

-- States are represented by integers starting from 1.
type State = Int

-- We assume that the Turing machine head lives in between the cells of the tape,
-- so at each stage the head has a fixed state and can point either to the left or right.
type Head = Either State State

-- Get current state.
state :: Head -> State
state = either id id

-- A cell either contains an integer or it wasn't visited yet.
data Cell = Cell !Int | Empty deriving (Eq, Ord, Show)

zeroC :: Cell
zeroC = Cell 0

-- The tape is a zipper, i.e. we store the left part of the tape, the head and the right part of the tape.
-- For example, configuration 110 A> 001 is represented by Tape [Cell 0, Cell 1, Cell 1] (Right 1) [Cell 0, Cell 0, Cell 1].
data Tape = Tape {
            left :: [Cell],
            at :: Head,
            right :: [Cell]
            } deriving (Eq, Ord)

-- showBools [Cell 1, Cell 0, Empty] == "10."
showBools :: [Cell] -> String
showBools = concatMap (\b -> case b of Cell n -> show n; Empty -> ".")

-- We use 0, 1, ... for cell symbols, A to Z for machine states,
-- a dash - for the invalid state and <, > to signify the direction the head is pointing to.
instance Show Tape where
    show (Tape l a r) = showBools (reverse l) ++
                        (either (\s -> "<" ++ [('-':['A'..'Z']) !! s]) (\s -> [('-':['A'..'Z']) !! s] ++ ">") a) ++
                        showBools r

-- Tell the symbol the head is looking at.
peek :: Tape -> Cell
peek (Tape l a r) = let t = case a of Left _ -> l; Right _ -> r
                        norm s = if s == Empty then zeroC else s
                    in if null t then zeroC else norm $ head t

-- The Turing machine program is a mapping from (current symbol, state) to (new symbol, new state + direction).
type Program = M.Map (Cell, State) (Cell, Head)

-- Remove the top symbol from a list, and do nothing if it's empty.
pop :: [a] -> [a]
pop ls | null ls = []
       | otherwise = tail ls

-- Do one move of the Turing machine. Returns Nothing if the machine halts.
doMove :: Program -> Tape -> Maybe Tape
doMove prg t@(Tape l a r) = do
    (c, a') <-  M.lookup (peek t, state a) prg
    case (a, a') of
        (Left _, Left _) -> return $ Tape (pop l) a' (c:r)
        (Left _, Right _) -> return $ Tape (c:(pop l)) a' r
        (Right _, Right _) -> return $ Tape (c:l) a' (pop r)
        (Right _, Left _) -> return $ Tape l a' (c:(pop r))

-- Replace Either contents by ().
direction :: Either a b -> Either () ()
direction = either (const $ Left ()) (const $ Right ())

-- The simulation may halt, loop indefinitely or return some result.
data Result a = Halt | Loop | Result a deriving (Show)

instance Functor Result where
    fmap f (Result a) = Result (f a)
    fmap _ Halt = Halt
    fmap _ Loop = Loop

instance Applicative Result where
    pure a = Result a
    (Result f) <*> (Result a) = Result (f a)
    (Result f) <*> Halt = Halt
    (Result f) <*> Loop = Loop
    Halt <*> _ = Halt
    Loop <*> _ = Loop

instance Monad Result where
    (Result a) >>= f = f a
    Halt >>= _ = Halt
    Loop >>= _ = Loop

-- Run the machine for a given amount of steps.
-- Returns the intermediate tapes.
runFor :: Program -> Int -> [Tape]
runFor prg imax = go 1 (Tape [] (Right 1) [])
    where go i t | i > imax = []
                 | otherwise = case doMove prg t of
                                   Nothing -> []
                                   Just t' -> t : go (i+1) t'

-- Given a program and a tape, run the Turing machine until
-- it exits from one of the two sides of the tape.
-- If the machine halts or loops in the process, we report that.
runTillBorder :: Program -> Tape -> Result Tape
runTillBorder prg tape = go 0 tape
    where len = toInteger (length (left tape) + length (right tape))
          symbolsNum = toInteger . length . nub . (zeroC:) . map fst $ M.keys prg
          statesNum = toInteger . length . nub . map snd $ M.keys prg
          stepsCap = 1 + (2*statesNum)*(toInteger len+1)*symbolsNum^len -- Upper bound on the number of iterations
          atBorder (Tape [] (Left _) _) = True
          atBorder (Tape _ (Right _) []) = True
          atBorder _ = False
          go step t@(Tape l a r) | null l && direction a == Left () = return t
                                 | null r && direction a == Right () = return t
                                 | step > stepsCap = Loop
                                 | otherwise = maybe Halt (go (step+1)) (doMove prg t)

-- A shift rule is a rule of the form "a S> b -> b' a S>".
-- Given a program and a rule (represented as a tape) we check if it is a shift rule and return the resulting tape, if it is.
isShiftRule :: Program -> Tape -> Maybe Tape
isShiftRule prg tape
    | direction (at tape) == Right () = -- S> ???
        case runTillBorder prg tape of
             Halt -> Nothing
             Loop -> Nothing
             Result t -> if at tape == at t && ((left tape) `isPrefixOf` (left t)) then return t else Nothing
    | direction (at tape) == Left () = -- ??? <S
        case runTillBorder prg tape of
             Halt -> Nothing
             Loop -> Nothing
             Result t -> if at tape == at t && ((right tape) `isPrefixOf` (right t)) then return t else Nothing
    | otherwise = Nothing

-- Parse one transition of the machine description.
parseOne :: String -> Maybe (Cell, Head)
parseOne "1RZ" = Nothing
parseOne "---" = Nothing
parseOne (c:d:s:[]) | c `elem` "0123456789" && d `elem` "LR" && s `elem` ['A'..'Z'] =
    let st = fromEnum s - fromEnum 'A' + 1
    in return (Cell (read [c]), if d == 'L' then Left st else Right st)
                    | otherwise = Nothing
parseOne _ = Nothing

-- Chop the list into parts of length n.
chop :: Int -> [a] -> [[a]]
chop _ [] = []
chop n ls = let (h, t) = splitAt n ls
            in h : chop n t

-- Parse the compact machine description.
parse :: String -> Program
parse str = M.fromList . mapMaybe toCmd $ zip cells [(s, c) | s <- [1..states], c <- symbols]
    where lns = words $ map (\c -> if c == '_' then ' ' else c) str
          states = length lns
          symbols = take ((length $ head lns) `div` 3) [Cell c | c <- [0..]]
          cells = concatMap (chop 3) lns
          toCmd (str, (s, c)) = parseOne str >>= \a -> return ((c, s), a)

-- Add m-1 sets of additional symbols which behave the same as old symbols,
-- but on each write the machine switches to a new set.
duplicateSymbols :: Int -> Program -> Program
duplicateSymbols m prg = M.fromList . concatMap dup $ M.toList prg
    where transitions = M.toList prg
          symbols = length . nub $ map (fst . fst) transitions
          dup ((Cell c, s), (Cell c', h)) = [((Cell $ c+symbols*i, s), (Cell $ c'+symbols*((i+1) `mod` m), h)) | i <- [0..m-1]]
          dup t = [t]

-- Add new additional symbol sets recording which state wrote that symbol.
addStateLog :: Program -> Program
addStateLog prg = M.fromList . concatMap dup $ M.toList prg
    where transitions = M.toList prg
          symbols = length . nub $ map (fst . fst) transitions
          states = length . nub $ map (snd . fst) transitions -- This may fail if there's a state with all transitions undefined
          dup ((Cell c, s), (Cell c', h)) = [((Cell $ c+symbols*i, s), (Cell $ c'+symbols*(s-1), h)) | i <- [0..states-1]]
          dup t = [t]

-- Add new additional symbol sets recording the last symbol written (before it was rewritten).
addSymbolLog :: Program -> Program
addSymbolLog prg = M.fromList . concatMap dup $ M.toList prg
    where transitions = M.toList prg
          symbols = length . nub $ map (fst . fst) transitions
          dup ((Cell c, s), (Cell c', h)) = [((Cell $ c+symbols*i, s), (Cell $ c'+symbols*c, h)) | i <- [0..symbols-1]]
          dup t = [t]

-- A 3x3 bouncer-counter by Justin, which defies CPS
exampleBC :: Program
exampleBC = parse "1RB0LC---_1RC0LC0RB_2LA1LC0RA"

exampleLoop1 :: Program
exampleLoop1 = parse "1RB0RC_0LA0LA_1LD---_1RE1LB_1LB0RD"

exampleHalt1 :: Program
exampleHalt1 = parse "1RB1LC_0LA0LD_1LA1RZ_1LB1RE_0RD0RB"

exampleHalt2 :: Program
exampleHalt2 = parse "1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA"
