{- 
  This is a rough replication of mxdys' RepWL_ES decider, see https://github.com/ccz181078/Coq-BB5

  The decider has two integer parameters: block size B and repetition bound R. We simulate a (directional) Turing machine
  and partition the tape into blocks of fixed size. For example, for blocks of size B = 2:

  ... 11 01 10 10 10 B> 00 11 11 11 11 01 11 ...

  We collect the same blocks into powers:

  ... 11^1 01^1 10^3 B> 00^1 11^4 01^1 11^1 ...

  and replace powers with at least R repetitions with a regular expression of the form 'word^R+' which matches
  word^R, word^{R+1}, word^{R+2} and so on. For example, for R = 3:

  ... 11^1 01^1 10^3+ B> 00^1 11^3+ 01^1 11^1 ...

  We can run the Turing machine on such regex-tapes naturally: if the machine head faces a usual power (such as 00^1), we
  simply run the simulation as usual for one macro step. If the head faces a regex-power, say, '... S> word^k+ ...' then
  if k > 0 we replace the tape by '... S> word^1 word^{k-1}+ ...' and run the simulation as in the previous case, and
  if k = 0 then we branch into two possibilities, namely, '... S> word^1 word^0+ ...' and '... S> ...'.

  For example, consider a regex-tape

  ... 01^1 10^3+ 11^1 C> 11^3+ 01^1 ...

  We can pop one word and proceed with the usual macro step:

  ... 01^1 10^3+ 11^1 C> 11^1 11^2+ 01^1 ...

  Now consider a regex-tape

  ... 11^3+ 01^1 D> 11^0+ 01^2 ...

  We have to branch into two tapes (a) and (b):

  (a): ... 11^3+ 01^1 D> 11^1 11^0+ 01^2 ...
  (b): ... 11^3+ 01^1 D> 01^2 ...

  After each macro step we "compress" our tapes once again, i.e. collect same blocks into larger powers, like

  10^2 10^3    -->  10^5  -->  10^3+
  01^2 01^3+   -->  01^3+
  11^1+ 11^2+  -->  11^3+

  The decider saves all regex-tapes obtained during macro simulation (with branching) from the empty tape,
  and if this set eventually turns out to be closed under macro steps, we report the machine non-halting.
  In this implementation, an upper bound for the closed tape set is 10000, see 'decideRepeat'. The decider
  fails to conclude anything if it meets this bound.
-}

import System.Environment (getArgs)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List (nub)
import Data.Maybe (mapMaybe)

import Machine

-- Convert mxdys' Turing machine format used in his Coq program to the standard text format.
fromMxdys :: String -> String
fromMxdys str = map (\c -> if c == ' ' then '_' else c) . unwords . map concat . chop 2 . map (\w -> if last w == 'H' then "---" else w) .  map reverse $ words str

data Part = Power [Cell] Int   -- A constant power of a segment, e.g. (110)^10
          | AtLeast [Cell] Int -- A regular expression matching at least some number of repetitions, e.g. (110)^10+
          deriving (Eq, Ord)

instance Show Part where
    show (Power cs n) = showBools cs ++ "^" ++ show n
    show (AtLeast cs n) = showBools cs ++ "^" ++ show n ++ "+"

-- A regular expression tape.
data RTape = RTape {
             leftR :: [Part],
             atR :: Head,
             rightR :: [Part]
             } deriving (Eq, Ord)

instance Show RTape where
    show (RTape l h r) = (unwords $ map (show . rev) (reverse l)) ++
                         (either (\s -> "<" ++ [('-':['A'..'Z']) !! s]) (\s -> [('-':['A'..'Z']) !! s] ++ ">") h) ++
                         (unwords $ map show r)
        where rev (Power cs n) = Power (reverse cs) n
              rev (AtLeast cs n) = AtLeast (reverse cs) n

-- The empty rtape.
startRTape :: RTape
startRTape = RTape [] (Right 1) []

-- Glue powers of the same word together, e.g. (110)^3 (110)^4 -> (110)^7,
-- and update "at least" powers, e.g. (110)^3 (110)^4+ -> (110)^7+.
compress :: [Part] -> [Part]
compress parts@((Power cs n):(Power cs' n'):ps) = if cs == cs' then compress $ (Power cs (n+n')):ps else parts
compress parts@((Power cs n):(AtLeast cs' n'):ps) = if cs == cs' then compress $ (AtLeast cs (n+n')):ps else parts
compress parts@((AtLeast cs n):(Power cs' n'):ps) = if cs == cs' then compress $ (AtLeast cs (n+n')):ps else parts
compress parts@((AtLeast cs n):(AtLeast cs' n'):ps) = if cs == cs' then compress $ (AtLeast cs (n+n')):ps else parts
compress parts = parts

-- Replace powers by "at least" versions if there are at least 'bound' repetitions.
generalize :: Int -> [Part] -> [Part]
generalize bound parts = compress . map gen $ compress parts
    where gen (Power cs n) = if n >= bound then AtLeast cs bound else Power cs n
          gen (AtLeast cs n) = AtLeast cs (min n bound)

-- Block size.
type Size = Int

-- Do one macro step. Takes a Turing machine, block size, repetitions bound and an rtape.
-- Returns possible successors after simulating for one macro step.
macroStep :: Program -> Size -> Int -> RTape -> Result [RTape]
macroStep prg size bound (RTape l (Right s) []) = macroStep prg size bound (RTape l (Right s) [Power (replicate size zeroC) 1]) -- l S> .
macroStep prg size bound (RTape [] (Left s) r) = macroStep prg size bound (RTape [Power (replicate size zeroC) 1] (Left s) r) -- . <S r
macroStep prg size bound (RTape l (Right s) ((Power cs n):rs)) = do -- l S> cs^n rs
    Tape l' h' r' <- runTillBorder prg (Tape [] (Right s) cs)
    let rs' = if n == 1 then rs else generalize bound $ (Power cs (n-1)):rs
        ll = if null l' then l else generalize bound $ (Power l' 1) : l
        rr = if null r' then rs' else generalize bound $ (Power r' 1) : rs'
    return $ [RTape ll h' rr]
macroStep prg size bound (RTape ((Power cs n):ls) (Left s) r) = do -- ls cs^n <S r
    Tape l' h' r' <- runTillBorder prg (Tape cs (Left s) [])
    let ls' = if n == 1 then ls else generalize bound $ (Power cs (n-1)):ls
        rr = if null r' then r else generalize bound $ (Power r' 1) : r
        ll = if null l' then ls' else generalize bound $ (Power l' 1) : ls'
    return $ [RTape ll h' rr]
macroStep prg size bound (RTape l (Right s) ((AtLeast cs 0):rs)) = do -- l S> cs^0+ rs
    some <- macroStep prg size bound (RTape l (Right s) ((Power cs 1):(AtLeast cs 0):rs)) -- l S> cs^1 cs^0+ rs
    none <- macroStep prg size bound (RTape l (Right s) rs) -- l S> rs
    return $ some ++ none
macroStep prg size bound (RTape l (Right s) ((AtLeast cs n):rs)) = do -- l S> cs^n+ rs
    macroStep prg size bound (RTape l (Right s) ((Power cs 1):(AtLeast cs (n-1)):rs)) -- l S> cs^1 cs^(n-1)+ rs
macroStep prg size bound (RTape ((AtLeast cs 0):ls) (Left s) r) = do -- ls cs^0+ <S r
    some <- macroStep prg size bound (RTape ((Power cs 1):(AtLeast cs 0):ls) (Left s) r) -- ls cs^0+ cs^1 <S r
    none <- macroStep prg size bound (RTape ls (Left s) r) -- ls <S r
    return $ some ++ none
macroStep prg size bound (RTape ((AtLeast cs n):ls) (Left s) r) = do -- ls cs^n+ <S r
    macroStep prg size bound (RTape ((Power cs 1):(AtLeast cs (n-1)):ls) (Left s) r) -- ls cs^(n-1)+ cs^1 <S r

-- Solved with parameters 6 and 2.
exampleBouncer :: Program
exampleBouncer = parse "1RB1LC_1LA1RD_1LD1LA_1RA1RE_---1RB"

-- Solved with parameters 4 and 2.
exampleModular :: Program
exampleModular = parse "1RB0LA_0LB1RC_0RD---_1RE1RA_1LF0RB_0LA0LE"

-- Try to decide a machine using mxdys' method. Takes a machine, block size and repetition bound.
-- Returns the set of rtapes closed under succession, if such a set exists.
decideRepeat :: Program -> Size -> Int -> Maybe [RTape]
decideRepeat prg size bound = fmap S.toList $ grow S.empty [startRTape]
    where grow :: S.Set RTape -> [RTape] -> Maybe (S.Set RTape)
          grow set new | S.size set > 10000 = Nothing
                       | otherwise =  let reallyNew = filter (`S.notMember` set) new
                                      in if null reallyNew
                                         then return set
                                         else case mapM (macroStep prg size bound) reallyNew of
                                                  Result new' -> grow (foldr S.insert set reallyNew) (concat new')
                                                  _ -> Nothing

-- Run the decider on machines from standard input. Takes block size and repetition bound as command line arguments.
-- For example:
-- > cat holdouts.txt | ./main 4 3
main = do
    [size, bound] <- map read `fmap` getArgs
    file <- lines `fmap` getContents
    let rs = map (\p -> (p, decideRepeat (parse p) size bound)) file
    mapM_ (putStrLn . fst) $ filter (\(_, r) -> case r of Just _ -> True; _ -> False) rs -- Output solved
