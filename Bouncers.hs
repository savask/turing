{- 
  This is an implementation of a bouncers decider. It should roughly correspond to Tony's bouncers,
  Skelet's linearly increasing sequence and Shawn's diff rules.

  We assume that the Turing machine head lives in between the cells, and can point to the left or to the right.
  If there are strings a, b, b' and a state S such that starting from tape a S> b we can reach b' a S>
  in several steps, we say that we have a "shift rule". A shift rule allows the machine to jump over a power of b:
      a S> b^n --> b'^n a S>
  Similarly one defines a shift rule with the head pointing to the left.

  Let u1, ..., uk, w1, ..., wk be (possibly empty) strings, and let n1, ..., nk be abstract variables. Say we are given a tape:
      <S u1 w1^n1 u2 w2^n2 ... uk wk^nk    (*)
  and after a finite number of steps and shift rules we end at a tape
      <S u1 w1^(n1+c1) u2 w2^(n2+c2) ... uk wk^(nk+ck)
  where c1, ..., ck are some positive constants. Then the language specified by the regular expression
      <S u1 (w1) u2 (w2) ... uk (wk)
  is "eventually closed" (here (w) means that the string w is repeated one or more times) with respect to our Turing machine,
  i.e. given a tape from that language, the machine reaches a tape from the language in a finite amount of steps and shift rules
  (and does not halt in the process). We call a Turing machine a bouncer if it satisfies conditions above (and similar conditions
  for the case when the tape is ... S>), and one can reach a tape of the form <S u1 w1^n1 ... uk wk^nk (or ... S>) from the starting tape.
  Clearly bouncers do not halt by the usual CTL argument.

  The algorithm for deciding bouncers consists of two steps. First, we try to find a candidate tape formula of the form (*).
  To do that, we run the machine for stepLimit amount of steps, and record tapes where the head is at the border and looks outside
  Then we use Tony's heuristic and find 4 tapes such that their lengths are in an arithmetic progression and step counts are in a
  quadratic progression. We take 3 such tapes s0, s1, s2 and try to express them as
      s(n) = <S u1 w1^n u2 w2^n ... uk wk^n.
  One can prove that one abstract variable is enough, so we do not lose anything by using only n.
  We find s(n) with a dynamic programming algo (see function toPowers), and we output
      <S u1 (w1) u2 (w2) ... uk (wk)    (**)
  as our candidate tape formula. Similarly, we look for tapes ending in S>.

  For example, if we have
      s0 = 101 S>
      s1 = 110011 S>
      s2 = 110100111 S>
  then
      s(n) = 1 10^n 0 1^n 1 S>
  and the tape formula will be
      1 (10) 0 (1) 1 S>.

  On the second step we try to prove that our tape formula is "increasing", that is, after a finite number of steps and shift rules
  we end up in a less general tape formula. To do that, we run the machine for stepLimit macro steps starting from (**),
  where one macro step is just a usual Turing machine step if the head points at a constant segment (i.e. u1, ..., uk)
  and a shift rule if the head points at a power (i.e. (w1), ..., (wk)). After each macro step we align powers away from the head
  (i.e. to the left on the left half of the tape, and to the right on the right half).
  If we have "... (w) x ..." on the tape and wx = xw' for some string w', then we can move (w) to the right and obtain "... x (w') ...".
  "Aligning" means that we move powers in that manner as far as possible.

  (As a small digression for people with rule-based deciders: the reason for aligning is that instead of using real formulae
  like "C> 110^(n+3)" this decider uses "C> 110110110(110)". Sometimes we need to decrease the formula, like
      C> 110^(n+3) --> C> 110 110^(n+2) --> 101 D> 110^(n+2) --> 101 111^(n+2) D>
  so by aligning all powers away from the machine head we side-step this problem, as we defer shift rule application as much as we can.)
  
  For example, we could have the following steps:
      1 (10) 0 A> 1 (1) --> 1 (10) 00 B> (1)    [a usual step]
      1 (10) 00 B> (1) --> 1 (10) 0 (0) 0 B>    [used a shift rule 0 B> 1 --> 0 0 B>]
  The resulting tape 1 (10) 0 (0) 0 B> will be aligned to 1 (10) (0) 00 B>.

  After each macro step we check if the resulting tape is a special case of the original tape.
  For example, suppose we started with
      1 (10) 0 (1) 1 S>
  and after some steps and shift rules we end in
      1 (10) 100 (1) 11 S>.
  The second tape formula is a special case of the first, since (10) 10 lies in (10) and (1) 1 lies in (1).
  Since all powers are aligned, we can check if the second string is a special case of the first with a greedy algorithm (see function isIncreasing).

  If we found an increasing pair of tape formulae then the decider succeeds and outputs the tape formula.
  If we cannot find an increasing tape in a given amount of time, or if the machine halts or it is not possible to perform a macro step
  (say, the machine head faces a power but there is no relevant shift rule to jump over it), then we output failure.

  The decider tries the above procedure for all triplets s0, s1, s2 satisfying Tony's heuristic, with some minor optimizations
  (for example, to avoid checking tapes which lie in the same arithmetic progression). Essentially the only parameter is stepLimit,
  one can also comment out "take 10" in function increasingSequence to check all tape formulae instead of the first 10 only
  (that slows down the decider considerably, though).

  stepLimit equal to 1000000 and "take 10" commented out are enough to reproduce Justin's bouncers run on the current undecided index.
-}

import qualified Data.Map as M
import qualified Data.Array as A
import Data.Maybe (catMaybes, mapMaybe)
import Data.List (nubBy, inits, isPrefixOf)
import Control.Monad (guard)

import Machine

type Segment = [Cell]

-- A tape expression consists of constant segments and powers, i.e. one-or-more repetitions of some string.
data TapeExpr = Const Segment | Power Segment deriving (Eq, Ord)

instance Show TapeExpr where
    show (Const s) = showBools s
    show (Power s) = "(" ++ showBools s ++ ")"

turnAround :: TapeExpr -> TapeExpr
turnAround (Const s) = Const (reverse s)
turnAround (Power s) = Power (reverse s)

-- Formula tape, analogue of Tape but with tape expressions.
data FTape = FTape {
            leftF :: [TapeExpr],
            atF :: Head,
            rightF :: [TapeExpr]
            } deriving (Eq, Ord)

instance Show FTape where
    show (FTape l h r) = (unwords . map (show . turnAround) $ reverse l) ++ " " ++
                         (either (\s -> "<" ++ [('-':['A'..'Z']) !! s]) (\s -> [('-':['A'..'Z']) !! s] ++ ">") h) ++ " " ++
                         unwords (map show r)

-- Concatenate constant segments together.
glueConsts :: [TapeExpr] -> [TapeExpr]
glueConsts [] = []
glueConsts ((Const []):xs) = glueConsts xs
glueConsts [x] = [x]
glueConsts ((Const x1):(Const x2):xs) = glueConsts ((Const $ x1++x2):xs)
glueConsts (x:xs) = x : glueConsts xs

-- Align all powers to the right, i.e. (10|n)1 -> 1(01|n).
alignRight :: [TapeExpr] -> [TapeExpr]
alignRight [] = []
alignRight [x] = [x]
alignRight ((Power x):(Const y):xs) =
    let -- We can replace "t (a as) a bs" by "t a (as a) bs". Function roll does that while it's possible
        roll t a [] = [Const (reverse t), Power a]
        roll t p@(a:as) c@(b:bs) | a == b = roll (b:t) (as ++ [a]) bs
                                 | otherwise = [Const (reverse t), Power p, Const c]
    in (roll [] x y) ++ alignRight xs
alignRight ((Const y):xs) = (Const y) : alignRight xs
alignRight (x:xs) = x : alignRight xs

-- Pack the tape, i.e. glue constant blocks and align all powers to the right.
pack :: FTape -> FTape
pack (FTape l h r) = FTape (p l) h (p r)
    where p = glueConsts . alignRight . glueConsts

-- Return the first Just value in a list.
firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust ((Just a):ls) = Just a
firstJust (Nothing:ls) = firstJust ls

-- For tape "l S> r" try all suffixes l' of l to find a shift rule (same for <S).
extractShiftRule :: Program -> Tape -> Maybe Tape
extractShiftRule prg (Tape l (Right s) r) = firstJust [isShiftRule prg (Tape li (Right s) r) | li <- inits l]
extractShiftRule prg (Tape l (Left s) r) = firstJust [isShiftRule prg (Tape l (Left s) ri) | ri <- inits r]

-- Split a tape expression into a constant segment and the rest.
takeConstPrefix :: [TapeExpr] -> (Segment, [TapeExpr])
takeConstPrefix ((Const s):t) = (s, t)
takeConstPrefix t = ([], t)

maybeToResult :: Maybe a -> Result a
maybeToResult Nothing = Halt
maybeToResult (Just a) = Result a

-- Do one macro move of the machine, i.e. a usual move or run through a power (if it corresponds to a shift-rule).
doMacroMove :: Program -> FTape -> Result FTape
doMacroMove prg (FTape l (Right s) []) = doMacroMove prg (FTape l (Right s) [Const [zeroC]]) -- S> .
doMacroMove prg (FTape [] (Left s) r) = doMacroMove prg (FTape [Const [zeroC]] (Left s) r) -- . <S
doMacroMove prg (FTape l (Right s) ((Const r):rs)) = do -- l S> r rs
    Tape l' h' r' <- maybeToResult $ doMove prg (Tape [] (Right s) r)
    return $ FTape ((Const l'):l) h' ((Const r'):rs)
doMacroMove prg (FTape l (Right s) ((Power r):rs)) = -- l S> r^e rs
   let (l1, l2) = takeConstPrefix l in
   case extractShiftRule prg (Tape l1 (Right s) r) of
        Nothing -> Halt
        Just (Tape l' h' _) -> let lr = length r
                                   la = length l' - lr
                                   (l1a, l1') = splitAt la l1 -- l S> r^e rs == l2 l1 S> r^e rs == l2 l1' a S> r^e rs
                                   (a, r') = splitAt la l' -- Shift rule:  a S> r -> r' a S>
                               in return $ FTape ((Const a):(Power r'):(Const l1'):l2) h' rs -- l2 l1' r'^e a S> rs
doMacroMove prg (FTape ((Const l):ls) (Left s) r) = do -- ls l <S r
    Tape l' h' r' <- maybeToResult $ doMove prg (Tape l (Left s) [])
    return $ FTape ((Const l'):ls) h' ((Const r'):r)
doMacroMove prg (FTape ((Power l):ls) (Left s) r) = -- ls l^e <S r
    let (r1, r2) = takeConstPrefix r in
    case extractShiftRule prg (Tape l (Left s) r1) of
         Nothing -> Halt
         Just (Tape _ h' r') -> let ll = length l
                                    la = length r' - ll
                                    (l1a, r1') = splitAt la r1 -- ls l^e <S r == ls l^e <S r1 r2 == ls l^e <S a r1' r2
                                    (a, l') = splitAt la r' -- Shift rule: l <S a -> <S a l'
                                in return $ FTape ls h' ((Const a):(Power l'):(Const r1'):r2) -- ls <S a l'^e r1' r2
doMacroMove prg _ = Halt -- Report error if we cannot make a move.

-- Check if two tapes are increasing, i.e. the second tape is a special case of the first.
-- For example, tapes 1(0) and 10(0) are increasing, while 10(0)1 and 1(0)1 are not.
-- We assume that powers in input tapes are right-aligned.
isIncreasing :: FTape -> FTape -> Bool
isIncreasing (FTape l h r) (FTape l' h' r') = h == h' && incr l l' && incr r r'
    where incr [] [] = True
          incr ((Const w):ws) ((Const w'):ws') = w `isPrefixOf` w' && incr ws (if w == w' then ws' else (Const $ drop (length w) w'):ws')
          incr ((Power w):ws) ((Power w'):ws') = w == w' && incr ws ws'
          incr t@((Power w):ws) ((Const w'):ws') = w `isPrefixOf` w' && incr t (if w == w' then ws' else (Const $ drop (length w) w'):ws')
          incr _ _ = False

-- Simulate the machine till it visits an increasing tape.
runTillIncreasing :: Program -> FTape -> Result FTape
runTillIncreasing prg tape = oneMove tape >>= go stepLimit
    where oneMove t = fmap pack $ doMacroMove prg t
          go 0 _ = Halt
          go s t | isIncreasing tape t = return tape
                 | otherwise = oneMove t >>= go (s-1)

-- Output tape lengths, step counts and head states when the machine is in a record position.
recordStats :: [Tape] -> [(Int, Int, Head)]
recordStats = map (\(s, t) -> (length (left t) + length (right t), s, at t)) . filter (\(_, t) -> isRecord t) . zip [0..]
    where -- Check if the machine just visited a new cell, i.e. if the tape is either ... S>. or .<S ...
          isRecord :: Tape -> Bool
          isRecord (Tape [] (Left _) _) = True
          isRecord (Tape _ (Right _) []) = True
          isRecord _ = False

-- Produces a list of tuples, where the first element
-- of each tuple precedes the second.
pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = [(x, y) | y <- xs] ++ pairs xs

-- Check if the list is [a, a, ... a]
isConst :: Eq a => [a] -> Bool
isConst [] = True
isConst (x:xs) = all (x == ) xs

-- Find step counts which are in a polynomial progression such that at corresponding times
-- the machine is in a record position and tape lengths are in an arithmetic progression.
-- First argument is the polynomial degree, second is the list of tapes. Returns maximal progressions.
linPolyTest :: Int -> [Tape] -> [[Int]]
linPolyTest deg tapes = concatMap checkPair $ pairs steps
    where records = recordStats tapes
          steps = map (\(s, _, _) -> s) records
          msteps = maximum steps
          arr = M.fromList $ map (\(s, l, h) -> (s, (l, h))) records
          -- Check if numbers are in a polynomial progression
          arePoly ls = let diff xs = zipWith (-) (tail xs) xs
                       in isConst ((iterate diff ls) !! deg)
          checkPair (a1, a2)
              | snd (arr M.! a1) == snd (arr M.! a2) = -- check that machine heads at steps a1 and a2 are the same
                  case mapM (`M.lookup` arr) [k*(a2 - a1) + a1 | k <- [0..(msteps - a1) `div` (a2-a1)]] of
                       Just ts -> if length ts >= 4 && isConst (map snd ts) && arePoly (map fst ts) then [map fst ts] else []
                       _ -> []
              | otherwise = []

-- Given three strings s0, s1, s2, try to express each as s(x) = u1 w1^x u2 w2^x ..., where wi, ui are some words.
-- Such an expression is not unique (an example by J. Blanchard: 001^x 0^x 01001001^x == 0010010^x 01^x 001^x for x = 0, 1, 2),
-- and we output only one possible expression.
toPowers :: Segment -> Segment -> Segment -> Maybe [TapeExpr]
toPowers s0 s1 s2 = mem A.! (0, 0)
    where mem = A.array ((0, 0), (ls0, ls1)) [((x, y), go x y) | x <- [0..ls0], y <- [0..ls1]]
          ls0 = length s0
          ls1 = length s1
          ls2 = length s2
          -- Uses memoization with array mem. i0 and i1 are symbols dropped from s0 and s1 respectively.
          go i0 i1 | i0 == ls0 && i1 == ls1 && i2 == ls2 = return [] -- If all strings are empty
                   | i1 < i0 = Nothing
                   | otherwise = firstJust (skip : map pow (reverse . zip [1..] . take ((ls2 - i2) `div` 2) . tail $ inits v1))
              where v0 = drop i0 s0
                    v1 = drop i1 s1
                    v2 = drop i2 s2
                    i2 = i0 + (i1 - i0)*2 -- number of symbols dropped from s2
                    -- If strings start at the same symbol, try skipping it
                    skip | null v0 || null v1 || null v2 = Nothing
                         | head v0 == head v1 && head v1 == head v2 = fmap ((Const [head v0]):) $ mem A.! (i0+1, i1+1)
                         | otherwise = Nothing
                    -- If v1 = w v1' and v2 = w w v2', try reducing the problem to v0, v1', v2'.
                    -- Here k is the length of w.
                    pow (k, w) = if (w ++ w) `isPrefixOf` v2 then fmap (Power w :) $ mem A.! (i0, i1+k) else Nothing

-- Given three tapes, try obtaining a corresponding formula tape.
toPowersTape :: Tape -> Tape -> Tape -> Maybe FTape
toPowersTape t0 t1 t2 = do
    l <- toPowers (left t0) (left t1) (left t2)
    r <- toPowers (right t0) (right t1) (right t2)
    return . pack $ FTape l (at t2) r

-- This constant is used when applying Tony's heuristic and
-- when running the machine till it meets an increasing tape.
stepLimit = 100000

-- Search for 3 tapes s0, s1, s2 in an arithmetic-quadratic progression (Tony's heuristic),
-- and try obtaining a formula tape s(x) for those. s(1) is added to the output, for example,
-- for s0 = 1, s1 = 10, s2 = 100 we'll have s(x) = 1 0^x and the output will contain "1 (0)".
setupIncreasingTape :: Program -> [FTape]
setupIncreasingTape prg = do
    let tapes = runFor prg (stepLimit+1)
        incts = map reverse . nubBy (\a b -> take 3 a == take 3 b) . map reverse . -- Remove sequences of steps which are a suffix of another sequence
                filter (\i -> length i >= 4) $ linPolyTest 2 tapes -- Linear-quadratic heuristic
        history = A.listArray (0, stepLimit) tapes
        goodThread ts = let [s0, s1, s2] = take 3 ts
                            t0 = history A.! s0
                            t1 = history A.! s1
                            t2 = history A.! s2
                        in toPowersTape t0 t1 t2
    guard $ length tapes == (stepLimit+1)
    guard . not $ null incts
    catMaybes $ map goodThread incts

-- Returns the first result in a list, if it exists.
firstResult :: [Result a] -> Maybe a
firstResult [] = Nothing
firstResult ((Result r):rs) = return r
firstResult (_:rs) = firstResult rs

-- Try to decide the machine as a bouncer.
-- If the decider succeeded and there two increasing tapes s(1) and s(2), then it returns s(1).
-- We consider only first 10 potential tape formulae, that is not enough sometimes, see exampleComplex.
increasingSequence :: Program -> Maybe FTape
increasingSequence prg = firstResult . map (runTillIncreasing prg) . take 10 $ setupIncreasingTape prg

-- A version of increasingSequence which outputs a detailed certificate.
-- First line is "STEP N" , where N is the number of steps from the empty tape to the initial formula tape.
-- The following lines have the form:
-- "tp <tab> STEP N", meaning one needs to make N usual steps from the tape tp,
-- "tp <tab> RULE r", meaning one needs to apply a shift rule r, or
-- "tp <tab> END", meaning that we reached a tape, which is a special case of the initial formula tape.
certificate :: Program -> Maybe String
certificate prg = do
    tape <- increasingSequence prg
    let -- Tape history
        history = zip [0..] $ runFor prg stepLimit
        clean = concatMap (\c -> case c of Const x -> x; Power x -> x)
        -- Initial tape (converted from formula tape)
        tape' = Tape (clean $ leftF tape) (atF tape) (clean $ rightF tape)
        firstStep = fst . head $ filter (\(_, t) -> t == tape') history
        -- A version of isShiftRule which returns the full rule
        isShiftRule' start = isShiftRule prg start >>= \end -> return (start, end)
        -- A version of extractShiftRule which returns the full rule
        extractShiftRule' :: Tape -> Maybe (Tape, Tape)
        extractShiftRule' (Tape l (Right s) r) = firstJust [isShiftRule' (Tape li (Right s) r) | li <- inits l]
        extractShiftRule' (Tape l (Left s) r) = firstJust [isShiftRule' (Tape l (Left s) ri) | ri <- inits r]
        -- Comment what happens on the current step
        comment t@(FTape ((Power l):_) (Left h) r) = -- (l) <S r
            case extractShiftRule' (Tape l (Left h) (fst $ takeConstPrefix r)) of
                 Nothing -> ""
                 Just (start, end) -> "RULE " ++ show start ++ " --> " ++ show end
        comment t@(FTape l (Right h) ((Power r):_)) = -- l S> (r)
            case extractShiftRule' (Tape (fst $ takeConstPrefix l) (Right h) r) of
                 Nothing -> ""
                 Just (start, end) -> "RULE " ++ show start ++ " --> " ++ show end
        comment t | isIncreasing tape t = "END"
                  | otherwise = "STEP"
        -- Do one macro move with packing
        oneMove t = fmap pack $ doMacroMove prg t
        -- Return the history of formula tapes
        go 0 _ = Halt
        go s t | isIncreasing tape t = return [t]
               | otherwise = fmap (t:) (oneMove t >>= go (s-1))
        -- The history of formula tapes
        Result fhistory = oneMove tape >>= go stepLimit
        annotated = (tape, "STEP") : map (\t -> (t, comment t)) fhistory
        -- Replace STEP .. STEP by STEP n
        clumpSteps [] = []
        clumpSteps cs = let (steps, rest) = span ((== "STEP") . snd) cs
                        in if null steps then head rest : clumpSteps (tail rest)
                                         else (fst $ head steps, "STEP " ++ (show $ length steps)) : clumpSteps rest
        -- The certificate string
        cert = unlines . map (\(t, c) -> show t ++ "\t" ++ c) $ clumpSteps annotated
    return $ "STEP " ++ show firstStep ++ "\n" ++ cert

-- A bouncer.
example :: Program
example = parse "1RB1LE_1RC0LC_1LD0RA_0LA1RA_---0LB"

-- A bouncer with "four partitions" in Tony's terminology.
exampleFour :: Program
exampleFour = parse "1RB0RD_1LC1LE_1RA1LB_---0RC_1LB0LE"

-- A moving bouncer. Adds a lot of trailing zeros.
exampleMoving :: Program
exampleMoving = parse "1RB0LC_0LA1RC_0LD0LE_1LA1RA_---1LC"

-- A bouncer which requires one to remove the "take 10" optimization.
exampleComplex :: Program
exampleComplex = parse "1RB---_0RC1RD_0LD1RC_1LE0RA_1RA0LE"

exampleHalt :: Program
exampleHalt = parse "1RB1LC_0LA0LD_1LA1RZ_1LB1RE_0RD0RB"

exampleLoop :: Program
exampleLoop = parse "1RB0RC_0LA0LA_1LD---_1RE1LB_1LB0RD"

-- Run the bouncers decider on standard input.
-- Takes a list of machines in text format (one per line), outputs the machines solved.
main = do
    file <- lines `fmap` getContents
    let rs = map (\p -> (p, increasingSequence (parse p))) file
    mapM_ (putStrLn . fst) $ filter (\(_, r) -> case r of Just _ -> True; _ -> False) rs -- Output solved
    -- mapM_ (putStrLn . fst) $ filter (\(_, r) -> r == Nothing) rs -- Output unsolved machines
    -- print . length $ filter (\(_, r) -> case r of Just _ -> True; _ -> False) rs -- Output the number of solved
    -- let rs' = map (\p -> (p, certificate (parse p))) file
    -- mapM_ (\(m, Just c) -> putStrLn $ m ++ "\n" ++ c) $ filter (\(_, r) -> r /= Nothing) rs' -- Output solved with certificates
