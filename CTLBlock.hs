{-
  This is a version of Skelet's grammar mode 3 decider; it is more general in some aspects and less general in others.

  We use the directional Turing machine format. The decider takes in two parameters: the block size S, and the repetition bound B.
  The decider works by building a closed set of regular expressions ("closed tape language"), where expressions consist either of
  constant blocks of length S or Kleene stars. A Kleene star matching any combination of the words w1, ..., wk will be abbreviated
  as {w1,...,wk}. For example, the following regular expression tape
      01 {11,00} 10 A> {00} 11
  matches any of the following tapes
      01 10 A> 11,  01 11 11 00 10 A> 00 11,  01 00 10 A> 11,  etc.
  The main idea of the decider is that if a block appears often on the tape (at least B times), we put it inside a Kleene star,
  hence "generalizing" the regex tape. More precisely, we do the following.

  Consider some tape and split it into blocks of equal size S. For example for S = 2 the tape
      01110011001000 A> 1001100110
  will be split into
      01 11 00 11 00 10 00 A> 10 01 10 01 10.
  We spare the blocks adjacent to the machine head from our consideration, and focus only on the blocks inside the square brackets:
      [01 11 00 11 00 10] 00 A> 10 [01 10 01 10].
  Count how many times each block occurs inside the square brackets, separately for each tape side. In our example, on the left
  the block 01 occurs once, 11 occurs twice, 00 twice, 10 occurs once. On the right side, the blocks 01 and 10 occur twice each.

  We mark blocks which occur less than B times as "stable". For example, for B = 2 the following blocks (marked with ^) are stable:
      [01 11 00 11 00 10] 00 A> 10 [01 10 01 10].
       ^              ^             
  Now in order to generalize our regex tape, we leave stable blocks as is, and put blocks between them into Kleene stars.
  For our example (here we removed the square brackets):
      01 {11, 00} 10 00 A> 10 {01, 10}.
  Note how 11 00 11 00 matches a Kleene star {11, 00}, and 01 10 01 10 matches {01, 10}.

  If a block appears inside a Kleene star, it cannot be stable. For example the following regex tape
     11 {00} 11 {10, 00} 00 B> 11
  will be generalized to
     {11, 00, 10} 00 B> 11
  since none of the blocks on the left hand side are stable. Of course, the 00 adjacent to B> is spared.

  We run our macro simulator on regex tapes, and save them into a set - once the set is closed, we report success.
  If the machine halts in the process or the set becomes too large, we report failure. Regex tapes leading to looping machines can be ignored.

  Note that if the machine head points at a constant block, one macro step will give us one regex tape as a result. If the machine points at
  a Kleene star, we branch into several possibilities. For example the regex tape
      11 C> {10, 00} 01
  will branch into regex tapes
      11 C> 01,  11 C> 10 {10, 00} 01,  11 C> 00 {10, 00} 01.

  Skelet's decider corresponds to B = 2, essentially he cares only about blocks which appear once on the tape, so it is less general in this regard.
  On the other hand, his decider can parse the tape into blocks of variable size (Huffman codes), so my implementation is less general than his in that aspect.
-}

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (sortBy, sort, nub, intersperse)
import Data.Function (on)
import System.Environment (getArgs)

import Debug.Trace (traceShow, traceShowId)

import Machine

-- A segment is simply a piece of the tape.
type Segment = [Cell]

data Part = Const Segment -- A constant part.
          | KStar [Segment] -- Kleene's star
          deriving (Eq, Ord)

instance Show Part where
    show (Const w) = showBools w
    show (KStar ws) = "{" ++ (concat $ intersperse "," (map showBools ws)) ++ "}"

-- A regex is a list of constant segments and Kleene's stars.
type Regex = [Part]

-- A tape where left and right parts are regular expressions of our form.
data BlockTape = BlockTape {
            leftB :: Regex,
            atB :: Head,
            rightB :: Regex
            } deriving (Eq, Ord)

instance Show BlockTape where
    show (BlockTape l h r) = (unwords $ map show (map rev $ reverse l)) ++ 
                             (either (\s -> "<" ++ [('-':['A'..'Z']) !! s]) (\s -> [('-':['A'..'Z']) !! s] ++ ">") h) ++
                             (unwords $ map show r)
        where rev (Const w) = Const (reverse w)
              rev (KStar ws) = KStar (map reverse ws)

-- Turn a regex into a large Kleene star.
-- For example, "01 {10, 11} 11 {00}" --> "{00, 01, 10, 11}".
generalize :: Regex -> Regex
generalize xs = [KStar (sort . nub $ concatMap toBlock xs)] -- We keep words inside KStar sorted
    where toBlock (Const b) = [b]
          toBlock (KStar bs) = bs

-- Transform a regex into a more general one.
-- Segments which appear in the regex less than 'bound' number of times (and don't appear in a Kleene star)
-- are left untouched, while segments (and Kleene stars) in between those are replaced by a larger Kleene star.
pack :: Int -> Regex -> Regex
pack _ [] = []
pack bound tape = go tape
    where toBlock (Const b) = [(b, 1)]
          toBlock (KStar bs) = [(b, bound) | b <- bs]
          blockStats :: M.Map Segment Int
          blockStats = foldr (\(b, c) -> M.insertWith (+) b c) M.empty $ concatMap toBlock tape
          isUnique (Const b) = blockStats M.! b < bound
          isUnique _ = False
          go [] = []
          go ys = let (nq, rest) = break isUnique ys
                  in if null nq then (head ys) : go (tail ys)
                                else (generalize nq) ++ go rest

-- Applies 'pack' only if the regex starts with a constant block.
pack' :: Int -> Regex -> Regex
pack' bound ((Const c):xs) = (Const c) : pack bound xs
pack' bound xs = xs

-- Remove empty segments and Kleene stars.
clean :: Regex -> Regex
clean = filter (\c -> c /= (Const []) && c /= (KStar []))

-- Clean and pack both sides of a BlockTape.
tidy :: Int -> BlockTape -> BlockTape
tidy bound (BlockTape l h r) = BlockTape (pack' bound $ clean l) h (pack' bound $ clean r)

-- Segment size.
type Size = Int

-- Simulate a macro-step of the machine, branching to several possibilities if necessary.
-- Takes in the program, segment size, repetition bound for packing, and a BlockTape.
-- Outputs possible continuations after one macro step.
blockStep :: Program -> Size -> Int -> BlockTape -> Result [BlockTape]
blockStep prg size bound (BlockTape [] (Left s) r) = blockStep prg size bound (BlockTape [Const $ replicate size zeroC] (Left s) r) -- . <S r
blockStep prg size bound (BlockTape l (Right s) []) = blockStep prg size bound (BlockTape l (Right s) [Const $ replicate size zeroC]) -- l S> .
blockStep prg size bound (BlockTape ((Const w):ls) (Left s) r) = do -- ls w <S r
    (Tape l' h' r') <- runTillBorder prg (Tape w (Left s) [])
    return [tidy bound (BlockTape (Const l' : ls) h' (Const r' : r))]
blockStep prg size bound (BlockTape l (Right s) ((Const w):rs)) = do -- l S> w rs
    (Tape l' h' r') <- runTillBorder prg (Tape [] (Right s) w)
    return [tidy bound (BlockTape (Const l' : l) h' (Const r' : rs))]
blockStep prg size bound (BlockTape ((KStar ws):ls) (Left s) r) = do -- ls {ws} <S r
    return $ (BlockTape ls (Left s) r) : -- ls <S r
             [BlockTape (Const w : KStar ws : ls) (Left s) r | w <- ws] -- ls {ws} w <S r
blockStep prg size bound (BlockTape l (Right s) ((KStar ws):rs)) = do -- l S> {ws} rs
    return $ (BlockTape l (Right s) rs) : -- l S> rs
             [BlockTape l (Right s) (Const w : KStar ws : rs) | w <- ws] -- l S> w {ws} rs

-- Sort segments inside Kleene stars.
normalize :: BlockTape -> BlockTape
normalize (BlockTape l h r) = BlockTape (map norm l) h (map norm r)
    where norm (Const w) = Const w
          norm (KStar ws) = KStar (sort ws)

-- The starting configuration.
startB :: BlockTape
startB = BlockTape [] (Right 1) []

-- Run the machine for 1000 steps and split the tape into segments.
setupTape :: Program -> Size -> BlockTape
setupTape prg size = BlockTape (toBlocks l) h (toBlocks r)
    where Tape l h r = last $ runFor prg 1000
          compensate bs = bs ++ (replicate (size - length bs) zeroC)
          toBlocks xs = map (Const . compensate) $ chop size xs

-- Check if the machine is pointing at a Kleene star.
looksAtStar :: BlockTape -> Bool
looksAtStar (BlockTape ((KStar _):_) (Left _) _) = True
looksAtStar (BlockTape _ (Right _) ((KStar _):_)) = True
looksAtStar _ = False

-- Simulate the machine until it starts pointing at a Kleene star.
runTillStar :: Program -> Size -> Int -> BlockTape -> Result BlockTape
runTillStar prg size bound tape = go S.empty tape
    where go set t | looksAtStar t = return t
                   | t `S.member` set = Loop
                   | otherwise = case blockStep prg size bound t of
                                      Loop -> Loop
                                      Halt -> Halt
                                      Result [t'] -> go (S.insert t set) t'
                                      Result _ -> error "Something is wrong"

-- Run the Skelet grammar mode 3 decider.
-- Takes in the program, segment size, and a repetition bound.
-- Outputs the set of BlockTapes closed under macro steps, if it exists.
closedTapeLanguage :: Program -> Size -> Int -> Maybe [BlockTape]
closedTapeLanguage prg size bound = fmap (S.toList) $ go S.empty [startB] -- [setupTape prg size]
    where notLoop Loop = False
          notLoop _ = True
          go set new | S.size set > 10000 = Nothing
                     | otherwise = let reallyNew = S.toList $ (S.fromList new) S.\\ set
                                   in if null reallyNew
                                      then {- traceShow (S.size set) $ -} return set
                                      else case sequence . filter notLoop $ map (blockStep prg size bound) reallyNew of
                                                Result new' -> go (foldr S.insert set reallyNew) (concat new')
                                                _ -> Nothing

-- Given a segment size, repetition bound and a list of machines (in text format), try solving them with the decider.
-- It tries out all segment sizes and bounds up to given values, trying to utilize UCB to do it in a smarter way.
schedule :: Size -> Int -> [String] -> [String]
schedule size bound prgs = goOver prgs probs0
    where probs0 = [((s, b), 0, 1) | s <- [2..size], b <- [2..bound]]
          go _ call [] = ([], call [])
          go prg call (((s, b), succ, tries):xs) =
              case closedTapeLanguage (parse prg) s b of
                  Just sol ->  ([prg], call $ ((s, b), succ+1/(fromIntegral $ length sol), tries+1):xs)
                  Nothing -> go prg (call . (((s, b), succ, tries+1):)) xs
          goOver [] _ = []
          goOver (p:ps) probs = let time = sum $ map (\(_, _, t) -> t) probs
                                    (p', probs') = {- traceShow probs $ -} go p id probs
                                    probs'' = reverse $ sortBy (compare `on` (\(_, succ, tries) -> succ/tries + sqrt (2*(log time)/tries))) probs'
                                in p' ++ goOver ps probs''

exampleSpec1 :: Program
exampleSpec1 = parse "1RB0LC_1RC0RF_1RD1LA_1LE---_0RF1LE_1RA0LA"

exampleLong :: Program
exampleLong = parse "1RB3LA1LA4LA2RA_2LB2RA---0RA0RB"

-- Run the decider on many machines.
-- Takes block size and repetition bound as command line arguments.
-- For example,
-- > cat holdouts.txt | ./CTLBlock 4 3
-- will output the list of solved machines.
main = do
    [size, bound] <- map read `fmap` getArgs
    file <- lines `fmap` getContents
    mapM_ putStrLn $ schedule size bound file -- Use a fancy scheduler
    -- let rs = map (\p -> (p, closedTapeLanguage (parse p) size bound)) file -- Use specific parameters
    -- mapM_ (putStrLn . fst) $ filter (\(_, r) -> case r of Just _ -> True; _ -> False) rs -- Output solved
