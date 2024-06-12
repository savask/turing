{-
  This is a simplified implementation of Skelet's closed position set decider.

  The main idea of the decider is as follows.
  The tape is partitioned into segments of fixed width (width 4 in examples below).
  As in macro machines, we assume that the head is positioned between the segments (and may point left or right)
  and we always make sure that after several simulation steps the head lands between (some other) segments.
  For example, 0000 0101 A> 1110  -->  <B 1010 0110 0110.

  Instead of storing the whole tape, at each point of the computation we deal only with a 3 segment wide window;
  we will call each segment of the window, in order, the left, central and right segment. For example:
  in the window 1100 0101 C> 1110 the segment 1100 is left, 0101 is central and 1110 is right.
  A position is a window where the head is either between the left and central segments and is pointing to the left,
  or is between the central and right segment and is pointing to the right, for instance:
      1100 0101 C> 1110 and 0101 <A 1111 0110
  are correct positions, while
      <A 1111 0000 1010 or 0001 B> 1110 1010
  are not.

  The decider exhibits a set of positions such that the starting configuration lies in the set (i.e. 0000 0000 A> 0000)
  and simulating the machine moves it from one position to the next without halting or looping forever.
  Once the machine runs over one of window's ends, the decider must suggest a continuation, i.e. shift the window
  and guess the new cells. The principal idea is that we can keep two graphs (one for the left edge, one for the right),
  where segments are vertices, and edges mean that one segment may appear adjacent to the other.

  For example, if we started from 1100 0101 C> 1110 after several steps we may end at <A 0000 1011 0011.
  After that, we shift the window one segment to the left and obtain ???? <A 0000 1011, where question marks denote
  the unknown segment. Instead of bruteforcing all 2^4 possible segments to the left of the head, we take a look
  at the "left graph" and see arrows 1010 <- 1100 and 1110 <- 1100, which means we need to consider only two new positions:
      1010 <A 0000 1011 and 1110 <A 0000 1011.
  Note that we used 1100 as the edges' beginning, since initially the tape might have looked like
      ???? 1100 0101 C> 1110
  so the segment ???? is adjacent to 1100.

  This procedure is repeated for new positions until we find a position which makes the machine halt or loop forever
  (the decider fails to solve the problem in this case), or when adjacency graphs and position sets stop growing.
  If that happens, then we found the closed position set and the machine never halts.

  Finally, the rules governing left and right adjacency graphs must be described.
  At the start the graphs contain only two edges: 0000 <- 0000 for the left graph and 0000 -> 0000 for the right graph.
  This corresponds to the fact that the tape is filled with zeros at the start, i.e. after 0000 one may see 0000.
  The main rule is that we update adjacency graphs only when segments go over the border of the window (when we shift it).
  For example, if we had a position
      1100 0101 B> 0011
  and after simulating it we end up in
      <C 1111 1100 0110
  we add the edge 1100 -> 0110 to the right graph (since after shifting the window to the left, 0110 will go over the right border).
  If the initial right segment 0011 was adjacent to some segment XXXX in the right graph, we must also add an edge
      0110 -> XXXX
  for all such segments XXXX.

  Intuitively, two segments XXXX and YYYY are adjacent if either they were adjacent in some window (we show window borders with |):
      ... ???? | <A ???? XXXX YYYY | ???? ...
  or if YYYY was adjacent to some ZZZZ which later got changed into XXXX:
      ... ???? | ???? <B ???? ZZZZ | YYYY ...   -->   ... | <C ???? ???? XXXX | YYYY ...

  This program will output left and right graphs and the closed position set if the decider solves the machine.
  The closed position set is formatted as a graph, where the beginning of an edge is a position, and the
  end of an edge is the window after simulating the machine till it runs over window's edge.
  If the decider can't resolve the machine, it will output either "Halt" or "Loop" - that does not mean
  that the machine halts or loops but simply indicates that one the considered positions halts or loops.

  Note that in general segment sizes need not be the same. The input to this decider are three segment sizes
  (call them L, C and R) where the whole tape has a segment of length C in the middle, left infinite tape part
  is partitioned into segments of length L, while right infinite tape part is partitioned into segments of size R.
  In other words, the tape looks like this, where the window spans three consecutive segments:
      ... L L L L C R R R R ...
               |-----|
  To track segment lengths we associate to each segment its mode (a number from 0 to 2), where 0 corresponds to L,
  1 to C and 2 to R. Vertices of left and right adjacency graphs are in fact tuples, where the first component is the segment
  and the second component is its mode. Each window stored in the closed position set also stores a list of three modes
  alongside, for example, the window on the diagram above will store [0, 1, 2]. If the window spans segments of lengths
  C, R and R then the modes list will be [1, 2, 2] etc. The possible mode lists are:
      [0, 0, 0], [0, 0, 1], [0, 1, 2], [1, 2, 2], [2, 2, 2].
  When shifting the window left or right we update the mode list accordingly, by appending a mode extracted from
  the adjacency graph and dropping the mode of the segment which falls outside the window.

  Observe that even when all segment lengths are the same (i.e. L = C = R), mode does improve the decider as it can
  track the position of the Turing machine relative to the tape origin.

  This re-implementation of Skelet's decider is simplified, as it does not implement the "stop symbol S"
  for adjacency graphs (see Skelet's code for details). Empirically it seems that any machine solvable with the stop
  symbol is solvable without it but with, perhaps, larger segment sizes.

  This program solves machines #43374927 with segment size 4, #36909813 with size 2,
  "chaotic" machine #76708232 with size 2, "complex counter" #10936909 with size 2.

  Note that larger segment sizes don't always make the decider more powerful.
-}

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (mapMaybe)
import Data.Foldable (foldlM)
import System.Environment (getArgs)

import Machine

-- Mode is a residue modulo 3.
type Mode = Int

-- A segment is simply a piece of the tape with assigned mode.
type Segment = ([Cell], Mode)

-- The AdjacentGraph records which segments of the tape can (in principle) be adjacent to each other.
-- We will use two such graphs, one for segments appearing from the left part of the window, and one for the right part.
type Edge = (Segment, Segment)
type AdjacentGraph = M.Map Segment [Segment]

grToList :: AdjacentGraph -> [Edge]
grToList = concatMap (\(s, fs) -> [(s, f) | f <- fs]) . M.toList

-- Given a segment s, determine all segments f such that there's an edge s -> f in the graph.
adjacent :: AdjacentGraph -> Segment -> [Segment]
adjacent ag s = maybe [] id (M.lookup s ag)

-- Add an edge to the graph.
addEdge :: AdjacentGraph -> Edge -> AdjacentGraph
addEdge ag e = M.insertWith (\[x] ls -> if x `elem` ls then ls else x:ls) (fst e) [snd e] ag

-- The Info structure stores currently known graphs for segments appearing from the left and from the right,
-- as well as the currently explored position set.
data Info = Info {
            leftGraph :: AdjacentGraph,
            rightGraph :: AdjacentGraph,
            visitedTapes :: S.Set (Tape, [Mode])
            } deriving (Show)

-- Pretty print the Info structure. The program is needed to compute how tapes transform into each other.
showInfo :: Program -> Info -> String
showInfo prg (Info lgr rgr ts) = leftArrows ++ rightArrows ++ tapes
        where showEdge (s1, s2) = showBools (fst s1) ++ ", " ++ show (snd s1) ++ " --> " ++ showBools (fst s2) ++ ", " ++ show (snd s2)
              showEdge' (s1, s2) = showBools (reverse $ fst s2) ++ ", " ++ show (snd s2) ++ " <-- " ++ showBools (reverse $ fst s1) ++ ", " ++ show (snd s1)
              leftArrows = "Left continuations:\n" ++ (unlines . map showEdge' $ grToList lgr) ++ "\n"
              rightArrows = "Right continuations:\n" ++ (unlines . map showEdge $ grToList rgr) ++ "\n"
              showTape t = show t ++ " --> " ++
                           case runTillBorder prg t of
                               Halt -> "Halt"
                               Loop -> "Loop"
                               Result t' -> show t'
              tapes = "Transitions:\n" ++ (unlines . map (\(t, m) -> showTape t ++ ", " ++ show m) $ S.toList ts)

-- Number of edges in the adjacency gaph.
volGr :: AdjacentGraph -> Int
volGr = M.foldr (\a b -> length a + b) 0

-- Used to check when Info grows in size.
volume :: Info -> Int
volume (Info l r v) = volGr l + volGr r + S.size v

-- Returns last n symbols of ls.
lastN :: Int -> [a] -> [a]
lastN n ls = drop (length ls - n) ls

-- Sizes of segments, corresponding to each mode.
type Sizes = [Int]

-- Return size of the segment by mode.
-- For example, sizes [a, b, c] mean that 0 mode segment has size a, 1 mode segment has size b, 2 mode segment - size c.
sizeByMode :: Sizes -> Mode -> Int
sizeByMode sizes i = sizes !! (i `mod` (length sizes))

-- Given the program, segment sizes, known info, tape and current modes, update known info.
-- This procedure runs the machine till it exits the tape at either side,
-- adds new segment edges to the graph and adds new tapes to explore to the info structure.
simWindow :: Program -> Sizes -> Info -> (Tape, [Mode]) -> Result Info
simWindow prg sizes inf@(Info leftgr rightgr visited) (tape, [mll, mcc, mrr]) =
    case runTillBorder prg tape of
        Halt -> Halt
        Loop -> return inf -- We can skip looping positions
        Result t -> if null (right t) then return $ rightCase t else return $ leftCase t
    where [sll, scc, srr] = map (sizeByMode sizes) [mll, mcc, mrr] -- Sizes of window segments
           -- Machine went over the right border
          rightCase t = let ll = take sll . drop (scc+srr) $ left t
                            cc = take scc . drop srr $ left t
                            leftgr' = foldl addEdge leftgr $ -- If the tape was ll <? ccrr then s = ll
                                      ((cc, mcc), (ll, mll)):[((ll, mll), seg) | seg <- adjacent leftgr (lastN sll $ left tape, mll)]
                            continuations = adjacent rightgr (lastN srr $ right tape, mrr)
                            new = map (\(r, m) -> (Tape (take (srr+scc) $ left t) (at t) r, [mcc, mrr, m])) continuations
                        in Info leftgr' rightgr (foldr S.insert visited new)
          -- Machine went over the left border
          leftCase t = let cc = take scc . drop sll $ right t
                           rr = take srr . drop (sll+scc) $ right t
                           rightgr' = foldl addEdge rightgr $ -- If the tape was ll <? ccrr then s = rr
                                      ((cc, mcc), (rr, mrr)):[((rr, mrr), seg) | seg <- adjacent rightgr (lastN srr $ right tape, mrr)]
                           continuations = adjacent leftgr (lastN sll $ left tape, mll)
                           new = map (\(l, m) -> (Tape l (at t) (take (sll+scc) $ right t), [m, mll, mcc])) continuations
                       in Info leftgr rightgr' (foldr S.insert visited new)

-- Run the decider on a given program, segment sizes and shift.
-- We start at the initial tape 00..0 00..A>..00 00..0, where A> is "shift" away from the right end of the central segment
-- (zeros are in fact represented by Empty, as the corresponding cells were never visited).
-- The left and right adjacency graphs initially contain edges 00..0, mode 0 <- 00..0, mode 0 and 00..0, mode 2 -> 00..0, mode 2,
-- meaning that there may be infinite zeros in both directions.
-- We apply simWindow to each known tape until the info structure stops recording new edges or tapes.
closedPositionSet :: Program -> Sizes -> Int -> Result Info
closedPositionSet prg sizes shift = do
    let mds = [0, 1, 2]
        [sll, scc, srr] = map (sizeByMode sizes) mds
        blankTape = Tape (replicate (scc + sll - shift) Empty) (Right 1) (replicate (srr + shift) Empty)
    let chunk md = (replicate (sizeByMode sizes md) Empty, md)
        info0 = Info (M.singleton (chunk $ head mds) [(chunk $ head mds)])
                     (M.singleton (chunk $ last mds) [(chunk $ last mds)])
                     (S.singleton (blankTape, mds))
    go info0
    where go info = let tapes = visitedTapes info
                    in if length tapes > 20000 -- Prevent OOMs
                       then Loop
                       else do
                           info' <- foldlM (\i t -> simWindow prg sizes i t) info tapes
                           if volume info' > volume info
                           then go info'
                           else return info'

-- One of the "scary" machines, #36909813 in the database.
example :: Program
example = parse "1RB0RB_1LC0RA_1LD0LB_0LE---_1RE1LB"

-- Given a decreasing list of integers, return its maximal by divisibility elements.
-- removeDivisors [10,9..1] == [10,9,8,7,6]
removeDivisors :: [Int] -> [Int]
removeDivisors [] = []
removeDivisors (x:xs) = x : removeDivisors (filter (\y -> x `mod` y /= 0) xs)

-- Apply the decider trying segment lengths from 1 to n.
tryUpto :: Int -> Program -> Maybe Info
tryUpto n prg = if null results then Nothing else Just info
    where results = filter (\r -> case r of Result _ -> True; _ -> False)
                    [closedPositionSet prg [sll, scc, srr] s | scc <- [1..n], s <- [0..scc], sll <- lens, srr <- lens]
          lens = reverse . removeDivisors $ reverse [1..n]
          Result info = head results

-- Apply the decider trying segment lengths A, B, B where A and B range from 1 to n.
tryABB :: Int -> Program -> Maybe Info
tryABB n prg = if null results then Nothing else Just info
    where results = filter (\r -> case r of Result _ -> True; _ -> False)
                    [closedPositionSet prg [a, b, b] 0 | a <- lens, b <- lens]
          lens = reverse . removeDivisors $ reverse [1..n]
          Result info = head results

-- Print a one-line summary of the proof, including adjacency graphs and tapes if the machine was proved infinite.
-- For example, if there are N edges (s1, f1), ..., (sN, fN) in the left graph,
-- M edges (s'1, f'1), ..., (s'M', f'M) in the right graph,
-- and K positions p1, ..., pK in the closed position set, then output
-- "Result N s1 f1 s2 f2 ... sN fN K s'1 f'1 ... s'M f'M K p1 p2 ... pK"
-- Each segment is shown together with its mode.
showProof :: Maybe Info -> String
showProof Nothing = "Nothing"
showProof (Just (Info lgr rgr tapes)) = 
    let showSegment (ls, m) = showBools ls ++ " " ++ show m
        showVisited (ls, ms) = show ls ++ " " ++ unwords (map show ms)
    in "Result " ++
       show (volGr lgr) ++ " " ++
       (unwords . map (\(a, b) -> showSegment a ++ " " ++ showSegment b) $ grToList lgr) ++ " " ++
       show (volGr rgr) ++ " " ++
       (unwords . map (\(a, b) -> showSegment a ++ " " ++ showSegment b) $ grToList rgr) ++ " " ++
       show (length tapes) ++ " " ++
       (unwords . map showVisited $ S.toList tapes)

-- Run the decider on many machines and output certificates.
-- Machines are supplied from stdin (one per line in compact format),
-- the command line argument is the maximal width of the segments to try.
-- Outputs the list of machines tagged with either 'Nothing' or 'Result' with a proof certificate.
{-
main = do
    limit <- (read . head) `fmap` getArgs
    file <- lines `fmap` getContents
    let rs = map (\p -> (p, tryUpto limit (parse p))) file
    putStr . unlines $ map (\(p, pr) -> p ++ " " ++ showProof pr) rs
    -}

-- Run the decider on many machines. Machines are supplied from stdin (one per line in compact format),
-- the command line argument is the maximal width of the segments to try.
-- Outputs the number of decided machines. For example,
-- >cat tmList | ./Turing 3
-- 268271
main = do
    limit <- (read . head) `fmap` getArgs
    file <- lines `fmap` getContents
    let rs = map (\p -> (p, tryABB limit ({- addSymbolLog . addStateLog $ -} parse p))) file
    -- print . length $ filter (\(_, r) -> case r of Nothing -> False; _ -> True) rs
    putStr . unlines . map fst $ filter (\(_, r) -> case r of Nothing -> False; _ -> True) rs

-- Run the decider on one machine.
-- The first argument is segment size and the second is the machine in compact format.
-- For example,
-- >./Turing 2 1RB0LD_1LC1RC_1LA0RC_---0LE_0RB1LD
-- Nothing
{-
main = do
    [num, machine] <- getArgs
    let prg = parse machine
        size = read num
    case tryUpto size prg of
         Nothing -> putStrLn "Nothing"
         Just info -> putStr $ showInfo prg info
-}
