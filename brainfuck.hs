{-# LANGUAGE ScopedTypeVariables #-}
import System.IO
import System.Environment
import Control.Monad.Identity


data Instruction =
  Plus
  | Minus
  | GoLeft
  | GoRight
  | Get
  | Put
  | While [Instruction]
  deriving (Show)

type Program = [Instruction]

data Env = Env {
  envTapeLeft :: [Int],
  envTapeHere :: Int,
  envTapeRight :: [Int],
  envProgram :: [Instruction]
 }

run :: Brainfuck m => Env -> m Env
run (env @ (Env left here right [])) = return env
run (Env left here right (Plus : rest)) = run (Env left (here + 1) right rest)
run (Env left here right (Minus : rest)) =
  if here >= 0 then run (Env left (here - 1) right rest)
  else error "negative number"
run (Env (l : left) here right (GoLeft : rest)) = run (Env left l (here : right) rest)
run (Env left here (r : right) (GoRight : rest)) = run (Env (here : left) r right rest)
run (Env left _here right (Get : rest)) = do
  x <- get
  run (Env left x right rest)
run (Env left here right (Put : rest)) = do
  put here
  run (Env left here right rest)
run (Env left here right (While body : rest))
  | here == 0 = run (Env left here right rest)
  | otherwise = run (Env left here right (body ++ While body : rest))


parse1 (' ' : rest) = parse1 rest
parse1 ('.' : rest) = (Put, rest)
parse1 (',' : rest) = (Get, rest)
parse1 ('+' : rest) = (Plus, rest)
parse1 ('<' : rest) = (GoLeft, rest)
parse1 ('>' : rest) = (GoRight, rest)
parse1 ('-' : rest) = (Minus, rest)
parse1 ('[' : rest) = runIdentity $ do
  (body, rest) <- return $ parseM rest
  return $ case rest of
    (']' : rest) -> (While body, rest)

parseM :: String -> ([Instruction], String)
parseM text = case text of
  [] -> ([], text)
  (']' : _) -> ([], text)
  _ -> runIdentity $ do
    (instr, rest) <- return $ parse1 text
    (instrs, rest) <- return $ parseM rest
    return (instr : instrs, rest)

parse s = case parseM s of
  (res, []) -> res

doWhile :: [Instruction] -> [Instruction]
doWhile prog = prog ++ [While prog]

p = parse

-- uses 5 slots of tape
-- to read a decimal
intReader :: [Instruction]
intReader =
  p "[-]>[-]>[-]>,----------[>[-]++++++[<------>-]<-- <<[-]>[-<+>]>> ++++++++++[<<<<[-]>[<+>>+<-]<[->+<] >>>>-]<[-<+>],----------]<<<[-]>>[-<<+>>]>"

-- pops a number, pushes result of dividion by 2: quotient and remainder
-- its stack frame layout:
-- 1. dividend (used as a loop counter)
-- 2. quotient accumulator
-- 3. iterations mod 2
-- 4. 1 - (iterations mod 2)
-- 5. tmp (used to increment 4)
divide2 :: [Instruction]
divide2 = p "[-]>[-]>[-]+>[-]<<<<[->>[->>+<<<+>]>[-<+>]>[-<+>]<<<<]>[-<+>]>[-<+>]"

render :: Program -> String
render = (>>= r) where
  r (While p) = "[" ++ render p ++ "]"
  r Get = ","
  r Put = "."
  r GoLeft = "<"
  r GoRight = ">"
  r Minus = "-"
  r Plus = "+"

-- [if_ n true false] pops a bool and runs the appropriate function.
-- it skips further [n] slots of the stack to be used and modified
-- by the branches.
-- It uses the next 2 stack items and zeroes them out.
if_ :: Int -> Program -> Program -> Program
if_ n true false =
  p (tr [('a', render true), ('b', render false)] $ tr_braces (n + 1) "<{[-]+<[-]>}[-{-<+>}]<{[->}a{<]>[-}b{]}")

pop :: [Instruction]
pop = p "<"

push0 :: Program
push0 = p "[-]>"


mulC c = push0 ++ push0 ++ push0 ++ p ("<<<<[->>+<<]>>>" ++ replicate c '+' ++ "[-<[-<+>]<[-<+>>+<]>>]<<")

addC c = p $ "<" ++ replicate c '+' ++ ">"

-- takes 1 number, returns 1 number
collatz = push0 ++ push0 ++ unearth 2 ++ duplicate ++ divide2 ++ if_
  2
  (pop ++ mulC 3 ++ addC 1 ++ duplicate)
  ([])
  ++ discard 1 4

-- duplicates top of stack
duplicate :: [Instruction]
duplicate = p "[-]>[-]<<[->+>+<<]>>[-<<+>>]"

tr substitutions s = foldr go s substitutions where
  go (from, to) = (>>= \c -> (if c == from then to else [c]))
tr_braces n =
  tr [('{', replicate n '<'),('}', replicate n '>')]

-- [discard keep drop] keeps [keep] top elements of the stack and discards the following [drop] ones
discard :: Int -> Int -> [Instruction]
discard 0 _ = []
discard keep drop = p $
  replicate (keep + drop) '<' ++
    concat (replicate keep $
      tr_braces drop "[-]}[-{+}]{>"
    )

-- duplicates the [i]th element of the stack.
-- unearth 0 = duplicate
unearth :: Int -> [Instruction]
unearth n = push0 ++ p (tr_braces (n+1) "[-]<{[-}+>+<{]}>[-<{+}>]")

class Monad m => Brainfuck m where
  get :: m Int
  put :: Int -> m ()

instance Brainfuck Identity where
  get = undefined
  put = undefined

instance Brainfuck IO where
  get = fmap fromEnum getChar
  put x = putChar (toEnum x)

debugStack :: [Int] -> [Instruction] -> [Int]
debugStack stack program =
  let env = runIdentity $ run (Env (stack ++ repeat undefined) 0 (repeat 0) program) in
  envTapeLeft env

-- works out to:
-- [-]>[-]>[-]>[-]<<<<[->>>+>+<<<<]>>>>[-<<<<+>>>>][-]>[-]<<[->+>+<<]>>[-<<+>>][-]>[-]>[-]+>[-]<<<<[->>[->>+<<<+>]>[-<+>]>[-<+>]<<<<]>[-<+>]>[-<+>]<<<<[-]+<[-]>>>>[-<<<-<+>>>>]<<<<[->>>><[-]>[-]>[-]><<<<[->>+<<]>>>+++[-<[-<+>]<[-<+>>+<]>>]<<<+>[-]>[-]<<[->+>+<<]>>[-<<+>>]<<<<]>[->>><<<]>>><<<<<[-]>>>>[-<<<<+>>>>]<<<<>
collatz_reference :: Int -> Int
collatz_reference n
  | n `mod` 2 == 0 = n `div` 2
  | otherwise = 3 * n + 1

testCases :: [(String, Program, [Int], [Int])]
testCases =
  [ ("divide2", divide2, [7], [1, 3])
  , ("push0", push0, [], [0])
  , ("unearth 3", unearth 3, [1,2,3,4], [4,1,2,3,4])
  , ("discard 2 3", discard 2 3, [1,2,3,4,5,6], [1,2,6])
  , ("duplicate", duplicate, [8], [8, 8])
  , ("mulC", mulC 10, [3], [30])
  , ("addC", addC 5, [2], [7])
  ]
  ++ [
   ("if 1", if_ 1 (addC 2) (addC 1), [1, 100, 8, 9], [102, 0, 0])
  ]
  ++ [ ("collatz " ++ show i, collatz, [i], [collatz_reference i]) | (i :: Int) <- [1..(50 :: Int)] ]

garbage = [88423,45456,57,235426,567562352,5235,56754]

runTestCase (name, program, input, reference_output) = do
  print $ "running test " ++ name
  let output_undefined = debugStack (input ++ repeat undefined) program
  let output_garbage = debugStack (input ++ garbage ++ repeat undefined) program
  if not (and $ zipWith (==) output_garbage (reference_output ++ garbage))
  then do
      putStrLn "Expected: "
      print (reference_output ++ garbage)
      putStrLn "Got: "
      print (take 5 $ zipWith (\x _ -> x) output_garbage (reference_output ++ garbage))
  else
    if not (and $ zipWith (==) output_undefined reference_output)
    then do
      putStrLn "Expected: "
      print reference_output
      putStrLn "Got: "
      print (zipWith (\x _ -> x) output_undefined reference_output)
    else
       return ()

main = do
  mapM_ runTestCase testCases
  putStrLn $ render collatz
