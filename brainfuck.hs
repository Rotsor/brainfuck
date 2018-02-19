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

data Env = Env {
  envTapeLeft :: [Int],
  envTapeHere :: Int,
  envTapeRight :: [Int],
  envProgram :: [Instruction]
 }

run :: Env -> IO ()
run (Env left here right []) = return ()
run (Env left here right (Plus : rest)) = run (Env left (here + 1) right rest)
run (Env left here right (Minus : rest)) = run (Env left (here - 1) right rest)
run (Env (l : left) here right (GoLeft : rest)) = run (Env left l (here : right) rest)
run (Env left here (r : right) (GoRight : rest)) = run (Env (here : left) r right rest)
run (Env left _here right (Get : rest)) = do
  char <- getChar
  run (Env left (fromEnum char) right rest)
run (Env left here right (Put : rest)) = do
  putChar (toEnum here)
  run (Env left here right rest)
run (Env left here right (While body : rest))
  | here == 0 = run (Env left here right rest)
  | otherwise = run (Env left here right (body ++ While body : rest))


parse1 ('.' : rest) = (Put, rest)
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

main = do
  args <- getArgs
  case args of
    [ prog ] -> do
--      print (parse prog)
      hSetBuffering stdin NoBuffering
      hSetBuffering stdout NoBuffering
      run (Env (repeat 0) 0 (repeat 0) (parse prog))
