{-# LANGUAGE GeneralizedNewtypeDeriving, ViewPatterns, LambdaCase, MultiWayIf #-}

module Main where

import Control.Applicative
import Control.Monad.State
import Data.Bits
import Data.Maybe
import Data.Char
import Data.List
import Data.Either
import System.Environment
import Data.Word
import Numeric


-- TODO: add support for labels
-- TODO: add linenumbers to instructions
-- TODO: allow reading a register directly into the ALU, changing the cmp flags

data AnsiAttribute =
  Off | Bold | Underline | Undefined | Italic | BlinkSlow | BlinkRapid | Reverse | Conceal deriving (Show, Enum)

data AnsiColor =
  Black | Red | Green | Yellow | Blue | Magenta | Cyan | White deriving (Show, Enum)

data Encoding = ASCII | Unicode | ANSI

data CPUState = CPUState { lastIns   :: Maybe Instruction
                         , leftInss  :: [Instruction]
                         , rightInss :: [Instruction]
                         , flags     :: (Bool, Bool, Bool, Bool)
                         , cpuRegs   :: (Word8, Word8, Word8, Word8)
                         , output    :: Word8
                         } deriving (Show)

data Result = Result { resultIns  :: Maybe Instruction
                     , resultRegs :: [Word8]
                     , leds       :: Word8
                     } deriving (Show)

data Option = Option { switch :: Char
                     , desc   :: String
                     , action :: String -> IO ()
                     }

type CPURegs = (Word8, Word8, Word8, Word8)

newtype Constant = Constant Word8 deriving (Show, Enum, Real, Num, Ord, Eq, Integral)

data Register = RegA | RegB | RegC | RegD deriving (Show)

newtype Address = Address Word8 deriving (Show, Enum, Real, Num, Ord, Eq, Integral)

data Flag = Greater | Equal | Less | Carry | OrFlag Flag Flag | NotFlag Flag
          deriving (Show)

data Alu1Ins = Negate | Not deriving (Show)

data Alu2Ins = Add | ShiftLeft | ShiftRight | And | Or | Xor deriving (Show)

data Instruction = ConstTo Register Constant
                 | Output Register
                 | Jump Address
                 | JumpIf Flag Address
                 | CopyFromRegA Register
                 | Alu1 Alu1Ins Register
                 | Alu2 Alu2Ins Register
                 | Halt
                 deriving (Show)

stringsToIns :: [String] -> Either String Instruction
stringsToIns [['c', 't', r], c] | isReg = Right . ConstTo (head reg) =<< readC
  where isReg = not $ null reg
        reg = rights . pure . stringToReg $ pure r
        readC = case c of
          ['0', 'x', a, b] | [(x,"")] <- readHex [a,b] -> Right $ Constant x
          (reads -> [(x, "")]) | x < 256 && x >= -128 -> Right $ Constant (fromIntegral x)
                               | otherwise            -> Left $ c ++
                      " is outside the valid constant range of -128..255"
          _ -> Left $ show c ++ " is not a valid constant"
stringsToIns ["out", reg] = Right . Output =<< stringToReg reg
stringsToIns ['j' : cs, a] | isJump = Right . fromJust jmp =<< readA
  where isJump = isJust jmp
        jumpIfs = [ ("e", JumpIf Equal)
                  , ("z", JumpIf Equal)
                  , ("g", JumpIf Greater)
                  , ("l", JumpIf Less)
                  , ("c", JumpIf Carry)
                  ]
        jmp | cs == "mp" = Just Jump
            | otherwise  = lookup cs jumpIfs
        readA = case reads a of
                     [(x, "")] | x < 128 && x >= -128 -> Right $ Address (fromIntegral x)
                               | otherwise            -> Left $ a ++
                               " is outside the valid address range of -128..127"
                     _ -> Left $ show a ++ " is not a valid address"
stringsToIns [ins, reg] | ins `elem` ["mov", "cpy"] = Right . CopyFromRegA =<< stringToReg reg
stringsToIns [ins, reg] | isAlu = Right . fromJust alu =<< stringToReg reg
  where isAlu = isJust alu
        alu1s = [ ("neg", Negate)
                , ("not", Not)
                ]
        alu2s = [ ("add", Add)
                , ("shl", ShiftLeft)
                , ("shr", ShiftRight)
                , ("and", And)
                , ("or" , Or )
                , ("xor", Xor)
                ]
        aluLU a as = a <$> lookup ins as
        alu = aluLU Alu1 alu1s <|> aluLU Alu2 alu2s
stringsToIns ["halt"] = Right Halt
stringsToIns s = Left $ show (unwords s) ++ " is not a valid Instruction"

stringToReg :: String -> Either String Register
stringToReg "a" = Right RegA
stringToReg "b" = Right RegB
stringToReg "c" = Right RegC
stringToReg "d" = Right RegD
stringToReg s = Left $ "No register named " ++ show s

linesToInss :: [String] -> Either String [Maybe Instruction]
linesToInss =
  mapM (sequenceA . fmap (stringsToIns . words) . emptyLine . takeWhile (/= ';'))
    where emptyLine l | all isSpace l = Nothing
                      | otherwise     = Just l

regToHex :: Register -> String
regToHex RegA = "0"
regToHex RegB = "1"
regToHex RegC = "2"
regToHex RegD = "3"

regToInt :: Register -> Int
regToInt RegA = 0
regToInt RegB = 1
regToInt RegC = 2
regToInt RegD = 3

insToHex :: Instruction -> String
insToHex (ConstTo r c) = "1" ++ regToHex r ++ nChar '0' 2 (showHex (fromIntegral c) "")
insToHex (Output r) = "1" ++ showHex (regToInt r + 8) "00"
insToHex (Jump a) = "20" ++ nChar '0' 2 (showHex (fromIntegral a) "")
insToHex (JumpIf f a) = "2" ++ flagToHex f ++ nChar '0' 2 (showHex (fromIntegral a) "")
insToHex (CopyFromRegA r) = "3" ++ showHex (regToInt r) "00"
insToHex (Alu1 i r) = "4" ++ alu1InsToHex i ++ "0" ++ regToHex r
insToHex (Alu2 i r) = "8" ++ alu2InsToHex i ++ "0" ++ regToHex r
insToHex Halt = "0000"

alu1InsToHex :: Alu1Ins -> String
alu1InsToHex Negate = nChar '0' 2 "6"
alu1InsToHex Not    = nChar '0' 2 "7"

alu2InsToHex :: Alu2Ins -> String
alu2InsToHex Add        = "0"
alu2InsToHex ShiftLeft  = "1"
alu2InsToHex ShiftRight = "2"
alu2InsToHex And        = "3"
alu2InsToHex Or         = "4"
alu2InsToHex Xor        = "5"

flagToHex :: Flag -> String
flagToHex Greater = "2"
flagToHex Equal   = "1"
flagToHex Less    = "3"
flagToHex Carry   = "8"
flagToHex (OrFlag _ _) = error
  "jumps that depend on more than one flag are currently not available"
flagToHex (NotFlag _) = error
  "jumps that negate flags are currently not available"

appendOriginal :: [String] -> [Maybe Instruction] -> [String]
appendOriginal ls ms = zipWith ((++) . (++ "    ") . fromMaybe "    ") hexs ls
  where hexs = map (fmap insToHex) ms

printHexAndOrig :: String -> IO ()
printHexAndOrig file = do
  content <- lines <$> readFile file
  mapM_ putStrLn . either pure (appendOriginal content) $ linesToInss content

printHex :: String -> IO ()
printHex file = do
  content <- lines <$> readFile file
  mapM_ putStrLn . either pure (map insToHex . catMaybes) $ linesToInss content

-- TODO: maybe group two adjacent lines together and separate them with a space
-- instead. Logisim doesn't seem to care about what kind of whitespace
-- separates the bytes, and it will make the text file nicer to look at.
printLogisim :: String -> IO ()
printLogisim file = do
  content <- lines <$> readFile file
  -- TODO actually pairs is wrong because we have 16 data bits in our ROM, not
  -- 8
  let pairs :: [String] -> [String]
      pairs ([a,b,c,d] : rest) = [a,b] : [c,d] : pairs rest
      pairs _ = []
  putStrLn . ("v2.0 raw\n" ++) . unlines . pairs . either pure (map insToHex . catMaybes) $
    linesToInss content

simulate :: State CPUState [Result]
simulate = gets rightInss >>= \case
    []         -> return []
    (Halt : _) -> return []
    (i : _)   ->
      unsafeIncIns >> eval i >> putLI i >> gets newSimResult >>= (<$> simulate) . (:)
  where
    unsafeIncIns :: State CPUState ()
    unsafeIncIns = modify' $ \s@(CPUState _ ls (r:rs) _ _ _) -> s {leftInss = r : ls, rightInss = rs}

putLI :: Instruction -> State CPUState ()
putLI i = modify' $ \s -> s {lastIns = Just i}

putReg :: Register -> Word8 -> State CPUState ()
putReg r x = modify' $ \s@(CPUState _ _ _ _ (a,b,c,d) _) ->
  let newRegs = case r of
        RegA -> (x,b,c,d)
        RegB -> (a,x,c,d)
        RegC -> (a,b,x,d)
        RegD -> (a,b,c,x)
  in s {cpuRegs = newRegs}

putFlag :: Flag -> Bool -> State CPUState ()
putFlag f b = modify' $ \s@(CPUState _ _ _ (g,e,l,c) _ _) ->
  let newFlags = case f of
        Greater -> (b,e,l,c)
        Equal   -> (g,b,l,c)
        Less    -> (g,e,b,c)
        Carry   -> (g,e,l,b)
  in s {flags = newFlags}

putFlags :: Ordering -> State CPUState ()
putFlags GT = putFlag Greater True  >> putFlag Equal False >> putFlag Less False
putFlags EQ = putFlag Greater False >> putFlag Equal True  >> putFlag Less False
putFlags LT = putFlag Greater False >> putFlag Equal False >> putFlag Less True

putOutput :: Word8 -> State CPUState ()
-- XXX is there a shorter way to write this?
putOutput x = modify' $ \s -> s {output = x}

-- we jump backwards one extra step because we increment before that
jump :: Address -> State CPUState ()
jump (Address a) = modify' $ \cs@(CPUState _ ls rs _ _ _) ->
  if | a == 0    -> cs {leftInss = drop 1 ls, rightInss = take 1 ls ++ rs}
     | a > 127   -> let s = - (fromIntegral a - 256 - 1)
                        (r, l) = splitAt s ls
                    in cs {leftInss = l, rightInss = reverse r ++ rs}
     | otherwise -> let s = fromIntegral a - 1
                        (l, r) = splitAt s rs
                    in cs {leftInss = ls ++ l, rightInss = r}

getReg :: Register -> State CPUState Word8
getReg r = gets cpuRegs >>= \(a,b,c,d) -> return $ case r of
  RegA -> a
  RegB -> b
  RegC -> c
  RegD -> d

getFlag :: Flag -> State CPUState Bool
getFlag f = gets flags >>= \(g,e,l,c) -> return $ case f of
  Greater -> g
  Equal   -> e
  Less    -> l
  Carry   -> c

eval :: Instruction -> State CPUState ()
eval (ConstTo r (Constant x)) = putReg r x
eval (Output r) = getReg r >>= putOutput
eval (Jump a) = jump a
eval (JumpIf f a) = evalFlag f >>= \b -> when b $ jump a
eval (CopyFromRegA r) = getReg RegA >>= putReg r
eval (Alu1 i r) = evalAlu1 i r
eval (Alu2 i r) = evalAlu2 i r
eval Halt = return ()

evalAlu1 :: Alu1Ins -> Register -> State CPUState ()
evalAlu1 i r = do
  let f = case i of
            Negate -> negate
            Not    -> complement
  x <- f <$> getReg r
  putReg r x
  putFlags $ compare x 0

evalAlu2 :: Alu2Ins -> Register -> State CPUState ()
evalAlu2 i r = do
  a <- getReg RegA
  x <- getReg r
  let f = flip $ case i of
            Add        -> (+)
            ShiftLeft  -> flip shiftL . fromIntegral
            ShiftRight -> flip shiftR . fromIntegral
            And        -> (.&.)
            Or         -> (.|.)
            Xor        -> xor
  let res =  f a x
  putReg RegA res
  putFlags $ compare res 0
  case i of
    Add -> putFlag Carry (let sum = fromIntegral a + fromIntegral x in sum > 127 || sum < 128)

evalFlag :: Flag -> State CPUState Bool
evalFlag (OrFlag f g) = evalFlag f >>= \fb -> evalFlag g >>= \gb -> return $ fb || gb
evalFlag (NotFlag f) = not <$> evalFlag f
evalFlag f = getFlag f

newSimResult :: CPUState -> Result
newSimResult (CPUState li _ _ _ (a,b,c,d) out) = Result li [a,b,c,d] out

prettyIns :: Instruction -> String
prettyIns (ConstTo r c) = "ct" ++ prettyReg r ++ " " ++ prettyConst c
prettyIns (Output r) = "out " ++ prettyReg r
prettyIns (Jump a) = "jmp " ++ prettyAddress a
prettyIns (JumpIf f a) = "j" ++ prettyFlag f ++ " " ++ prettyAddress a
prettyIns (CopyFromRegA r) = "mov " ++ prettyReg r
prettyIns (Alu1 i r) = prettyAlu1Ins i ++ " " ++ prettyReg r
prettyIns (Alu2 i r) = prettyAlu2Ins i ++ " " ++ prettyReg r
prettyIns Halt = "halt"

prettyAlu1Ins :: Alu1Ins -> String
prettyAlu1Ins Negate = "neg"
prettyAlu1Ins Not = "not"

prettyAlu2Ins :: Alu2Ins -> String
prettyAlu2Ins Add = "add"
prettyAlu2Ins ShiftLeft = "shl"
prettyAlu2Ins ShiftRight = "shr"
prettyAlu2Ins And = "and"
prettyAlu2Ins Or = "or"
prettyAlu2Ins Xor = "xor"

prettyFlag :: Flag -> String
prettyFlag Greater = "g"
prettyFlag Equal = "z"
prettyFlag Less = "l"
prettyFlag Carry = "c"
prettyFlag (NotFlag f) = "n" ++ prettyFlag f
prettyFlag (OrFlag f g) = prettyFlag f ++ prettyFlag g

prettyAddress :: Address -> String
prettyAddress (Address a) = sign a

prettyReg :: Register -> String
prettyReg RegA = "a"
prettyReg RegB = "b"
prettyReg RegC = "c"
prettyReg RegD = "d"

prettyConst :: Constant -> String
prettyConst (Constant c) = "0x" ++ nChar '0' 2 (showHex c " ; u: ") ++ show c ++ " ; s: " ++ sign c

prettyResult :: Encoding -> Result -> String
prettyResult enc (Result li regs ls) =
  line ++ lastI ++ regLine True ++ regsHex ++ regsU ++ regsDec ++ regLine False ++ diodes
  where
    lastI = maybe "Initial State:\n" (\i -> "Current Instruction: " ++ instruction i ++ "\n") li
    instruction = ansiFg Red . ansiAttr Bold . prettyIns
    regLine isTop = intercalate "  " (replicate (length regs) $ if isTop then topReg else botReg) ++ "\n"
    ansiAttr attr = ansiNum $ fromEnum attr
    ansiFg col = ansiNum (30 +  fromEnum col)
    ansiBg col = ansiNum (40 + fromEnum col)
    ansiNum = ansiCustom . show
    ansiCustom fmt s = case enc of ANSI -> "\ESC[" ++ fmt ++ "m" ++ s ++ "\ESC[m"
                                   _    -> s
    topReg = case enc of ASCII -> "+---------+"
                         _     -> ansiFg Blue "┎─────────┐"
    botReg = case enc of ASCII -> "+---------+"
                         _     -> ansiFg Blue "┖─────────┘"
    regsHex = mkRegs $ zipWith (\c r -> ansiFg Green (c : ": ") ++
      ansiAttr Bold (ansiFg White (nChar ' ' 4 ("0x" ++ showHex r "")))) ['A'..] regs
    regsU = mkRegs $ map (ansiFg White . ("    " ++) . nChar ' ' 3 . show) regs
    regsDec = mkRegs $ map (ansiFg White . ("   " ++) . nChar ' ' 4 . sign) regs
    mkRegs rs = regStart ++ intercalate regSep rs ++ regStop ++ "\n"
    regStart = case enc of ASCII   -> "| "
                           _       -> ansiFg Blue "┃ "
    regSep   = case enc of ASCII   -> " |  | "
                           _       -> ansiFg Blue " │  ┃ "
    regStop  = case enc of ASCII   -> " |"
                           _       -> ansiFg Blue " │"
    diodes = "    " ++ insertSpace (map applyEnc (nChar '0' 8 $ showIntAtBase 2 ("01" !!) ls "")) ++
      yl "    hex: " ++ bw ("0x" ++ showHex ls "") ++ yl "   udec: " ++ wt (show ls) ++ yl "    sdec: " ++ wt (sign ls)
    bw = ansiAttr Bold . ansiFg White
    yl = ansiFg Yellow
    wt = ansiFg White
    diodeDigits = case enc of ASCII   -> "O0"
                              _       -> "○●"
    applyEnc l | l == '0' = case enc of
                 ASCII   -> "O"
                 Unicode -> "○"
                 ANSI    -> ansiFg Black "●"
               | otherwise = case enc of
                 ASCII   -> "0"
                 Unicode -> "●"
                 ANSI    -> ansiFg Red "●"
    insertSpace (a:b:c:d:r) = concat $ a:b:c:d:" ":r
    line | isNothing li   = ""
         | otherwise      = case enc of ASCII   -> replicate 50 '_' ++ "\n\n"
                                        _       -> ansiFg Cyan $ replicate 50 '─' ++ "\n"

sign :: Word8 -> String
sign (fromIntegral -> x) | x > 127   = show (x - 256)
                         | otherwise = show x

nChar :: Char -> Int -> String -> String
nChar c n s = replicate (n - length s) c ++ s

defaultCPU :: CPUState
defaultCPU = CPUState Nothing [] [] (False, False, False, False) (0, 0, 0, 0) 0

runCPU :: Encoding -> String -> IO ()
runCPU enc file = do
  content <- lines <$> readFile file
  either putStrLn (run . catMaybes) $ linesToInss content
  where run = mapM_ (putStrLn . prettyResult enc) . results
        results is = newSimResult (cpu is) : evalState simulate (cpu is)
        cpu is = defaultCPU {rightInss = is}

main :: IO ()
main = getArgs >>= \case
  [['-', o], file] | isJust option -> fromJust option file
    where option = lookupOption options
          lookupOption [] = Nothing
          lookupOption (s:ss) | o == switch s = Just $ action s
                              | otherwise     = lookupOption ss
  _ -> getProgName >>= putStrLn . usage

usage :: String -> String
usage progName = "Usage: " ++ progName ++ " -(" ++ switches ++ ") FILE\n" ++ optionDescs
  where
    switches = intersperse '|' $ map switch options
    optionDescs =
      unlines $ zipWith ((++) . ("  -" ++) . (:": ")) (map switch options) (map desc options)

options :: [Option]
options = [ Option 'p' "print both hexadecimal and the original assembly"   printHexAndOrig
          , Option 'h' "print only hexadecimal"                             printHex
          , Option 'l' "print in Logisim ROM format"                        printLogisim
          , Option 'r' "simulate the CPU (ASCII output)"                  $ runCPU ASCII
          , Option 'u' "simulate the CPU (Unicode output)"                $ runCPU Unicode
          , Option 'a' "simulate the CPU (ANSI output)"                   $ runCPU ANSI
          ]
