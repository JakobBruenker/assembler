{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE Rank2Types                 #-}

module Main where

import Control.Applicative
import Control.Monad.State
import Data.Bits
import Data.Bool
import Data.Maybe
import Data.Char
import Data.List
import Data.Either
import System.Environment
import Data.Word
import Numeric
import Lens.Simple


-- TODO: maybe change it so registers is not actually a record, but a function
-- from RegisterID to RegisterContent, and then hide it through lenses
-- TODO: maybe use Control.Lens just so we can use Zoom
-- TODO: divide into several modules
-- TODO: allow to run only up to a certain number of steps
-- TODO: print out in binary
-- TODO: maybe change from using _leftInss and _rightInss to using just an array
-- (or a list) of Instructions and an instruction pointer
-- TODO: add support for labels
-- TODO: add linenumbers to instructions
-- TODO: add instruction to negate _flags
-- maybe also just remove Greater and Less, and just allow jumps depending on
-- Equal or Not equal (and carry)
-- TODO: allow reading a register directly into the ALU, changing the cmp
-- _flags.
-- TODO: add a second carry flag for signed operation actually - technically
-- don't need signed one because you can get it from anding with 1000 0000, or
-- something

data FlagStatus = Set | Unset deriving (Eq)

newtype RegContent = RegContent {_regContent :: Word8}
  deriving (Eq, Ord, Integral, Real, Enum, Num, Bits)

$(makeLenses ''RegContent)

data AnsiAttribute =
  Off | Bold | Underline | Undefined | Italic | BlinkSlow | BlinkRapid | Reverse | Conceal deriving (Enum)

data AnsiColor =
  Black | Red | Green | Yellow | Blue | Magenta | Cyan | White deriving (Enum)

data Charset = ASCII | Unicode | ANSI

data FlagID = Greater | Equal | Less | Carry deriving (Enum, Eq, Ord)

data Registers = Registers { _regA :: RegContent
                           , _regB :: RegContent
                           , _regC :: RegContent
                           , _regD :: RegContent
                           }

$(makeLenses ''Registers)

data Flags = Flags { _greater :: FlagStatus
                   , _equal   :: FlagStatus
                   , _less    :: FlagStatus
                   , _carry   :: FlagStatus
                   }

$(makeLenses ''Flags)

newtype ConstNum = ConstNum Word8 deriving (Enum, Real, Num, Ord, Eq, Integral)

data RegisterID = RegA | RegB | RegC | RegD deriving (Enum)

newtype Address = Address Word8 deriving (Enum, Real, Num, Ord, Eq, Integral)

data Alu1Ins = Negate | Not

data Alu2Ins = Add | ShiftLeft | ShiftRight | And | Or | Xor

data Instruction = ConstTo RegisterID ConstNum
                 | Output RegisterID
                 | Jump Address
                 | JumpIf FlagID Address
                 | CopyFromRegA RegisterID
                 | Alu1 Alu1Ins RegisterID
                 | Alu2 Alu2Ins RegisterID
                 | Halt

data CPU = CPU { _flags     :: Flags
               , _registers :: Registers
               , _output    :: Word8
               }

$(makeLenses ''CPU)

data Simulation = Simulation { _lastIns   :: Maybe Instruction
                             , _leftInss  :: [Instruction]
                             , _rightInss :: [Instruction]
                             , _cpuSteps  :: Integer
                             , _cpu       :: CPU
                             }

$(makeLenses ''Simulation)

data Result = Result { _resultIns   :: Maybe Instruction
                     , _resultRegs  :: Registers
                     , _leds        :: Word8
                     , _resultSteps :: Integer
                     }

$(makeLenses ''Result)

data Option = Option { _switch :: Char
                     , _desc   :: String
                     , _action :: String -> IO ()
                     }

$(makeLenses ''Option)

register :: RegisterID -> Lens' Registers RegContent
register RegA = regA
register RegB = regB
register RegC = regC
register RegD = regD

listRegisters :: Registers -> [RegContent]
listRegisters rs = map ((rs&) . view . register) [RegA ..]

flag :: FlagID -> Lens' Flags FlagStatus
flag Greater = greater
flag Equal   = equal
flag Less    = less
flag Carry   = carry

stringsToIns :: [String] -> Either String Instruction
stringsToIns [['c', 't', r], c] | isReg = Right . ConstTo (head reg) =<< readC
  where isReg = not $ null reg
        reg = rights . pure . stringToReg $ pure r
        readC = case c of
          ['0', 'x', a, b] | [(x,"")] <- readHex [a,b] -> Right $ ConstNum x
          (reads -> [(x, "")]) | x < 256 && x >= -128 -> Right $ ConstNum (fromIntegral x)
                               | otherwise            -> Left $ c ++
                      " is outside the valid constant range of -128..255"
          _ -> Left $ show c ++ " is not a valid constant"
stringsToIns ["out", reg] = Right . Output =<< stringToReg reg
stringsToIns ['j' : cs, a] | Just j <- jmp = Right . j =<< readA
  where jmp | cs == "mp" = Just Jump
            | otherwise  = lookup cs jumpIfs
        jumpIfs = [ ("e", JumpIf Equal)
                  , ("z", JumpIf Equal)
                  , ("g", JumpIf Greater)
                  , ("l", JumpIf Less)
                  , ("c", JumpIf Carry)
                  ]
        readA = case reads a of
                     [(x, "")] | x < 128 && x >= -128 -> Right $ Address (fromIntegral x)
                               | otherwise            -> Left $ a ++
                               " is outside the valid address range of -128..127"
                     _ -> Left $ show a ++ " is not a valid address"
stringsToIns [ins, reg] | ins `elem` ["mov", "cpy"] = Right . CopyFromRegA =<< stringToReg reg
stringsToIns [ins, reg] | Just i <- alu = Right . i =<< stringToReg reg
  where alu1s = [ ("neg", Negate)
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

stringToReg :: String -> Either String RegisterID
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

regToHex :: RegisterID -> String
regToHex RegA = "0"
regToHex RegB = "1"
regToHex RegC = "2"
regToHex RegD = "3"

regToInt :: RegisterID -> Int
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

flagToHex :: FlagID -> String
flagToHex Greater = "2"
flagToHex Equal   = "1"
flagToHex Less    = "3"
flagToHex Carry   = "8"

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

printLogisim :: String -> IO ()
printLogisim file = do
  content <- lines <$> readFile file
  putStrLn . ("v2.0 raw\n" ++) . unlines . either pure (map insToHex . catMaybes) $
    linesToInss content

simulate :: State Simulation [Result]
simulate = use rightInss >>= \case
    []    -> return []
    (i:_) ->
      incIns i >> eval i >> putLI i >> gets newSimResult >>= (<$> case i of Halt -> return []
                                                                            _    -> simulate) . (:)
  where incIns i = modify' $ (leftInss %~ (i :)) . (rightInss %~ drop 1) . (cpuSteps %~ (+1))

putLI :: Instruction -> State Simulation ()
putLI i = lastIns .= Just i

putReg :: RegisterID -> RegContent -> State Simulation ()
putReg r = assign $ cpu.registers.register r

putFlag :: FlagID -> FlagStatus -> State Simulation ()
putFlag f = assign $ cpu.flags.flag f

putFlags :: Ordering -> State Simulation ()
putFlags = zipWithM_ putFlag [ Greater, Equal, Less  ] . \case
  GT ->                      [ Set    , Unset, Unset ]
  EQ ->                      [ Unset  , Set  , Unset ]
  LT ->                      [ Unset  , Unset, Set   ]

putOutput :: Word8 -> State Simulation ()
putOutput = assign $ cpu.output

-- we jump backwards one extra step because we increment before that
jump :: Address -> State Simulation ()
jump (Address a) = modify' $ \ss -> let ls = ss^.leftInss
                                        rs = ss^.rightInss in
  (if | a == 0    -> (leftInss %~ drop 1) . (rightInss %~ (take 1 ls ++))
      | a > 127   -> let s = - (fromIntegral a - 256 - 1)
                         (r, ls') = splitAt s ls
                     in (leftInss .~ ls') . (rightInss %~ (reverse r ++))
      | otherwise -> let s = fromIntegral a - 1
                         (l, rs') = splitAt s rs
                     in (leftInss %~ (++ l)) . (rightInss .~ rs')) ss

getReg :: RegisterID -> State Simulation RegContent
getReg r = use $ cpu.registers.register r

getFlag :: FlagID -> State Simulation FlagStatus
getFlag f = use $ cpu.flags.flag f

eval :: Instruction -> State Simulation ()
eval (ConstTo r (ConstNum x)) = putReg r $ RegContent x
eval (Output r)               = putOutput . view regContent =<< getReg r
eval (Jump a)                 = jump a
eval (JumpIf f a)             = (when ?? jump a) . (== Set) =<< getFlag f
eval (CopyFromRegA r)         = putReg r =<< getReg RegA
eval (Alu1 i r)               = evalAlu1 i r
eval (Alu2 i r)               = evalAlu2 i r
eval Halt = return ()

evalAlu1 :: Alu1Ins -> RegisterID -> State Simulation ()
evalAlu1 i r = do
  let f = case i of
            Negate -> negate
            Not    -> complement
  x <- f <$> getReg r
  putReg r x
  putFlags $ compare x 0

evalAlu2 :: Alu2Ins -> RegisterID -> State Simulation ()
evalAlu2 i r = do
  a <- getReg RegA
  x <- getReg r
  let res = (case i of
        Add        -> (+)
        ShiftLeft  -> (. fromIntegral) . shiftL
        ShiftRight -> (. fromIntegral) . shiftR
        And        -> (.&.)
        Or         -> (.|.)
        Xor        -> xor)
        a x
  putReg RegA res
  putFlags $ compare res 0
  case i of
    Add -> putFlag Carry . bool Unset Set $ fromIntegral a + fromIntegral x > 255
    _   -> return ()

newSimResult :: Simulation -> Result
newSimResult ss = Result { _resultIns   = ss^.lastIns
                         , _resultRegs  = ss^.cpu.registers
                         , _leds        = ss^.cpu.output
                         , _resultSteps = ss^.cpuSteps
                         }

prettyIns :: Instruction -> String
prettyIns (ConstTo r c)    = "ct" ++ prettyReg r ++ " " ++ prettyConst c
prettyIns (Output r)       = "out " ++ prettyReg r
prettyIns (Jump a)         = "jmp " ++ prettyAddress a
prettyIns (JumpIf f a)     = "j" ++ prettyFlagID f ++ " " ++ prettyAddress a
prettyIns (CopyFromRegA r) = "mov " ++ prettyReg r
prettyIns (Alu1 i r)       = prettyAlu1Ins i ++ " " ++ prettyReg r
prettyIns (Alu2 i r)       = prettyAlu2Ins i ++ " " ++ prettyReg r
prettyIns Halt             = "halt"

prettyAlu1Ins :: Alu1Ins -> String
prettyAlu1Ins Negate = "neg"
prettyAlu1Ins Not    = "not"

prettyAlu2Ins :: Alu2Ins -> String
prettyAlu2Ins Add        = "add"
prettyAlu2Ins ShiftLeft  = "shl"
prettyAlu2Ins ShiftRight = "shr"
prettyAlu2Ins And        = "and"
prettyAlu2Ins Or         = "or"
prettyAlu2Ins Xor        = "xor"

prettyFlagID :: FlagID -> String
prettyFlagID Greater = "g"
prettyFlagID Equal   = "z"
prettyFlagID Less    = "l"
prettyFlagID Carry   = "c"

prettyAddress :: Address -> String
prettyAddress (Address a) = sign a

prettyReg :: RegisterID -> String
prettyReg RegA = "a"
prettyReg RegB = "b"
prettyReg RegC = "c"
prettyReg RegD = "d"

prettyConst :: ConstNum -> String
prettyConst (ConstNum c) = "0x" ++ nChar '0' 2 (showHex c " ; ") ++ show c ++ " ; " ++ sign c

prettyResults :: Charset -> [Result] -> String
prettyResults chs = tblines . concatMap (prettyResult chs)
  where tblines s = lineWith '┏' '┓' ++ s ++ lineWith '┗' '┛'
        lineWith l r = case chs of ASCII -> ""
                                   _     -> ansiForeground chs Cyan $ l : replicate 45 '━' ++ r : "\n"

ansiAttribute :: Charset -> AnsiAttribute -> String -> String
ansiAttribute chs attr = ansiNumber chs $ fromEnum attr

ansiForeground :: Charset -> AnsiColor -> String -> String
ansiForeground chs col = ansiNumber chs  (30 +  fromEnum col)

ansiNumber :: Charset -> Int -> String -> String
ansiNumber chs = ansiCustom chs . show

ansiCustom :: Charset -> String -> String -> String
ansiCustom chs fmt s = case chs of ANSI -> "\ESC[" ++ fmt ++ "m" ++ s ++ "\ESC[m"
                                   _    -> s

-- putting 3 different Charsets together makes this a bit clumsy (although
-- I think it definitely makes sense to put Unicode and ANSI together)
prettyResult :: Charset -> Result -> String
prettyResult chs (Result li (map (^.regContent) . listRegisters -> regs) ls steps) =
  line False ++ lastI ++ line True ++ regLine True ++ regsHex ++ regsU ++ regsDec ++ regLine False ++ diodes
  where
    lastI = br 1 . bl $ lastI' ++ spaces dispSteps
    -- using nChar here makes this a bit confusing to be honest
    spaces = (asciiUni "       " "" ++) .
      nChar ' ' (43 - length lastI' + maybe 1 (const 2) li * length (bw ""))
    lastI' = maybe "" (ansiFg Red . ansiAttr Bold . prettyIns) li
    dispSteps = ansiFg Magenta . ansiAttr Bold $ show steps
    regLine isTop = br 1 . bl $ intercalate sepDist (replicate 4 $ oneReg isTop)
    oneReg isTop = case chs of ASCII -> "+---------+"
                               _     -> ansiFg Blue $ if isTop then "┏━┯━━━━━━┓" else "┗━━━━━━━━┛"
    ansiFg = ansiForeground chs
    ansiAttr = ansiAttribute chs
    regsHex = br 1 . bl $ mkRegs False $ zipWith (\c r -> ansiFg Green (pure c) ++
      asciiUni "  " (ansiFg Blue "│ ") ++
      "0x" ++ bw (nChar '0' 2 $ showHex r "")) ['A'..] regs
    regsU = br 1 . bl $ mkRegs True $ map (((case chs of ASCII -> "    "; _ -> ansiFg Blue "─┘  ") ++) . wt .
      nChar ' ' 3 . show) regs
    regsDec = br 1 . bl $ mkRegs False $ map (ansiFg White . ("   " ++) . nChar ' ' 4 . sign) regs
    mkRegs isMid rs = regStart isMid ++ intercalate (regSep isMid) rs ++ regStop
    regStart isMid = case chs of ASCII   -> "| "
                                 _       -> ansiFg Blue $ if isMid then "┠" else "┃"
    regStop        = case chs of ASCII   -> " |"
                                 _       -> ansiFg Blue " ┃"
    regSep = (regStop ++) . (sepDist ++) . regStart
    sepDist = case chs of ASCII -> "  "; _ -> " "
    diodeLine l m r = asciiUni "" . br 6 . bl . yl . ("     " ++) . (l :) . (++ [r]) .
      intercalate [m] $ map (`replicate` '━') [11,6,5,6]
    -- XXX probably split this up according to ASCII/non-ASCII
    diodes = diodeLine '┏' '┯' '┓' ++ (br 6 . bl) (asciiUni "  " (yl "     ┃ ") ++ insertSpace (map applyEnc (nChar '0' 8 $ showIntAtBase 2 ("01" !!) ls "")) ++ asciiUni "   hex: " (yl " │ ") ++ "0x" ++ bw (nChar '0' 2 $ showHex ls "") ++ asciiUni "   udec: " (yl " │ ") ++ wt (nChar ' ' 3 $ show ls) ++ asciiUni "    sdec: " (yl " │ ") ++ wt (nChar ' ' 4 $ sign ls) ++ asciiUni "" (yl " ┃")) ++ diodeLine '┗' '┷' '┛'
    asciiUni sa su = case chs of ASCII -> sa; _ -> su
    bw = ansiAttr Bold . ansiFg White
    yl = ansiFg Yellow
    wt = ansiFg White
    bl = (asciiUni "" (ansiFg Cyan "┃ ") ++)
    br n = (++ asciiUni "\n" (ansiFg Cyan $ replicate n ' ' ++ "┃\n"))
    applyEnc l | l == '0' = case chs of
                 ASCII   -> "O"
                 Unicode -> "○"
                 ANSI    -> ansiFg Black "●"
               | otherwise = case chs of
                 ASCII -> "0"
                 _     -> ansiFg Red "●"
    insertSpace (a:b:c:d:r) = concat $ a:b:c:d:" ":r
    insertSpace xs = concat xs
    line False | isNothing li = ""
    line _ = asciiUni (replicate 50 '_' ++ "\n\n") . ansiFg Cyan $ '┠' : replicate 45 '─' ++ "┨\n"

sign :: Word8 -> String
sign = show . (bool id (subtract 256) =<< (> 127)) .  fromIntegral

nChar :: Char -> Int -> String -> String
nChar c n s = replicate (n - length s) c ++ s

defaultSimulation :: Simulation
defaultSimulation = Simulation
  { _lastIns   = Nothing
  , _leftInss  = []
  , _rightInss = []
  , _cpuSteps  = 0
  , _cpu       = defaultCPU
  }

defaultCPU :: CPU
defaultCPU = CPU
  { _flags     = Flags Unset Unset Unset Unset
  , _registers = Registers 0 0 0 0
  , _output    = 0
  }

runSimulation :: Charset -> String -> IO ()
runSimulation chs file = do
  content <- lines <$> readFile file
  either putStrLn (putStr . run . catMaybes) $ linesToInss content
  where run :: [Instruction] -> String
        run = prettyResults chs . results . (set rightInss ?? defaultSimulation)
        results :: Simulation -> [Result]
        results = (:) <$> newSimResult <*> evalState simulate

main :: IO ()
main = getArgs >>= \case
  [['-', s], file] | Just o <- find ((s ==) . view switch) options -> o^.action $ file
  _ -> putStrLn . usage =<< getProgName

usage :: String -> String
usage progName = "Usage: " ++ progName ++ " -(" ++ switches ++ ") FILE\n" ++ optionDescs
  where
    switches = intersperse '|' $ map (^.switch) options
    optionDescs = unlines $ map ((++) <$> ("  -" ++) . (:": ") . (^.switch) <*> (^.desc)) options

options :: [Option]
options = map (\(a,b,c) -> Option a b c)
   [( 'p', "print both hexadecimal and the original assembly"             , printHexAndOrig
  ),( 'h', "print only hexadecimal"                                       , printHex
  ),( 'l', "print in Logisim ROM format"                                  , printLogisim
  ),( 'r', "simulate the CPU (ASCII output)"                              , runSimulation ASCII
  ),( 'u', "simulate the CPU (Unicode output)"                            , runSimulation Unicode
  ),( 'a', "simulate the CPU (Unicode output using ANSI Escape Sequences)", runSimulation ANSI
  )]
