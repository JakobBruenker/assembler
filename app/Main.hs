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

import Control.Applicative ((<|>))
import Control.Lens
import Control.Monad.State
import Data.Bits
import Data.Bool
import Data.Char
import Data.Either
import Data.List
import Data.Maybe
import Data.Vector (Vector, empty, (!?), fromList)
import Data.Word
import Numeric
import Options
import System.Environment

-- TODO: divide into several modules, and split print and simulate into
-- separate executables
-- TODO: add support for labels

data FlagStatus = Set | Unset deriving (Eq)

newtype RegContent = RegContent {_regContent :: Word8}
  deriving (Eq, Ord, Integral, Real, Enum, Num, Bits)

makeLenses ''RegContent

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

makeLenses ''Registers

data Flags = Flags { _greater :: FlagStatus
                   , _equal   :: FlagStatus
                   , _less    :: FlagStatus
                   , _carry   :: FlagStatus
                   }

makeLenses ''Flags

newtype ConstNum = ConstNum Word8
                   deriving (Enum, Real, Num, Ord, Eq, Integral)

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
                 | Nop
                 | Halt

data NumberedInstruction = NIns { _linenumber :: Int
                                , _instruction :: Instruction
                                }

makeLenses ''NumberedInstruction

data CPU = CPU { _flags     :: Flags
               , _registers :: Registers
               , _output    :: Word8
               }

makeLenses ''CPU

data Simulation = Simulation { _lastIns   :: Maybe NumberedInstruction
                             , _instrs    :: Vector NumberedInstruction
                             , _instrPtr  :: Int
                             , _cpuSteps  :: Integer
                             , _cpu       :: CPU
                             }

makeLenses ''Simulation

data Result = Result { _resultIns   :: Maybe NumberedInstruction
                     , _resultRegs  :: Registers
                     , _leds        :: Word8
                     , _resultFlags :: Flags
                     , _resultSteps :: Integer
                     }

makeLenses ''Result

data TerminationReason = Halted
                       | RanOut
                       | StepsReached

data Outcome = Outcome { _reason  :: TerminationReason
                       , _results :: [Result]
                       }

makeLenses ''Outcome

register :: RegisterID -> Lens' Registers RegContent
register RegA = regA
register RegB = regB
register RegC = regC
register RegD = regD

cpuReg :: RegisterID -> Lens' Simulation RegContent
cpuReg r = cpu.registers.register r

listRegisters :: Registers -> [RegContent]
listRegisters rs = map ((rs&) . view . register) [RegA ..]

flag :: FlagID -> Lens' Flags FlagStatus
flag Greater = greater
flag Equal   = equal
flag Less    = less
flag Carry   = carry

strings2Ins :: [String] -> Either String Instruction
strings2Ins [['c', 't', r], c] | isReg = Right . ConstTo (head reg) =<< readC
  where isReg = not $ null reg
        reg = rights . pure . string2Reg $ pure r
        readC = case c of
          ['0', 'x', a, b] | [(x,"")] <- readHex [a,b] -> Right $ ConstNum x
          (reads -> [(x, "")])
            | x < 256 && x >= -128 -> Right $ ConstNum (fromIntegral x)
            | otherwise            -> Left $ c ++
              " is outside the valid constant range of -128..255"
          _ -> Left $ show c ++ " is not a valid constant"
strings2Ins ["out", reg] = Right . Output =<< string2Reg reg
strings2Ins ['j' : cs, a] | Just j <- jmp = Right . j =<< readA
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
strings2Ins [ins, reg] | ins `elem` ["mov", "cpy"] =
  Right . CopyFromRegA =<< string2Reg reg
strings2Ins [ins, reg] | Just i <- alu = Right . i =<< string2Reg reg
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
        aluLU :: (a -> RegisterID -> Instruction) -> [(String, a)]
              -> Maybe (RegisterID -> Instruction)
        aluLU a as = a <$> lookup ins as
        alu = aluLU Alu1 alu1s <|> aluLU Alu2 alu2s
strings2Ins ["nop"] = Right Nop
strings2Ins ["halt"] = Right Halt
strings2Ins s = Left $ show (unwords s) ++ " is not a valid Instruction"

string2Reg :: String -> Either String RegisterID
string2Reg "a" = Right RegA
string2Reg "b" = Right RegB
string2Reg "c" = Right RegC
string2Reg "d" = Right RegD
string2Reg s = Left $ "No register named " ++ show s

lines2Inss :: [String] -> Either String [Maybe Instruction]
lines2Inss = (fmap . fmap . fmap . fmap) (view instruction) lines2NInss
-- Just look at this beast ^

lines2NInss :: [String] -> Either String [Maybe NumberedInstruction]
lines2NInss = zipWithM (\lnu -> ((fmap . fmap) (NIns lnu)) .
    (traverse (strings2Ins . words) . emptyLine . takeWhile (/= ';'))) [1..]
    where emptyLine l | all isSpace l = Nothing
                      | otherwise     = Just l

ins2Hex :: Bool -> Instruction -> String
ins2Hex binary = (if binary then hexToBin else id) . go
  where
    go (ConstTo r c) = "1" ++ reg2Hex r ++ two0 (showHex (fromIntegral c) "")
    go (Output r) = "1" ++ showHex (fromEnum r + 8) "00"
    go (Jump a) = "20" ++ two0 (showHex (fromIntegral a) "")
    go (JumpIf f a) = "2" ++ flag2Hex f ++ two0 (showHex (fromIntegral a) "")
    go (CopyFromRegA r) = "3" ++ showHex (fromEnum r) "00"
    go (Alu1 i r) = "4" ++ alu1Ins2Hex i ++ "0" ++ reg2Hex r
    go (Alu2 i r) = "8" ++ alu2Ins2Hex i ++ "0" ++ reg2Hex r
    go Nop = "0100"
    go Halt = "0000"

    two0 = nChar '0' 2

    reg2Hex = show . fromEnum

    flag2Hex Greater = "2"
    flag2Hex Equal   = "1"
    flag2Hex Less    = "3"
    flag2Hex Carry   = "8"

    alu1Ins2Hex Negate = "6"
    alu1Ins2Hex Not    = "7"

    alu2Ins2Hex Add        = "0"
    alu2Ins2Hex ShiftLeft  = "1"
    alu2Ins2Hex ShiftRight = "2"
    alu2Ins2Hex And        = "3"
    alu2Ins2Hex Or         = "4"
    alu2Ins2Hex Xor        = "5"

-- Careful: prints out an error if the input isn't actually hex
hexToBin :: String -> String
hexToBin s = case readInt 16 isHexDigit digitToInt s of
  [(n, "")] -> let s' = showIntAtBase 2 intToDigit n ""
               in replicate (4 * length s - length s') '0' ++ s'
  _ -> error $ "Main.hextoBin: tried to read " ++ show s ++ " as a hex number"

appendOriginal :: Bool -> [String] -> [Maybe Instruction] -> [String]
appendOriginal binary ls ms =
  zipWith ((++) . (++ "    ") . fromMaybe "    ") hexs ls
  where hexs = map (fmap (ins2Hex binary)) ms

printAsmAndOrig :: Bool -> String -> IO ()
printAsmAndOrig binary file = do
  content <- lines <$> readFile file
  mapM_ putStrLn . either pure (appendOriginal binary content) $
    lines2Inss content

printAsm :: Bool -> String -> IO ()
printAsm binary file = do
  content <- lines <$> readFile file
  mapM_ putStrLn . either pure (map (ins2Hex binary) . catMaybes) $
    lines2Inss content

printLogisim :: Bool -> String -> IO ()
printLogisim binary file = do
  content <- lines <$> readFile file
  putStrLn . ("v2.0 raw\n" ++) . unlines .
    either pure (map (ins2Hex binary) . catMaybes) $ lines2Inss content

simulate :: Maybe Int -> State Simulation Outcome
simulate msteps =
  if | Just True <- (<1) <$> msteps -> end StepsReached
     | otherwise -> do
       ins <- use instrs
       ind <- use instrPtr
       case ins !? ind of
         Nothing -> end RanOut
         mni@(Just (view instruction -> i)) -> do
           cpuSteps += 1
           instrPtr += 1
           eval i
           lastIns .= mni
           let next = case i of Halt -> end Halted
                                _    -> simulate ((\s -> s - 1) <$> msteps)
           (next <&>) . (results %~) . (:) =<< gets simResult
  where end :: TerminationReason -> State Simulation Outcome
        end = pure . (Outcome ?? [])

putFlag :: FlagID -> FlagStatus -> State Flags ()
putFlag = assign . flag

putFlags :: Ordering -> State Flags ()
putFlags = zipWithM_ putFlag [ Greater, Equal, Less  ] . \case
  GT ->                      [ Set    , Unset, Unset ]
  EQ ->                      [ Unset  , Set  , Unset ]
  LT ->                      [ Unset  , Unset, Set   ]

-- we jump backwards one extra step because we increment before that
jump :: Address -> State Int ()
jump (Address a) = id += sign a - 1

getFlag :: FlagID -> State Simulation FlagStatus
getFlag f = use $ cpu.flags.flag f

eval :: Instruction -> State Simulation ()
eval (ConstTo r (ConstNum x)) = cpuReg r .= RegContent x
eval (Output r)               = (cpu.output .=) =<< use (cpuReg r.regContent)
eval (CopyFromRegA r)         = (cpuReg r .=) =<< use (cpuReg RegA)
eval (Alu1 i r)               = evalAlu1 i r
eval (Alu2 i r)               = evalAlu2 i r
eval (Jump a)     = zoom instrPtr $ jump a
eval (JumpIf f a) = (when ?? zoom instrPtr (jump a)) . (== Set) =<< getFlag f
eval _ = pure ()

evalAlu1 :: Alu1Ins -> RegisterID -> State Simulation ()
evalAlu1 i r = do
  let f = case i of
            Negate -> negate
            Not    -> complement
  res <- f <$> use (cpuReg r)
  cpuReg r .= res
  zoom (cpu.flags) $ do putFlags $ compare res 0
                        putFlag Carry Unset

evalAlu2 :: Alu2Ins -> RegisterID -> State Simulation ()
evalAlu2 i r = do
  a <- use (cpuReg RegA)
  x <- use (cpuReg r)
  let res = f a x
      f = case i of
        Add        -> (+)
        ShiftLeft  -> (. fromIntegral) . shiftL
        ShiftRight -> (. fromIntegral) . shiftR
        And        -> (.&.)
        Or         -> (.|.)
        Xor        -> xor
  cpuReg RegA .= res
  zoom (cpu.flags) $ do putFlags $ compare res 0
                        putFlag Carry . bool Unset Set $
                          fromIntegral a + fromIntegral x > 255
  -- TODO:
  -- Question: should carry flag only be set if the operation is Add?
  -- case i of
  --   Add -> zoom (cpu.flags) . putFlag Carry . bool Unset Set $
  --           fromIntegral a + fromIntegral x > 255
  --   _   -> pure ()

simResult :: Simulation -> Result
simResult ss = Result { _resultIns   = ss^.lastIns
                      , _resultRegs  = ss^.cpu.registers
                      , _leds        = ss^.cpu.output
                      , _resultFlags = ss^.cpu.flags
                      , _resultSteps = ss^.cpuSteps
                      }

prettyNIns :: NumberedInstruction -> String
prettyNIns (NIns ln ins) = (show ln ++ ": ") ++ prettyIns ins

prettyIns :: Instruction -> String
prettyIns (ConstTo r c)    = "ct" ++ prettyReg r ++ " " ++ prettyConst c
prettyIns (Output r)       = "out " ++ prettyReg r
prettyIns (Jump a)         = "jmp " ++ prettyAddress a
prettyIns (JumpIf f a)     = "j" ++ prettyFlagID f ++ " " ++ prettyAddress a
prettyIns (CopyFromRegA r) = "mov " ++ prettyReg r
prettyIns (Alu1 i r)       = prettyAlu1Ins i ++ " " ++ prettyReg r
prettyIns (Alu2 i r)       = prettyAlu2Ins i ++ " " ++ prettyReg r
prettyIns Nop              = "nop"
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
prettyAddress (Address a) = show $ sign a

prettyReg :: RegisterID -> String
prettyReg RegA = "a"
prettyReg RegB = "b"
prettyReg RegC = "c"
prettyReg RegD = "d"

prettyConst :: ConstNum -> String
prettyConst (ConstNum c) =
  "0x" ++ nChar '0' 2 (showHex c " ; ") ++ show c ++ " ; " ++ show (sign c)

prettyResults :: Charset -> Outcome -> String
prettyResults chs (Outcome tr rs) =
  (tblines $ concatMap (prettyResult chs) rs) ++ "\n" ++ termReason ++ "\n"
  where tblines s = lineWith '┏' '┓' ++ s ++ lineWith '┗' '┛'
        lineWith l r = case chs of
          ASCII -> ""
          _     -> ansiForeground chs Cyan $ l : replicate 45 '━' ++ r : "\n"
        termReason = case tr of
          Halted       -> "Program halted."
          RanOut       -> "Ran out of instructions."
          StepsReached -> "Reached maximum number of steps."

ansiAttribute :: Charset -> AnsiAttribute -> String -> String
ansiAttribute chs attr = ansiNumber chs $ fromEnum attr

ansiForeground :: Charset -> AnsiColor -> String -> String
ansiForeground chs col = ansiNumber chs  (30 + fromEnum col)

ansiNumber :: Charset -> Int -> String -> String
ansiNumber = (. show) . ansiCustom

ansiCustom :: Charset -> String -> String -> String
ansiCustom chs fmt s = case chs of
  ANSI -> "\ESC[" ++ fmt ++ "m" ++ s ++ "\ESC[m"
  _    -> s

-- putting 3 different Charsets together makes this a bit clumsy (although
-- I think it definitely makes sense to put Unicode and ANSI together)
prettyResult :: Charset -> Result -> String
prettyResult
  chs (Result li (map (^.regContent) . listRegisters -> regs) ls fs steps) =
  line False ++
  lastI ++
  line True ++
  regLine True ++
  regsHex ++
  regsU ++
  regsDec ++
  regLine False ++
  diodes
  where
    lastI = br 1 . bl $ lastI' ++ spaces dispSteps
    -- using nChar here makes this a bit confusing to be honest
    spaces = (asciiUni "       " "" ++) .
      nChar ' ' (43 - length lastI' + maybe 1 (const 2) li * length (bw ""))
    lastI' = maybe "" (ansiFg Red . ansiAttr Bold . prettyNIns) li
    dispSteps = ansiFg Magenta . ansiAttr Bold $ show steps
    regLine isTop =
      br 1 . bl $ intercalate sepDist (replicate 4 $ oneReg isTop)
    oneReg isTop = case chs of
      ASCII -> "+---------+"
      _     -> ansiFg Blue $ if isTop then "┏━┯━━━━━━┓" else "┗━━━━━━━━┛"
    ansiFg = ansiForeground chs
    ansiAttr = ansiAttribute chs
    regsHex =
      br 1 . bl $ mkRegs False $ zipWith (\c r -> ansiFg Green (pure c) ++
      asciiUni "  " (ansiFg Blue "│ ") ++
      "0x" ++ bw (nChar '0' 2 $ showHex r "")) ['A'..] regs
    regsU = br 1 . bl . mkRegs True $
      map (((case chs of ASCII -> "    "; _ -> ansiFg Blue "─┘  ") ++) . wt .
      nChar ' ' 3 . show) regs
    regsDec = br 1 . bl . mkRegs False $
      map (ansiFg White . ("   " ++) . nChar ' ' 4 . show . sign) regs
    mkRegs isMid rs =
      regStart isMid ++ intercalate (regSep isMid) rs ++ regStop
    regStart isMid = case chs of
      ASCII   -> "| "
      _       -> ansiFg Blue $ if isMid then "┠" else "┃"
    regStop        = case chs of
      ASCII   -> " |"
      _       -> ansiFg Blue " ┃"
    regSep = (regStop ++) . (sepDist ++) . regStart
    sepDist = case chs of ASCII -> "  "; _ -> " "
    diodes = asciiUni diodesASCII diodesUni
      where
        diodesASCII = prettyFlags ++ " " ++ lights ++ "   hex: " ++ hex ++
          "   udec: " ++ udec ++ "   sdec: " ++ sdec ++ "\n"
        diodesUni = diodeLine '┏' '┯' '┓' ++ (br 2 . bl)
          (yl " ┃ " ++ prettyFlags ++ yl " │ " ++ lights ++ yl " │ " ++
          hex ++ yl " │  " ++ udec ++ yl " │ " ++ sdec ++ yl " ┃") ++
          diodeLine '┗' '┷' '┛'
        prettyFlags = case chs of
          ASCII | length flagStates < 4 -> "E E"
                | otherwise -> (case last flagStates of Set -> "C"
                                                        _   -> " ") ++
                               case take 3 flagStates of
                                 [Set,   Unset, Unset] -> " >"
                                 [Unset, Set,   Unset] -> " ="
                                 [Unset, Unset, Set  ] -> " <"
                                 [Set  , Set  , Unset] -> "<="
                                 [Unset, Set  , Set  ] -> ">="
                                 [Unset, Unset, Unset] -> "  "
                                 _                     -> " E"
          _ -> concat $
            zipWith (\f c -> (ansiFg $ case f of
                      Set -> White
                      _   -> Black) [c])
                    flagStates "GELC"
          where flagStates = map ((fs^.) . flag) [Greater ..]
        lights = insertSpace (map applyEnc $
          nChar '0' 8 $ showIntAtBase 2 ("01" !!) ls "")
        hex = "0x" ++ bw (nChar '0' 2 $ showHex ls "")
        udec = wt . nChar ' ' 3 $ show ls
        sdec = wt . nChar ' ' 4 . show $ sign ls
        diodeLine l c r = br 2 . bl . yl . (" " ++) . (l :) .
          (++ [r]) . intercalate [c] $ map (`replicate` '━') [6,11,6,6,6]
        applyEnc l | l == '0' = case chs of
                     ASCII   -> "O"
                     Unicode -> "○"
                     ANSI    -> ansiFg Black "●"
                   | otherwise = case chs of
                     ASCII -> "0"
                     _     -> ansiFg Red "●"
    asciiUni sa su = case chs of ASCII -> sa; _ -> su
    bw = ansiAttr Bold . ansiFg White
    yl = ansiFg Yellow
    wt = ansiFg White
    bl = (asciiUni "" (ansiFg Cyan "┃ ") ++)
    br n = (++ asciiUni "\n" (ansiFg Cyan $ replicate n ' ' ++ "┃\n"))
    insertSpace (a:b:c:d:r) = concat $ a:b:c:d:" ":r
    insertSpace xs = concat xs
    line b | b            = ln '┠' '─' '┨'
           | isNothing li = ""
           | otherwise    = ln '┣' '━' '┫'
      where
        ln l c r = asciiUni lineASCII (lineUni l c r)
        lineASCII | b = replicate 50 '-' ++ "\n\n"
                  | otherwise = '\n' : replicate 50 '=' ++ "\n"
        lineUni l c r = ansiFg Cyan $ l : replicate 45 c ++ r : "\n"

sign :: Word8 -> Int
sign = (bool id (subtract 256) =<< (> 127)) . fromIntegral

nChar :: Char -> Int -> String -> String
nChar c n s = replicate (n - length s) c ++ s

defaultSimulation :: Simulation
defaultSimulation = Simulation
  { _lastIns   = Nothing
  , _instrs    = empty
  , _instrPtr  = 0
  , _cpuSteps  = 0
  , _cpu       = defaultCPU
  }

defaultCPU :: CPU
defaultCPU = CPU
  { _flags     = Flags Unset Unset Unset Unset
  , _registers = Registers 0 0 0 0
  , _output    = 0
  }

runSimulation :: Maybe Int -> Charset -> String -> IO ()
runSimulation msteps chs file = do
  content <- lines <$> readFile file
  either putStrLn (putStr . run . catMaybes) $ lines2NInss content
  where
    run :: [NumberedInstruction] -> String
    run is = prettyResults chs . outcome . (set instrs ?? defaultSimulation) $
      fromList is
    outcome :: Simulation -> Outcome
    outcome =
      (&) . evalState (simulate msteps) <*> (results %~) . (:) . simResult

boolOption :: String -> Char -> String -> DefineOptions Bool
boolOption long short desc = defineOption optionType_bool (\o -> o
  { optionLongFlags   = [long]
  , optionShortFlags  = [short]
  , optionDescription = desc
  , optionDefault     = False
  })

data MainOptions = MainOptions

instance Options MainOptions where
  defineOptions = pure MainOptions

data PrintOptions = PrintOptions
  { optLogisim  :: Bool
  , optAssembly :: Bool
  , optBinary :: Bool
  }

instance Options PrintOptions where
  defineOptions = pure PrintOptions
    <*> boolOption "logisim" 'l'
        "Whether to print out in Logisim ROM format"
    <*> boolOption "assembly" 'a'
        "Whether to print out the assembly code, when --logisim is off"
    <*> boolOption "binary" 'b'
        "Whether to print in binary, when --logisim is off"

data SimulateOptions = SimulateOptions
  { optUnicode :: Bool
  , optColor   :: Bool
  , optSteps   :: Maybe Int
  }

instance Options SimulateOptions where
  defineOptions = pure SimulateOptions
    <*> boolOption "unicode" 'u'
        "Whether to use unicode"
    <*> boolOption "color" 'c'
        "Whether to use ANSI color escape sequences, when --unicode is on"
    <*> defineOption (optionType_maybe optionType_int) (\o -> o
          { optionLongFlags   = ["steps"]
          , optionShortFlags  = ['s']
          , optionDescription = "Maximum number of simulated steps"
          , optionDefault     = Nothing
          })

checkFilename :: (String -> IO ()) -> [String] -> IO ()
checkFilename f [filename] = f filename
checkFilename _ _ = putStrLn . usage =<< getProgName

runPrint :: MainOptions -> PrintOptions -> [String] -> IO ()
runPrint _ opts args = checkFilename go args
  where go | optLogisim  opts = printLogisim binary
           | optAssembly opts = printAsmAndOrig binary
           | otherwise        = printAsm binary
        binary = optBinary opts

runSimulate :: MainOptions -> SimulateOptions -> [String] -> IO ()
runSimulate _ opts args = checkFilename go args
  where go | optUnicode opts, optColor opts = runSim ANSI
           | optUnicode opts                = runSim Unicode
           | otherwise                      = runSim ASCII
        runSim = runSimulation $ optSteps opts

main :: IO ()
main = runSubcommand
  [ subcommand "print" runPrint
  , subcommand "simulate" runSimulate
  ]

usage :: String -> String
usage progName =
  "Usage: " ++ progName ++ " {print|simulate} [<OPTIONS>] <FILE>\n" ++
  "For available options, see\n" ++ progName ++ " {print|simulate} --help"
