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
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveTraversable          #-}

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
import qualified Data.HashMap.Strict as M
import Data.Vector (Vector, empty, (!?), fromList)
import Data.Word
import Numeric
import Options
import System.Environment

-- TODO: divide into several modules, and split print and simulate into
-- separate executables
-- TODO: add instructions to negate flags
-- TODO: maybe add jge, jle, and jnz, to be translated into negating flags and
-- the opposite jump

data FlagStatus = Set | Unset deriving (Show, Eq)

newtype RegContent = RegContent {_regContent :: Word8}
  deriving (Show, Eq, Ord, Integral, Real, Enum, Num, Bits)

makeLenses ''RegContent

data AnsiAttribute = Off | Bold | Underline | Undefined | Italic | BlinkSlow
                   | BlinkRapid | Reverse | Conceal
                   deriving (Show, Enum)

data AnsiColor = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White
               deriving (Show, Enum)

data Charset = ASCII | Unicode | ANSI deriving Show

data FlagID = Greater | Equal | Less | Carry deriving (Show, Enum, Eq, Ord)

data Registers = Registers { _regA :: RegContent
                           , _regB :: RegContent
                           , _regC :: RegContent
                           , _regD :: RegContent
                           } deriving Show

makeLenses ''Registers

data Flags = Flags { _greater :: FlagStatus
                   , _equal   :: FlagStatus
                   , _less    :: FlagStatus
                   , _carry   :: FlagStatus
                   } deriving Show

makeLenses ''Flags

newtype ConstNum = ConstNum Word8
                   deriving (Show, Enum, Real, Num, Ord, Eq, Integral)

data RegisterID = RegA | RegB | RegC | RegD deriving (Show, Enum)

newtype Address = Address Word8
                deriving (Show, Enum, Real, Num, Ord, Eq, Integral)

data Alu1Ins = Negate | Not deriving Show

data Alu2Ins = Add | ShiftLeft | ShiftRight | And | Or | Xor deriving Show

data Instruction = ConstTo RegisterID ConstNum
                 | Output RegisterID
                 | Jump Address (Maybe String)
                 | JumpIf FlagID Address (Maybe String)
                 | CopyFromRegA RegisterID
                 | Alu1 Alu1Ins RegisterID
                 | Alu2 Alu2Ins RegisterID
                 | Nop
                 | Halt
                 deriving Show

data Numbered a = Numbered { _linenumber :: Int
                           , _line :: a
                           } deriving (Show, Functor, Foldable, Traversable)

makeLenses ''Numbered

data CPU = CPU { _flags     :: Flags
               , _registers :: Registers
               , _output    :: Word8
               } deriving Show

makeLenses ''CPU

data Simulation = Simulation { _lastIns   :: Maybe (Numbered Instruction)
                             , _instrs    :: Vector (Numbered Instruction)
                             , _instrPtr  :: Int
                             , _cpuSteps  :: Integer
                             , _cpu       :: CPU
                             } deriving Show

makeLenses ''Simulation

data Result = Result { _resultIns   :: Maybe (Numbered Instruction)
                     , _resultRegs  :: Registers
                     , _leds        :: Word8
                     , _resultFlags :: Flags
                     , _resultSteps :: Integer
                     } deriving Show

makeLenses ''Result

data TerminationReason = Halted
                       | RanOut
                       | StepsReached
                       deriving Show

data Outcome = Outcome { _reason  :: TerminationReason
                       , _results :: [Result]
                       } deriving Show

type Labels = M.HashMap String Int

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

mkError :: Int -> String -> Either String a
mkError ln str = Left $ "Error in Line " ++ show ln ++ ": " ++ str

strings2Ins :: Labels -> (Int, Numbered [String])
            -> Either String (Numbered Instruction)
strings2Ins _ (_, Numbered l [['c', 't', r], c]) | not $ null reg =
  Numbered l <$> (Right . ConstTo (head reg) =<< readC)
  where reg = rights . pure . string2Reg l $ pure r
        readC = case c of
          ['0', 'x', a, b] | [(x,"")] <- readHex [a,b] -> Right $ ConstNum x
          (reads -> [(x, "")])
            | x < 256 && x >= -128 -> Right $ ConstNum (fromIntegral x)
            | otherwise            -> mkError l $ c ++
              " is outside the valid constant range of -128..255"
          _ -> mkError l $ show c ++ " is not a valid constant"
strings2Ins _ (_, Numbered l ["out", reg]) = Numbered l <$>
  (Right . Output =<< string2Reg l reg)
strings2Ins labels (i, Numbered l ['j' : cs, a]) | Just j <- jmp =
  Numbered l <$> (Right . uncurry j =<< readA)
  where jmp | cs == "mp" = Just Jump
            | otherwise  = lookup cs jumpIfs
        jumpIfs = [ ("e", JumpIf Equal)
                  , ("z", JumpIf Equal)
                  , ("g", JumpIf Greater)
                  , ("l", JumpIf Less)
                  , ("c", JumpIf Carry)
                  ]
        readA :: Either String (Address, Maybe String)
        readA = case reads a of
          [(x, "")] -> toAddr x Nothing
          _ | Just addr <- M.lookup a labels ->
              -- Right . Address . fromIntegral $ addr - i
              toAddr (addr - i) $ Just a
          _ -> mkError l $ show a ++ " is not a valid address or label"
        toAddr :: Int -> Maybe String -> Either String (Address, Maybe String)
        toAddr addr ms
          | addr < 128 && addr >= -128 =
            Right $ (Address (fromIntegral addr), ms)
          | otherwise = mkError l $ fromMaybe (show addr) ms ++
            " is outside the valid address range of -128..127"
strings2Ins _ (_, Numbered l [ins, reg]) | ins `elem` ["mov", "cpy"] =
  Numbered l <$> (Right . CopyFromRegA =<< string2Reg l reg)
strings2Ins _ (_, Numbered l [ins, reg]) | Just i <- alu =
  Numbered l <$> (Right . i =<< string2Reg l reg)
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
strings2Ins _ (_, Numbered l ["nop"]) = Numbered l <$> Right Nop
strings2Ins _ (_, Numbered l ["halt"]) = Numbered l <$> Right Halt
strings2Ins _ (_, Numbered l s) =
  mkError l $ show (unwords s) ++ " is not a valid instruction"

string2Reg :: Int -> String -> Either String RegisterID
string2Reg _ "a" = Right RegA
string2Reg _ "b" = Right RegB
string2Reg _ "c" = Right RegC
string2Reg _ "d" = Right RegD
string2Reg l s = mkError l $ "No register named " ++ show s

getIns :: [String] -> Either String [Instruction]
getIns = (fmap (^.line) <$>) . getNumIns

getNumIns :: [String] -> Either String [Numbered Instruction]
getNumIns ss = getInsLines ss >>=
  (\(labels, ns) -> traverse (strings2Ins labels . fmap (words <$>)) ns)

-- returns lines that actually contain instruction along with the line number
getInsLines :: [String] -> Either String (Labels, [(Int, Numbered String)])
getInsLines ss = (,fmap (uncurry Numbered) <$> ins) <$>
  assignLbls lbls ins M.empty
  where
    (lbls, ins) = bimap (fmap init <$>) (zip [0..]) .
      distribute (isLabel . snd) .
      filter (not . null . snd) .
      (fmap (strip . takeWhile (/= ';')) <$>) $
      zip [1..] ss

    maxI = succ . maximum $ map fst ins

    assignLbls :: [(Int, String)] -> [(Int, (Int, String))] -> Labels
           -> Either String Labels
    assignLbls lbl@((n, l):ls) is@((x, (m, _)):is'@((y, (o, _)):_)) lblm
      | n < m = assignLbls ls is =<< insertLabel n l x lblm
      | m < n, n <= o = assignLbls ls is =<< insertLabel n l y lblm
      | otherwise = assignLbls lbl is' lblm
    assignLbls lbl@((n, l):ls) is@[(x, (o, _))] lblm
      | n <= o = assignLbls ls is =<< insertLabel n l x lblm
      | otherwise = assignLbls lbl [] lblm
    assignLbls ((n, l):ls) [] lblm =
      assignLbls ls [] =<< insertLabel n l maxI lblm
    assignLbls [] _ lblm = Right lblm

    insertLabel :: Int -> String -> Int -> Labels -> Either String Labels
    insertLabel n lbl x lblm
      | lbl `M.member` lblm = mkError n $ "Duplicate label " ++ show lbl
      | otherwise = Right $ M.insert lbl x lblm

    strip = let f = dropWhile isSpace . reverse in f . f
    isLabel (x:xs) -- this is what I get for not using a parsing library
      | isAlpha x, all isAlphaNum $ init xs, last xs == ':' = True
    isLabel _ = False

distribute :: (a -> Bool) -> [a] -> ([a], [a])
distribute p l = bimap reverse reverse $ go l [] []
  where go [] ts fs = (ts, fs)
        go (x:xs) ts fs | p x       = go xs (x:ts) fs
                        | otherwise = go xs ts (x:fs)

ins2Hex :: Bool -> Instruction -> String
ins2Hex binary = (if binary then unsafeHexToBin else id) . go
  where
    go (ConstTo r c) = "1" ++ reg2Hex r ++ two0 (showHex (fromIntegral c) "")
    go (Output r) = "1" ++ showHex (fromEnum r + 8) "00"
    go (Jump a _) = "20" ++ two0 (showHex (fromIntegral a) "")
    go (JumpIf f a _) =
      "2" ++ flag2Hex f ++ two0 (showHex (fromIntegral a) "")
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

unsafeHexToBin :: String -> String
unsafeHexToBin =
  intercalate " " . map ((sequence (replicate 4 "01") !!) . digitToInt)

lineNumber :: Bool -> Int -> Numbered a -> String
lineNumber numbers maxline (Numbered n _) | numbers   = nu ++ ": "
                                          | otherwise = ""
  where str = show n
        nu = replicate (length (show maxline) - length str) ' ' ++ str

appendOriginal :: Bool -> Bool -> Int -> [String] -> [Numbered Instruction]
               -> [String]
appendOriginal numbers binary maxline ls is =
  zipWith (\nb ->
           ((lineNumber numbers maxline nb ++ nb^.line ++ "    ") ++)) hexs ls
  where hexs :: [Numbered String]
        hexs = fill $ fmap (ins2Hex binary) <$> is
        fill :: [Numbered String] -> [Numbered String]
        fill ns@(Numbered n _ : _) =
          map (flip Numbered filler) [1..n-1] ++ go ns
        fill ns = ns
        go :: [Numbered String] -> [Numbered String]
        go (Numbered n@(succ -> n') i : rest@(Numbered m _ : _))
          | n' < m    = Numbered n i : go (Numbered n' filler : rest)
          | otherwise = Numbered n i : go rest
        go [nb@(Numbered n _)] =
          nb : map (flip Numbered filler) [succ n..maxline]
        go [] = []
        filler = replicate (if binary then 19 else 4) ' '

printAsmAndOrig :: Bool -> Bool -> String -> IO ()
printAsmAndOrig numbers binary file = do
  content <- lines <$> readFile file
  mapM_ putStrLn .
    either pure (appendOriginal numbers binary (length content) content) $
    getNumIns content

printAsm :: Bool -> Bool -> String -> IO ()
printAsm numbers binary file = do
  content <- lines <$> readFile file
  mapM_ putStrLn . either pure
    ((((++) . lineNumber numbers (length content)) <*> view line <$>) .
      (fmap (ins2Hex binary) <$>)) $
    getNumIns content

printLogisim :: Bool -> String -> IO ()
printLogisim binary file = do
  content <- lines <$> readFile file
  mapM_ putStrLn . ("v2.0 raw" :) .
    either pure (ins2Hex binary <$>) $ getIns content

simulate :: Maybe Int -> State Simulation Outcome
simulate msteps =
  if | Just True <- (<1) <$> msteps -> end StepsReached
     | otherwise -> do
       ins <- use instrs
       ind <- use instrPtr
       case ins !? ind of
         Nothing -> end RanOut
         mni@(Just (view line -> i)) -> do
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
eval (Jump a _)               = zoom instrPtr $ jump a
eval (JumpIf f a _)
  = (when ?? zoom instrPtr (jump a)) . (== Set) =<< getFlag f
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

prettyNIns :: (Numbered Instruction) -> String
prettyNIns (Numbered ln ins) = (show ln ++ ": ") ++ prettyIns ins

prettyIns :: Instruction -> String
prettyIns (ConstTo r c)    = "ct" ++ prettyReg r ++ " " ++ prettyConst c
prettyIns (Output r)       = "out " ++ prettyReg r
prettyIns (CopyFromRegA r) = "mov " ++ prettyReg r
prettyIns (Alu1 i r)       = prettyAlu1Ins i ++ " " ++ prettyReg r
prettyIns (Alu2 i r)       = prettyAlu2Ins i ++ " " ++ prettyReg r
prettyIns Nop              = "nop"
prettyIns Halt             = "halt"
prettyIns (Jump a l)       = "jmp " ++ prettyAddress a ++ prettyLabel l
prettyIns (JumpIf f a l)   =
  "j" ++ prettyFlagID f ++ " " ++ prettyAddress a ++ prettyLabel l

prettyLabel :: Maybe String -> String
prettyLabel (Just l) = "; " ++ l
prettyLabel Nothing = ""

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
  hline False ++
  lastI ++
  hline True ++
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
          Unicode -> zipWith (\f c -> case f of
                               Set -> c
                               _   -> ' ') flagStates letters
          ANSI -> concat $
            zipWith (\f c -> (ansiFg $ case f of
                      Set -> White
                      _   -> Black) [c])
                    flagStates letters
          where flagStates = map ((fs^.) . flag) [Greater ..]
                letters = "GELC"
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
    hline b | b            = ln '┠' '─' '┨'
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
  either putStrLn (putStr . run) $ getNumIns content
  where
    run :: [Numbered Instruction] -> String
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
  , optNumbers :: Bool
  }

instance Options PrintOptions where
  defineOptions = pure PrintOptions
    <*> boolOption "logisim" 'l'
        "Whether to print out in Logisim ROM format"
    <*> boolOption "assembly" 'a'
        "Whether to print out the assembly code, when --logisim is off"
    <*> boolOption "binary" 'b'
        "Whether to print in binary, when --logisim is off"
    <*> boolOption "numbers" 'n'
        "Whether to print out line numbers, when --logisim is off"

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
           | optAssembly opts = printAsmAndOrig numbers binary
           | otherwise        = printAsm numbers binary
        binary = optBinary opts
        numbers = optNumbers opts

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
