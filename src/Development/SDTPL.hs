{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

{-|
Module      : Development.SDTPL
Description : String Decision Tree Processing Language
Copyright   : (c) 2015 Peter Amidon <psa.pub.0@picnicpark.org>
License     : Apache-2

This module provides a compiler for a DSL that is intended for
following complex decision trees when converting a set of input
strings and booleans to a set of outputs; it also contains a method of
generating control flow graphs from these programs, in order to aid
debugging.

-}

module Development.SDTPL (compileSDTPL, graphSDTPL) where

import Text.Parsec
import qualified Data.Map as M
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import qualified Language.Haskell.TH.Syntax (lift)
import Data.List
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Graph.Inductive
import Data.GraphViz hiding (parse)
import qualified Data.Text.Lazy as T

-- Prevent name collisions with lift from Control.Monad.Trans
liftQ :: Lift t => t -> ExpQ
liftQ = Language.Haskell.TH.Syntax.lift

data VarType = String | Bool deriving (Eq, Show)
data Var = Var VarType String deriving (Eq, Show)
data VarRef = VarRef String deriving (Eq, Show)

type VarList = [Var]

type Address = String
data Val = LitVal String | VarVal VarRef | UnknownVal deriving (Eq, Show)
data Instruction = BLANKP VarRef | EQP VarRef VarRef | TRUEP VarRef | RET [Val] deriving (Eq, Show)

data Procedure = Procedure { initAddr :: Address
                           , instrs :: M.Map Address Instruction } deriving (Eq, Show)

data Operation = Take VarList | Make VarList | Proc Procedure deriving (Eq, Show)

isTake (Take _) = True
isTake _ = False
isMake (Make _) = True
isMake _ = False
isProc (Proc _) = True
isProc _ = False

-- Real spaces parser: the spaces parser from Parsec accepts all kinds
-- of other things, like newlines, but this behavior is sometimes
-- undesirable.
rspaces :: Stream s m Char => ParsecT s u m ()
rspaces = skipMany (char ' ')

ident :: Stream s m Char => (String -> x) -> ParsecT s u m x
ident t = t <$> many1 alphaNum

varDec :: Stream s m Char => ParsecT s u m VarList
varDec = stringVarD <|> boolVarD
  where stringVarD = string "S:" *> rspaces *> sepBy (var String) rspaces
        boolVarD = string "B:" *> rspaces *> sepBy (var Bool) rspaces
        var = ident . Var


varDecList :: Stream s m Char => ParsecT s u m VarList
varDecList = concat <$> sepBy varDec (rspaces *> char ',' *> rspaces)

takeP :: Stream s m Char => ParsecT s u m Operation
takeP = Take <$> (string "TAKE" *> rspaces *> varDecList)

makeP :: Stream s m Char => ParsecT s u m Operation
makeP = Make <$> (string "MAKE" *> rspaces *> varDecList)

instParser :: Stream s m Char => ParsecT s u m (Address, Instruction)
instParser = (,) <$> address <* rspaces <*> instruction
  where address :: Stream s m Char => ParsecT s u m Address
        address = manyTill alphaNum (char ':')
        instruction :: Stream s m Char => ParsecT s u m Instruction
        instruction = blankP <|> eqP <|> trueP <|> retP
        blankP :: Stream s m Char => ParsecT s u m Instruction
        blankP = string "BLANKP" *> (BLANKP <$> vr)
        eqP :: Stream s m Char => ParsecT s u m Instruction
        eqP = string "EQP" *> (EQP <$> vr <*> vr)
        trueP :: Stream s m Char => ParsecT s u m Instruction
        trueP = string "TRUEP" *> (TRUEP <$> vr)
        retP :: Stream s m Char => ParsecT s u m Instruction
        retP = string "RET" *> (RET <$> (rspaces *> sepBy exp rspaces))
        vr :: Stream s m Char => ParsecT s u m VarRef
        vr = rspaces *> ident VarRef
        exp :: Stream s m Char => ParsecT s u m Val
        exp = litValVal <|> unknownVal <|> (VarVal <$> vr)
        litValVal :: Stream s m Char => ParsecT s u m Val
        litValVal = LitVal <$> (char '"' *> many (noneOf "\"") <* char '"')
        unknownVal :: Stream s m Char => ParsecT s u m Val
        unknownVal = string "UNKNOWN" *> pure UnknownVal

procP :: Stream s m Char => ParsecT s u m Operation
procP = string "PROC" *> spaces *> (Proc <$> (Procedure <$> addr <*> instrs))
  where addr :: Stream s m Char => ParsecT s u m Address
        addr = ident id <* spaces
        instrs :: Stream s m Char => ParsecT s u m (M.Map Address Instruction)
        instrs = M.fromList <$> manyTill (instParser <* spaces) (string "END")

progP :: Stream s m Char => ParsecT s u m [Operation]
progP = endBy (takeP <|> makeP <|> procP) newline

-- | Create a function named by a string which performs the processing
-- described in the specified file.
compileSDTPL :: String -> FilePath -> Q [Dec]
compileSDTPL n f = do
  p <- parse progP f <$> runIO (readFile f)
  let prog = either (const $ fail "Unparseable input") id p
  (Take vars) <- maybe (fail "No TAKE statement") return $ find isTake prog
  body <- generateBody prog
  let varNames = map varName vars
  return [FunD (mkName n) [Clause (map (VarP . mkName) varNames)
                                  (NormalB body)
                                  []]]
  where varName :: Var -> String
        varName (Var _ x) = x

generateBody :: [Operation] -> Q Exp
generateBody prog = do
    (Take takeVars) <- maybe (fail "No TAKE statement") return $ find isTake prog
    let varTypes = M.fromList $ map varEntry takeVars
          where varEntry (Var t n) = (n, t)
    p <- maybe (fail "No PROC statement") return $ find isProc prog
    generateTree p varTypes
  where generateTree :: Operation -> M.Map String VarType -> ExpQ
        generateTree (Proc (Procedure{..})) = generateInstr initAddr instrs
        generateInstr :: Address -> M.Map Address Instruction -> M.Map String VarType -> ExpQ
        generateInstr i m varTypes = do
          instr <- maybe (fail $ "Missing instruction " ++ i) return $
                         M.lookup i m
          case instr of
            (BLANKP var) -> tyCheck var String >> genBP var
            (EQP var1 var2) -> genEP var1 var2
            (TRUEP var) -> tyCheck var Bool >> genTP var
            (RET vals) -> genR vals
          where lookupVarTy :: String -> Q VarType
                lookupVarTy var = maybe (fail $ "Undefined var: " ++ var)
                                        return $ M.lookup var varTypes
                tyCheck :: VarRef -> VarType -> Q ()
                tyCheck (VarRef var) ty = do
                  varTy <- lookupVarTy var
                  unless (ty == varTy) $
                    fail $ "Wrongly-typed usage of var " ++ var
                genBP :: VarRef -> ExpQ
                genBP (VarRef var) = [|maybe $trueInstr
                                             (\x -> if x == ""
                                                       then $trueInstr
                                                       else $falseInstr)
                                             $(varE $ mkName var) |]
                genEP :: VarRef -> VarRef -> ExpQ
                genEP (VarRef var1) (VarRef var2) = do
                  var1Ty <- lookupVarTy var1
                  var2Ty <- lookupVarTy var2
                  unless (var1Ty == var2Ty) $
                         fail $ "Wrongly-typed comparison between var '"
                              ++ var1 ++ "' and var '" ++ var2 ++ "'"
                  [|if $v1 == $v2
                       then $trueInstr
                       else $falseInstr|]
                  where v1 = varE $ mkName var1
                        v2 = varE $ mkName var2
                genTP (VarRef var) = [|maybe $falseInstr
                                             (\x -> if x
                                                       then $trueInstr
                                                       else $falseInstr)
                                             $(varE $ mkName var)|]
                falseInstr = generateInstr (i ++ "0") m varTypes
                trueInstr = generateInstr (i ++ "1") m varTypes
                genR :: [Val] -> ExpQ
                genR vals = do
                  (Make makeVars) <- maybe (fail "No MAKE statement") return $
                                       find isMake prog
                  unless (length vals == length makeVars) $
                    fail "Error: wrong number of args to RET"
                  t <- zipWithM toExp vals $ makeTypes makeVars
                  return $ TupE t
                  where toExp :: Val -> VarType -> ExpQ
                        toExp (LitVal s) String = [|Just $(liftQ s)|]
                        toExp (LitVal s) Bool = [|Just $(liftQ (read s :: Bool))|]
                        toExp (VarVal v@(VarRef n)) t = tyCheck v t
                                                        >> varE (mkName n)
                        toExp UnknownVal String = liftQ (Nothing :: Maybe String)
                        toExp UnknownVal Bool = liftQ (Nothing :: Maybe Bool)
                        makeTypes :: [Var] -> [VarType]
                        makeTypes = map (\(Var t _) -> t)

-- | Create a dot file for a control flow graph of the SDTPL program
-- in the specified file.
graphSDTPL :: FilePath -> MaybeT IO String
graphSDTPL f = do
  p <- parse progP f <$> liftIO (readFile f)
  prog <- either (const mzero) return p
  (Proc x) <- MaybeT . return $ find isProc prog
  (Make makeVars) <- MaybeT . return$ find isMake prog
  T.unpack <$> (MaybeT . return $ genGraph x makeVars)

genGraph :: Procedure -> VarList -> Maybe T.Text
genGraph Procedure{..} v = do
  graphRep <- addInstructionGraph initAddr instrs v
  -- This extra variable is needed because without it GHC thinks that
  -- the Gr instance is ambiguous
  let graph :: Gr (String, Shape) String
      graph = uncurry mkGraph graphRep
  return . printDotGraph $ graphToDot params graph
  where fmtNode (_, (l, s)) = [toLabel l, shape s]
        fmtEdge (_, _, l) = [toLabel l]
        params = nonClusteredParams { fmtNode = fmtNode, fmtEdge = fmtEdge }

addInstructionGraph :: Address -> M.Map Address Instruction -> VarList -> Maybe ([LNode (String, Shape)], [LEdge String])
addInstructionGraph i m v = do (_, n, e) <- addInstructionGraph' 0  i m v
                               return (n, e)

-- The first Int is the maximum node number used so far; it is used to
-- ensure that node labels are monotonically increasing, and therefore
-- unique.  The new maximum node number after an invocation of this
-- function is returned as the first element of the result tuple; this
-- is also the node number of the top of the tree.
addInstructionGraph' :: Int -> Address -> M.Map Address Instruction -> VarList -> Maybe (Int, [LNode (String, Shape)], [LEdge String])
addInstructionGraph' n i m v = do
  instr <- M.lookup i m
  case instr of
    (BLANKP var) -> genBP var
    (EQP var1 var2) -> genEP var1 var2
    (TRUEP var) -> genTP var
    (RET vals) -> genR vals
  where genxP label = do
          (n1, p1, e1) <- addInstructionGraph' n (i ++ "0") m v
          (n2, p2, e2) <- addInstructionGraph' n1 (i ++ "1") m v
          let point = (n2 + 1, (label, Ellipse))
              noEdge = (n2 + 1, n1, "no")
              yesEdge = (n2 + 1, n2, "yes")
          return (n2 + 1, point:p1 ++ p2, noEdge:yesEdge:e1 ++ e2)
        genBP (VarRef var) = genxP ('\'':var++ "' field blank?")
        genEP (VarRef var1) (VarRef var2) =
          genxP ('\'':var1++ "'=='"++var2++ "'?")
        genTP (VarRef var) = genxP ("Is '"++var++"' true?")
        genR vals = Just (n + 1, [point], [])
          where label = concat $ zipWith (\x y -> x ++ "=" ++ y ++ "\n")
                                         (map (\(Var _ n) -> n) v)
                                         (map renderVal vals)
                point = (n + 1, (label, BoxShape))
                renderVal (LitVal s) = s
                renderVal (VarVal (VarRef n)) = n
                renderVal UnknownVal = "Unknown"
