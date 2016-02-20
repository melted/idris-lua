module IRTS.CodegenLua(codegenLua) where

import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Simplified
import Idris.Core.TT as TT

import Data.Maybe
import Data.Char

import qualified Data.Text as T

import Language.Lua.PrettyPrinter
import Language.Lua as L

-- import Text.PrettyPrint.Leijen

codegenLua :: CodeGenerator
codegenLua ci = do let out = Block (map doCodegen (simpleDecls ci) ++ [start]) Nothing
                   let decls = Block (map getFunName (simpleDecls ci)) Nothing
                   let src = decls `concatBlock` out
                   let code = displayS (renderPretty 0.4 80 (pprint src)) ""
                   putStrLn code
                   writeFile (outputFile ci) code

start = funcall (luaName (sMN 0 "runMain")) []

variable s = PrefixExp $ PEVar $ VarName s
pfuncall f a = PrefixExp $ PEFunCall $ NormalFunCall (PEVar (VarName f)) (Args a)
funcall f a = FunCall $ NormalFunCall (PEVar (VarName f)) (Args a)
table t n = PrefixExp $ PEVar $ Select (PEVar (VarName t)) n
number n = Number $ show n

luaName :: TT.Name -> String
luaName n = "idris_" ++ concatMap alphanum (showCG n)
  where alphanum x | isAlpha x || isDigit x = [x]
                   | otherwise = "_" ++ show (fromEnum x) ++ "_"

var :: TT.Name -> String
var (UN s) = T.unpack s

loc :: Int -> String
loc i = "loc" ++ show i

getFunName :: (TT.Name, SDecl) -> Stat
getFunName (n, _) = LocalAssign [luaName n] Nothing

doCodegen :: (TT.Name, SDecl) -> Stat
doCodegen (n, SFun _ args i def) = cgFun n args def

cgFun :: TT.Name -> [TT.Name] -> SExp -> Stat
cgFun n args def =
    FunAssign (FunName (luaName n) [] Nothing) (FunBody (map (loc . fst) (zip [0..] args)) False
        (cgBody doRet def))
            where
                doRet bs e = Block bs (Just [e])
--    = "function " ++ luaName n ++ "("
--                  ++ showSep "," (map (loc . fst) (zip [0..] args)) ++ ") {\n"
--                  ++ cgBody doRet def ++ "\n}\n\n"
--  where doRet :: String -> String -- Return the calculated expression
--        doRet str = "return " ++ str ++ ";"

-- cgBody converts the SExp into a chunk of php which calculates the result
-- of an expression, then runs the function on the resulting bit of code.
--
-- We do it this way because we might calculate an expression in a deeply nested
-- case statement, or inside a let, etc, so the assignment/return of the calculated
-- expression itself may happen quite deeply.
concatBlock :: Block -> Block -> Block
concatBlock (Block b1 _) (Block b2 r) = Block (b1 ++ b2) r

cgBody :: ([Stat] -> Exp -> Block) -> SExp -> Block
cgBody ret (SV (Glob n)) = ret [] $ variable (luaName n)
cgBody ret (SV (Loc i)) = ret [] $ variable (loc i)
cgBody ret (SApp _ f args) = ret [] $ pfuncall (luaName f)
                        (map (variable . cgVar) args)

cgBody ret (SLet (Loc i) v sc)
   = concatBlock
        (cgBody (\x y -> Block (x ++ [Assign [VarName $ loc i] [y]]) Nothing) v)
        (cgBody ret sc)
cgBody ret (SUpdate n e)
   = cgBody ret e
cgBody ret (SProj e i)
   = ret [] $ PrefixExp $ PEVar (Select (PEVar (VarName $ cgVar e)) (Number $ show (i + 1)))
cgBody ret (SCon _ t n args)
   = ret [] $ TableConst ((Field $ Number (show t)):(map (Field . variable . cgVar) args))
cgBody ret (SCase _ e alts)
   = let scrvar = cgVar e
         scr = if any conCase alts then table scrvar (Number "1") else variable scrvar in
         Block [If (map (cgAlt ret scrvar scr) alts) Nothing] Nothing
  where conCase (SConCase _ _ _ _ _) = True
        conCase _ = False
cgBody ret (SChkCase e alts)
   = let scrvar = cgVar e
         scr = if any conCase alts then table scrvar (Number "1") else variable scrvar in
            Block [If (map (cgAlt ret scrvar scr) alts) Nothing] Nothing
  where conCase (SConCase _ _ _ _ _) = True
        conCase _ = False
cgBody ret (SConst c) = ret [] $ cgConst c
cgBody ret (SOp op args) = ret [] $ cgOp op (map (variable . cgVar) args)
cgBody ret SNothing = ret [] $ Nil
cgBody ret (SError x) = ret [] $ String $ "error( " ++ show x ++ ")"
cgBody ret _ = ret [] $ String $ "error(\"NOT IMPLEMENTED!!!!\")"

cgAlt :: ([Stat] -> Exp -> Block) -> String -> Exp -> SAlt -> (Exp, Block)
cgAlt ret scr test (SConstCase t exp)
   = (Binop L.EQ test (cgConst t), cgBody ret exp)
cgAlt ret scr test (SDefaultCase exp) = (L.Bool True, cgBody ret exp)
cgAlt ret scr test (SConCase lv t n args exp)
    = (Binop L.EQ test (number t), Block (project 1 lv args) Nothing
        `concatBlock` cgBody ret exp)
   where project i v [] = []
         project i v (n : ns) = [Assign [VarName $ loc v] [table scr (number (i + 1))]]
                            ++ project (i + 1) (v + 1) ns

cgVar :: LVar -> String
cgVar (Loc i) = loc i
cgVar (Glob n) = var n

cgConst :: Const -> Exp
cgConst (I i) = Number $ show i
cgConst (Ch i) = Number $ show (ord i) -- Treat Char as ints, because PHP treats them as Strings...
cgConst (BI i) = pfuncall "bigint" [String $ show i]
cgConst (TT.Str s) = String $ show s
cgConst TheWorld = String "0"
cgConst x | isTypeConst x = String "0"
cgConst x = error $ "Constant " ++ show x ++ " not compilable yet"

cgOp :: PrimFn -> [Exp] -> Exp
cgOp (LPlus (ATInt _)) [l, r]
     = Binop Add l r
cgOp (LMinus (ATInt _)) [l, r]
     = Binop Sub l r
cgOp (LTimes (ATInt _)) [l, r]
     = Binop Mul l r
cgOp (LEq (ATInt _)) [l, r]
     = Binop L.EQ l r
cgOp (LSLt (ATInt _)) [l, r]
     = Binop L.LT l r
cgOp (LSLe (ATInt _)) [l, r]
     = Binop LTE l r
cgOp (LSGt (ATInt _)) [l, r]
     = Binop L.GT l r
cgOp (LSGe (ATInt _)) [l, r]
     = Binop GTE l r
cgOp LStrEq [l,r] = Binop L.EQ l r
cgOp LStrRev [x] = pfuncall "string.reverse" [x]
cgOp LStrLen [x] = pfuncall "string.len" [x]
cgOp LStrHead [x] = pfuncall "string.sub" [x, Number "1", Number "2"]
cgOp LStrIndex [x, y] = pfuncall "string.sub" [x, Binop Add y (number 1), Binop Add y (number 2)]
cgOp LStrTail [x] = pfuncall "string.sub" [x, Number "2"]

cgOp (LIntStr _) [x] = pfuncall "tostring" [x]
cgOp (LChInt _) [x] = pfuncall "string.byte" [x]
cgOp (LIntCh _) [x] = pfuncall "string.char" [x]
cgOp (LSExt _ _) [x] = x
cgOp (LTrunc _ _) [x] = x
cgOp LWriteStr [_,str] = pfuncall "print" [str]
cgOp LReadStr [_] = pfuncall "io.read" []
cgOp LStrConcat [l,r] = Binop Concat l r
cgOp LStrCons [l,r] = Binop Concat l r
cgOp (LStrInt _) [x] = x
cgOp op exps = pfuncall "print" [String $ "error(\"OPERATOR " ++ show op ++ " NOT IMPLEMENTED!!!!\")"]
   -- error("Operator " ++ show op ++ " not implemented")
