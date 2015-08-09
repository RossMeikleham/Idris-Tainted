module TaintExample

import Data.Tainted


data Expr = 
  Number (Tainted Int)
  | Add Expr Expr
              
instance Show Expr where
  show (Number x) = "Number (" ++ show x ++ ")"
  show (Add e1 e2) = "Add " ++ show e1 ++ " " ++ show e2

pure1 : Expr
pure1 = Number (Clean 3)

pure2 : Expr
pure2 = Number (Clean 7)

impure1 : Expr
impure1 = Number (Dirty 5)

expr1 : Expr
expr1 = Add pure1 pure2

expr2 : Expr
expr2 = Add impure1 pure1

expr3 : Expr
expr3 = Add pure1 (Add impure1 pure2) 

--Evaluate expression as much as Possible
evalExpr : Expr -> Expr
evalExpr (Number n) = Number n
evalExpr (Add e1 e2) = 
    case (evalExpr e1, evalExpr e2) of
            (Number i, Number j) => Number $ liftA2 (+) i j
            (x, y) => Add x y


reducedExpr1 : Expr
reducedExpr1 = evalExpr expr1

reducedExpr2 : Expr
reducedExpr2 = evalExpr expr2

reducedExpr3 : Expr
reducedExpr3 = evalExpr expr3
