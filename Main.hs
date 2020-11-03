
import Data.Maybe


type Symb = String 

infixl 2 :@
infix  1 `alphaEq`
infix  1 `betaEq`

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)


freeVars :: Expr -> [Symb]
freeVars (Var symb)        = [symb]
freeVars (first :@ second) = (freeVars first) ++ (freeVars second)
freeVars (Lam symb expr)   = filter (/= symb) (freeVars expr)


make_unique :: Symb -> [Symb] -> Symb
make_unique name list = if   elem name list 
                        then make_unique (name ++ "'") list
                        else name 


-- term[var := subterm] --
subst :: Symb -> Expr -> Expr -> Expr 
subst var subterm (Var name)        = if name == var then subterm else (Var name)
subst var subterm (first :@ second) = (subst var subterm first) :@ (subst var subterm second)
subst var subterm (Lam symb expr)   = if symb == var then (Lam symb expr) else result            -- TODO --
                                          where free_subterm = freeVars subterm
                                                free_expr    = freeVars expr
                                                result       = if   elem symb free_subterm
                                                               then let name   = make_unique symb (free_subterm ++ free_expr)
                                                                        first  = subst symb (Var name) expr
                                                                        second = subst var subterm first 
                                                                    in  Lam name second 
                                                               else Lam symb (subst var subterm expr)


-- alpha equivalence --
alphaEq :: Expr -> Expr -> Bool
alphaEq (Var first)       (Var second)      = (first == second)
alphaEq (left1 :@ right1) (left2 :@ right2) = (left1 `alphaEq` left2) && (right1 `alphaEq` right2)
alphaEq (Lam symb1 expr1) (Lam symb2 expr2) = let first  = expr1 `alphaEq` (subst symb2 (Var symb1) expr2)
                                                  second = expr2 `alphaEq` (subst symb1 (Var symb2) expr1)
                                              in  first && second
alphaEq _                 _                 = False
                                            

-- beta reduction --
reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var _)                    = Nothing

reduceOnce ((Lam symb expr) :@ right) = Just (subst symb right expr)

reduceOnce (left :@ right)            = let left'   = reduceOnce left 
                                            right'  = reduceOnce right
                                        in  if   left' == Nothing && right' == Nothing
                                            then Nothing
                                            else let left''  = maybe left id left'
                                                     right'' = maybe right id right'
                                                 in  Just (left'' :@ right'')

reduceOnce (Lam symb expr)            = let result = reduceOnce expr 
                                        in  if   result == Nothing 
                                            then Nothing
                                            else Just (Lam symb $ fromJust result)


-- beta reduction using normal strategy
nf :: Expr -> Expr 
nf expr = let reduce = reduceOnce expr
          in  if reduce == Nothing
              then expr
              else nf $ fromJust reduce 


-- beta equivalence
betaEq :: Expr -> Expr -> Bool 
betaEq first second = (nf first) `alphaEq` (nf second)
