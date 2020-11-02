import Data.List


type Symb = String 

infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)


freeVars :: Expr -> [Symb]
freeVars (Var symb)        = [symb]
freeVars (first :@ second) = nub $ (freeVars first) ++ (freeVars second)
freeVars (Lam symb expr)   = filter (/= symb) (freeVars expr)


-- term[var := subterm] --
subst :: Symb -> Expr -> Expr -> Expr 
subst var subterm (Var name)        = if name == var then subterm else (Var name)
subst var subterm (first :@ second) = (subst var subterm first) :@ (subst var subterm second)
subst var subterm (Lam symb expr)   = if symb == var then (Lam symb expr) else result            -- TODO --
                                          where free_subterm = freeVars subterm
                                                free_expr    = freeVars expr
                                                free         = nub $ free_subterm ++ free_expr
                                                make_unique  = \name -> if   elem name free 
                                                                        then make_unique (name ++ "'") 
                                                                        else name
                                                result       = if   elem symb free_subterm
                                                               then let name   = make_unique symb
                                                                        first  = subst symb (Var name) expr
                                                                        second = subst var subterm first 
                                                                    in  Lam name second 
                                                               else Lam symb (subst var subterm expr)
                                                 

