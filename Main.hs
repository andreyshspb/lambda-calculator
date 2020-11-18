import Data.Set ( Set, singleton, union, member, delete )


type Symb = String 

infixl 2 :@
infix  1 `alphaEq`
infix  1 `betaEq`

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)


freeVars :: Expr -> Set Symb
freeVars (Var s)   = singleton s
freeVars (l :@ r)  = freeVars l `union` freeVars r
freeVars (Lam s e) = delete s (freeVars e)


makeUnique :: Symb -> Set Symb -> Set Symb -> Symb
makeUnique n f s = if   member n f || member n s 
                   then makeUnique ('\'' : n) f s
                   else n


-- term[var := subterm] --
subst :: Symb -> Expr -> Expr -> Expr 
subst v n buf@(Var s)   | s == v    = n
                        | otherwise = buf

subst v n (l :@ r)      = subst v n l :@ subst v n r

subst v n buf@(Lam s e) | s == v    = buf
                        | otherwise = if   member s (freeVars n)
                                      then let name = makeUnique s (freeVars n) (freeVars e)
                                           in  Lam name $ subst v n $ subst s (Var name) e
                                      else Lam s (subst v n e)


-- alpha equivalence --
alphaEq :: Expr -> Expr -> Bool
alphaEq (Var f)     (Var s)     = f == s

alphaEq (l1 :@ r1)  (l2 :@ r2)  = (l1 `alphaEq` l2) && (r1 `alphaEq` r2)

alphaEq (Lam s1 e1) (Lam s2 e2) | s1 == s2  = e1 `alphaEq` e2
                                | otherwise = not (member s1 $ freeVars e2)
                                              && (e1 `alphaEq` subst s2 (Var s1) e2)

alphaEq _           _           = False
                                            

-- beta reduction --
reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var _)          = Nothing

reduceOnce ((Lam s e) :@ r) = Just (subst s r e)

reduceOnce (l :@ r)         = case reduceOnce l of 
                                  Nothing -> case reduceOnce r of
                                                 Nothing -> Nothing
                                                 Just r' -> Just (l :@ r')
                                  Just l' -> Just (l' :@ r) 

reduceOnce (Lam symb expr)  = case reduceOnce expr of 
                                  Nothing   -> Nothing
                                  Just elem -> Just (Lam symb elem)


-- beta reduction using normal strategy
nf :: Expr -> Expr 
nf expr = maybe expr nf (reduceOnce expr)


-- beta equivalence
betaEq :: Expr -> Expr -> Bool 
betaEq first second = nf first `alphaEq` nf second