
module Parser where


import Text.ParserCombinators.Parsec

import LambdaCalculus


instance Show Expr where
    show (Var s)                  = s 
    show (Var s1 :@ Var s2)       = s1 ++ " " ++ s2
    show (Var s :@ r)             = s ++ " (" ++ show r ++ ")"
    show (l :@ r)                 = "(" ++ show l ++ ") (" ++ show r ++ ")"
    show (Lam s e)                = "\\" ++ s ++ " -> " ++ show e


instance Read Expr where
    readsPrec _ s = case parseString s of 
        Left _  -> undefined
        Right x -> [(x, "")]



parseString :: String -> Either ParseError Expr    
parseString = parse (do r <- parseExpression; eof; return r) ""


parseIdentifier :: Parser String
parseIdentifier = do 
    h <- letter 
    t <- many alphaNum
    _ <- spaces
    return (h:t)


parseVariable :: Parser Expr
parseVariable = Var <$> parseIdentifier


parseBrackets :: Parser Expr
parseBrackets = do  
    _ <- char '(' >> spaces
    e <- parseExpression
    _ <- char ')' >> spaces
    return e


parseExpression :: Parser Expr
parseExpression = try parseApplication <|>
                  try parseAtom


parseAtom :: Parser Expr 
parseAtom = try parseLambda   <|>
            try parseVariable <|>
            try parseBrackets


parseApplication :: Parser Expr
parseApplication = chainl1 parseAtom (return (:@))


parseLambda :: Parser Expr
parseLambda = do
    _      <- char '\\' >> spaces
    idents <- many1 parseIdentifier
    _      <- string "->" >> spaces
    expr   <- parseExpression
    return $ foldr Lam expr idents

