import qualified Data.Set as Set

type Variables = String

data ParseTree
   = Identifier Variables
   | Abstraction (Variables, ParseTree) 
   | Application (ParseTree, ParseTree)
      deriving (Show,Read,Eq)

type ErrorMessage = String

findMostLeftTerm :: [String] -> Either ErrorMessage ([String],[String])
-- ex) findMostLeftTerm (words "( \\a. ( b c ) d ) e" == Right (["\\a.","(","b","c",")","d"],["e"])
findMostLeftTerm (")":_)          = Left "bracket unmatched - somewhere starts with )"
findMostLeftTerm ("(":xs)         = searchPairBracket xs 1
findMostLeftTerm ss@(('\\':_):_)  = Right (ss,[])
findMostLeftTerm   (x:xs)         = Right (x:[],xs)
findMostLeftTerm x                = Right (x,[])

searchPairBracket :: [String] -> Integer -> Either ErrorMessage ([String], [String])
-- ex) searchPairBracket (words " \\a. ( a a ) a ) a" ) == Right (["\\a.","(","a","a",")","a"],[,"a"]) 
searchPairBracket ss       0 = Right ([],ss)
searchPairBracket []       _ = Left "bracket unmatched - too many ("
searchPairBracket ("(":xs) n = do
   (fp,bp) <- searchPairBracket xs (n+1)
   Right (("(":fp),bp)
searchPairBracket (")":xs) n = do
   (fp,bp) <- searchPairBracket xs (n-1)
   if n-1 == 0
   then do
      Right (fp,bp)
   else do
      Right ((")":fp),bp)
searchPairBracket (x:xs)   n = do
   (fp,bp) <- searchPairBracket xs n
   Right ((x:fp),bp)

findMostRightPart :: [String] -> Either ErrorMessage ([String],[String])
findMostRightPart ss = do
   (fp,bp) <- findMostLeftTerm ss
   if bp == []
   then do
      Right ([],fp)
   else do
      (lp,rp) <- findMostRightPart bp
      if lp == []
      then do
         Right (["("] ++ fp ++ [")"] , rp)
      else do
         Right (["("] ++ fp ++ [")"] ++ lp, rp)

decomposeToWords :: String -> [String]
decomposeToWords s = words (filter (/='.') $ bracketForming s)
   where
      bracketForming :: String -> String
      bracketForming []       = []
      bracketForming ('(':xs) = " ( " ++ (bracketForming xs)
      bracketForming (')':xs) = " ) " ++ (bracketForming xs)
      bracketForming (x:xs)   = (x:(bracketForming xs))

parsingIntoTree :: [String] -> Either ErrorMessage ParseTree
parsingIntoTree ss = 
   case ss of
      [] -> Left "empty formula"
      (('\\':xs):[]) -> Left "A lambda part is not forming an abstruction"
      (x:[])         -> Right (Identifier x) 
      (('\\':xs):ys) -> do
         yys <- parsingIntoTree ys
         Right (Abstraction (xs, yys))
      _              -> do
         (lp,rp) <- findMostRightPart ss
         if lp == []
         then 
            parsingIntoTree rp
         else do
            rpPurse <- parsingIntoTree rp
            lpPurse <- parsingIntoTree lp
            Right (Application (lpPurse, rpPurse))
      
freeVariables :: ParseTree -> Set.Set Variables
freeVariables (Identifier x)      = Set.singleton x
freeVariables (Abstraction (x,m)) = Set.delete x $ freeVariables m
freeVariables (Application (m,n)) = Set.union (freeVariables m) (freeVariables n)

usedVariables :: ParseTree -> Set.Set Variables
usedVariables (Identifier x)      = Set.singleton x
usedVariables (Abstraction (x,m)) = Set.insert x $ usedVariables m
usedVariables (Application (m,n)) = Set.union (usedVariables m) (usedVariables n)

freshVariable :: ParseTree -> String
freshVariable tree = head $ filter (\x -> Set.notMember x (usedVariables tree)) $ map (\y -> "X" ++ (show y)) [1..]

substitution :: ParseTree -> String -> ParseTree -> ParseTree
-- ex) 'substitution t x y' means rewrite var x by tree y in tree t (t[x:=y])
substitution (Identifier z) x y =
   if z == x
   then
      y
   else
      Identifier z
substitution (Abstraction (z,m)) x y =
   if z == x
   then
      Abstraction (z,m)
   else if Set.member z $ freeVariables y
   then
      let w = freshVariable m in
      Abstraction (w, substitution (substitution m z (Identifier w)) x y)
   else
      Abstraction (z, substitution m x y)
substitution (Application (m,n)) x y = Application (substitution m x y, substitution n x y)

{-
substituteByVar :: ParseTree -> Variables -> Variables -> ParseTree
substituteByVar (Identifier z) x y =
   if z == x
   then
      Identifier y
   else
      Identifier z
substituteByVar (Abstraction (z,m)) x y = 
   if z == x
   then
      Abstraction (z,m)
   else if z == y
   then -- AlphaConversion
      let w = freshVariable m in
      Abstraction (w, substituteByVar (substituteByVar m z w) x y)
   else
      Abstraction (z, substituteByVar m x y)
substituteByVar (Application (m,n)) x y = Application (substituteByVar m x y, substituteByVar n x y)
-}

betaReduction :: ParseTree -> ParseTree
betaReduction (Application (Abstraction (w,n),m)) = (substitution n w m)
betaReduction x = x -- not used

searchMostLeftRedexAndReductIt :: Either ErrorMessage ParseTree -> Either ErrorMessage ParseTree
searchMostLeftRedexAndReductIt (Right tree) =
   case tree of      
      (Identifier _)                      -> Left "Normal Form"
      (Abstraction (x, tree))             -> do
         innerTree <- searchMostLeftRedexAndReductIt $ Right tree
         Right (Abstraction (x, innerTree))
      (Application (Abstraction (w,n),m)) -> Right $ betaReduction tree
      (Application (m,n))                 -> 
         let leftTree = searchMostLeftRedexAndReductIt (Right m) in
         case leftTree of
            Left _ -> do
               rightTreeComponent <- searchMostLeftRedexAndReductIt $ Right n
               Right (Application (m, rightTreeComponent))
            Right _ -> do
               leftTreeComponent <- leftTree
               Right (Application (leftTreeComponent, n))

makeUsualCalcForm :: ParseTree -> String
makeUsualCalcForm (Identifier x)                  = x ++ " "
makeUsualCalcForm (Abstraction (x, Identifier y)) = "\\" ++ x ++ ". " ++ (makeUsualCalcForm (Identifier y))
makeUsualCalcForm (Abstraction (x, m))            = "\\" ++ x ++ ". ( " ++ (makeUsualCalcForm m) ++ ") "
makeUsualCalcForm (Application (Abstraction (x, m), Abstraction (y, n))) = "( " ++ (makeUsualCalcForm (Abstraction (x, m))) ++ ") ( " ++ (makeUsualCalcForm (Abstraction (y, n))) ++ ") "
makeUsualCalcForm (Application (Abstraction (x, l), Application (m, n))) = "( " ++ (makeUsualCalcForm (Abstraction (x, l))) ++ ") ( " ++ (makeUsualCalcForm (Application (m, n))) ++ ") "
makeUsualCalcForm (Application (Abstraction (x, m), n)) = "( " ++ (makeUsualCalcForm (Abstraction (x, m))) ++ ") " ++ (makeUsualCalcForm n)
makeUsualCalcForm (Application (m, Abstraction (y, n))) = (makeUsualCalcForm m) ++ "( " ++ (makeUsualCalcForm (Abstraction (y, n))) ++ ") "
makeUsualCalcForm (Application (l, Application (m, n))) = (makeUsualCalcForm l) ++ "( " ++ (makeUsualCalcForm (Application (m, n))) ++ ") "
makeUsualCalcForm (Application (m, n))            = makeUsualCalcForm m ++ makeUsualCalcForm n

spanListOfEitherAtTheFirstLeft :: [Either a b] -> [Either a b]
spanListOfEitherAtTheFirstLeft []   = []
spanListOfEitherAtTheFirstLeft (Right x:xs) = (Right x:spanListOfEitherAtTheFirstLeft xs)
spanListOfEitherAtTheFirstLeft (Left x:xs)  = (Left x:[])

main = do
   str <- getLine
   let
      tree = parsingIntoTree $ decomposeToWords str
      reductionList = spanListOfEitherAtTheFirstLeft $ iterate searchMostLeftRedexAndReductIt tree
      showingForm = map (either id makeUsualCalcForm) reductionList
   mapM_ putStrLn $ (flip take) showingForm 10
