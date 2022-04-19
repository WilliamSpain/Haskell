{-# LANGUAGE TemplateHaskell #-}
import Data.List

data Term = Var String | Application Term Term | Lambda String Term
  deriving (Show, Eq)


-- QUESTION 1 freeVars

checkfreevars :: Integer -> [String]
-- (\x.x z)
checkfreevars 1 = freeVars (Application (Lambda "x" (Var "x")) (Var "z"))
-- (\v.\x.v \x.\u.x)
checkfreevars 2 = freeVars (Application (Lambda "v" (Lambda "x" (Var "v")))(Lambda "x" (Lambda "u" (Var "x"))))

removeWord :: String -> [String] -> [String]
removeWord _ [] = []
removeWord boundWord (x:xs) =
  if x == boundWord
      then removeWord boundWord xs
      else x:removeWord boundWord xs

freeVars :: Term -> [String]
freeVars (Var t) = t:[]
freeVars (Application tb ta) = freeVars tb++freeVars ta
freeVars (Lambda ts tt) = removeWord ts (freeVars tt)


--QUESTION 2 normalForm

checknormalform :: Integer -> Bool
-- ((\x.x) z)
checknormalform 1 = normalForm (Application (Lambda "x" (Var "x")) (Var "z"))
-- (\x.y)
checknormalform 2 = normalForm (Lambda "x" (Var "y"))


isLambda :: Term -> Bool
isLambda (Lambda _ _) = True
isLambda _ = False

isApp :: Term -> Bool
isApp (Application _ _) = True
isApp _ = False

isVar :: Term -> Bool
isVar (Var _) = True
isVar _ = False

normalForm :: Term -> Bool
normalForm (Application t1 t2) = 
  if (isLambda t1)&&((isVar t2)||(isApp t2))
      then False
  else if (isVar t1)&&(isVar t2)
      then True
  else normalForm t1 && normalForm t2
normalForm (Lambda _ _) = True
normalForm (Var _) = True


--QUESTION 3 listOVars

checklistovars :: [String]
checklistovars = take 50 listOVars

listOVars :: [String]
listOVars = [ variables : estring | estring <- "" : listOVars, variables <- ['a'..'z'] ++ ['0'..'9'] ]


--QUESTION 4 substitute

checksubstitute :: Integer -> Term
-- ((\x.x) z) sub "z" for "a"
checksubstitute 1 = (substitute (Application (Lambda "x" (Var "x")) (Var "z")) "z" (Var "a"))
-- ((\x.x) z)((\x.x) z)) sub "z" for "a"
checksubstitute 2 = (substitute (Application (Application (Lambda "x" (Var "x")) (Var "z")) (Application (Lambda "x" (Var "x")) (Var "z"))) "z" (Var "a"))


substitute :: Term -> String -> Term -> Term

substitute (Application t1 t2) replaced (Application t3 t4) =
  if replaced `elem` (freeVars t1) &&  replaced `elem` freeVars t2
      then (Application (substitute t1 replaced (Application t3 t4)) (substitute t2 replaced (Application t3 t4)))
  else if replaced `elem` freeVars t1
      then (Application (substitute t1 replaced (Application t3 t4)) t2)
  else if replaced `elem` freeVars t2
      then (Application t1 (substitute t2 replaced (Application t3 t4)))
      else (Application t1 t2) 
substitute (Application t1 t2) replaced (Lambda t3 t4) =
  if replaced `elem` freeVars t1 && replaced `elem` freeVars t2
      then (Application (substitute t1 replaced (Lambda t3 t4)) (substitute t2 replaced (Lambda t3 t4)))
  else if replaced `elem` freeVars t1
      then (Application (substitute t1 replaced (Lambda t3 t4)) t2)
  else if replaced `elem` freeVars t2
      then (Application t1 (substitute t2 replaced (Lambda t3 t4)))
      else (Application t1 t2)
substitute (Application t1 t2) replaced (Var t3) =
  if replaced `elem` freeVars t1 && replaced `elem` freeVars t2
      then (Application (substitute t1 replaced (Var t3)) (substitute t2 replaced (Var t3)))
  else if replaced `elem` freeVars t1
      then (Application (substitute t1 replaced (Var t3)) t2)
  else if replaced `elem` freeVars t2
      then (Application t1 (substitute t2 replaced (Var t3)))
      else (Application t1 t2)

substitute (Lambda t1 t2) replaced (Lambda t3 t4) =
  if replaced `elem` freeVars t2
      then (Lambda t1 (substitute t2 replaced (Lambda t3 t4)))
      else (Lambda t1 t2)
substitute (Lambda t1 t2) replaced (Application  t3 t4) =
  if replaced `elem` freeVars t2
      then (Lambda t1 (substitute t2 replaced (Application t3 t4)))
      else (Lambda t1 t2)
substitute (Lambda t1 t2) replaced (Var t3) =
  if replaced `elem` freeVars t2
      then (Lambda t1 (substitute t2 replaced (Var t3)))
      else (Lambda t1 t2)

substitute (Var v1) replaced (Var t2) = (Var t2)
substitute (Var v2) replaced (Application t1 t2) = (Application t1 t2)
substitute (Var v3) replaced (Lambda t1 t2) = (Lambda t1 t2)


-- QUESTION 5 alphaRename

checkalpharename :: Term
checkalpharename = (alphaRename (Lambda "x" (Var "x")) "y")
  
alphaRename :: Term -> String -> Term
alphaRename (Lambda t1 t2) replace =
  (Lambda replace (renameBounds (Var t1) (t2) (replace)))

--helps alpharename to rename the bound variables to match the changed formal variable
renameBounds :: Term -> Term ->String ->Term
renameBounds (Var formal) (Var t1) replace =
   if(formal == t1)
       then (Var replace)
   else (Var t1)
renameBounds (Var formal) (Application t1 t2) replace =
  (Application (renameBounds (Var formal) (t1) (replace)) (renameBounds (Var formal) (t2) (replace)))
renameBounds (Var formal) (Lambda t1 t2) replace =
  if(formal == t1)
      then (Lambda replace (renameBounds (Var formal) (t2) (replace)))
  else (Lambda t1 (renameBounds (Var formal) (t2) (replace)))


-- QUESTION 6 betaReduce 


checkbetareduce :: Term
-- (\x.x) <- ((\z.z)y)
checkbetareduce = (betaReduce (Lambda "x" (Var "x")) (Application (Lambda "z" (Var "z")) (Var "y")))
  
--helps to get unique variables filtering formalparams+freevars+listovars and getting the head and checks for other formals in freevars
renameHelper ::[String]->Term -> Term -> Term
renameHelper formals (Lambda t1 t2) (Lambda t3 t4) =
  if sharesElem (formalParams (Lambda t1 t2)) (freeVars(Lambda t3 t4))
      then
          if t1 `elem` freeVars (Lambda t3 t4)
              then alphaRename (Lambda t1 t2) ((head (filter (`notElem` (formals)) (filter (`notElem` (freeVars (Lambda t3 t4))) listOVars))))
          else renameHelper (formals) (t2) (Lambda t3 t4)
  else (Lambda t1 t2)
  
renameHelper formals (Lambda t1 t2) (Var t3) =
  if sharesElem (formalParams (Lambda t1 t2)) (freeVars(Var t3))
      then
          if t1 `elem` freeVars (Var t3)
              then alphaRename (Lambda t1 t2) ((head (filter (`notElem` (formals)) (filter (`notElem` (freeVars (Var t3 ))) listOVars))))
          else renameHelper (formals) (t2) (Var t3)
  else (Lambda t1 t2)
renameHelper formals (Lambda t1 t2) (Application t3 t4) =   
  if sharesElem (formalParams (Lambda t1 t2)) (freeVars(Application t3 t4))
      then
          if t1 `elem` freeVars (Application t3 t4)
              then alphaRename (Lambda t1 t2) ((head (filter (`notElem` (formals)) (filter (`notElem` (freeVars (Application  t3 t4 ))) listOVars))))
          else renameHelper (formals) (t2) (Application t3 t4)
  else (Lambda t1 t2)

renameHelper formals (Application t1 t2) (Application t3 t4) =
  if isVar t1 && isVar t2
      then (Application t1 t2)
  else if isVar t1
      then (Application t1 (renameHelper (formals) (t2) (Application t3 t4)))
  else if isVar t2
      then (Application (renameHelper (formals) (t1) (Application t3 t4)) t2)
  else (Application (renameHelper (formals) (t1) (Application t3 t4)) (renameHelper (formals) (t2) (Application t3 t4)))
renameHelper formals (Application t1 t2) (Lambda t3 t4) =
  if isLambda t1 || isApp t1 && isApp t2||isLambda t2
      then (Application (renameHelper formals t1 (Lambda t3 t4)) (renameHelper formals t2 (Lambda t3 t4)))
  else if isLambda t1 || isApp t1
      then (Application (renameHelper formals t1 (Lambda t3 t4)) t2)
  else if isLambda t2 || isApp t2
      then (Application t1 (renameHelper formals t2 (Lambda t3 t4)))
  else (Application t1 t2)
  
formalParams :: Term -> [String]
formalParams (Lambda t1 t2) =
  if isVar t2
      then [t1]
  else if isApp t2 || isLambda t2
      then [t1]++formalParams t2
  else []
formalParams (Application t1 t2)=formalParams t1++formalParams t2
formalParams (Var t1) = []

--do two lists share an element
sharesElem :: [String] -> [String] -> Bool
sharesElem [] _ = False
sharesElem (x:xs) ys
  | elem x ys = True
  | otherwise = sharesElem xs ys 

betaReduce :: Term -> Term -> Term
betaReduce (Lambda t1 t2) (Lambda t3 t4)=
  if sharesElem (formalParams (Lambda t1 t2)) (freeVars (Lambda t3 t4))
      then betaReduce (substitute (renameHelper (formalParams (Lambda t1 t2)) (Lambda t1 t2)((Lambda t3 t4))) t1 (Lambda t3 t4)) (Lambda t3 t4)
      else substitute t2 t1(Lambda t3 t4)
betaReduce (Lambda t1 t2) (Var t3)=
  if sharesElem (formalParams (Lambda t1 t2)) (freeVars (Var t3))
      then betaReduce (substitute (renameHelper (formalParams (Lambda t1 t2) )(Lambda t1 t2) (Var t3)) t1 (Var t3)) (Var t3)
      else substitute t2 t1 (Var t3)
betaReduce (Lambda t1 t2) (Application t3 t4)=
  if sharesElem (formalParams (Lambda t1 t2)) (freeVars (Application t3 t4))
      then betaReduce (substitute (renameHelper (formalParams (Lambda t1 t2) )(Lambda t1 t2) (Application t3 t4)) t1 (Application t3 t4)) (Application t3 t4)
      else substitute t2 t1 (Application t3 t4)

betaReduce (Application t1 t2) (Application t3 t4) =(Application (betaReduce t1 t2) (betaReduce t3 t4))
betaReduce (Application t1 t2) (Lambda t3 t4) =(Application (betaReduce t1 t2) (Lambda t3 t4))
betaReduce (Application t1 t2) (Var t3) = (Application (betaReduce t1 t2) (Var t3))

betaReduce (Var t1) (Var t2) = Var t1
betaReduce (Var t1) (Lambda t3 t4) = Var t1
betaReduce (Var t1) (Application t3 t4) = Var t1
  


--QUESTION 7 normalize


--normalizes (\x.x) <- ((\z.z)y)
checknormalize :: Term

checknormalize = (normalize checkbetareduce)

normalize :: Term -> Term
normalize (Application t1 t2)=(betaReduce (normalize t1) (normalize t2))
normalize (Lambda t1 t2)= (Lambda t1 (normalize t2))
normalize (Var t1) = (Var t1)


-- QUESTION 8 TermS

data TermS = VarS String | ApplicationS TermS [TermS] | LambdaS [String] TermS
  deriving (Show,Eq)



isLambdaS :: TermS -> Bool
isLambdaS (LambdaS _ _) = True
isLambdaS _ = False

isAppS :: TermS -> Bool
isAppS (ApplicationS _ _) = True
isAppS _ = False

isVarS :: TermS -> Bool
isVarS (VarS _) = True
isVarS _ = False

--Quesiton 9 deSugar

checkdesugar :: Term
checkdesugar = (deSugar (ApplicationS (VarS "a") [(VarS "b"),(VarS "c"),(VarS "d")] ))

deSugar :: TermS -> Term
deSugar (VarS t1) = Var t1
deSugar (ApplicationS t1 t2) =
  if length t2 > 1
      then (Application (deSugar (ApplicationS t1 (take ((length t2)-1) t2))) (deSugar (last t2)))
  else (Application (deSugar t1) (deSugar (head t2)))
deSugar (LambdaS t1 t2) =
  if length t1 > 1
      then (Lambda (head t1) (deSugar (LambdaS (tail t1) t2 )))
  else if isAppS t2 || isLambdaS t2
      then (Lambda (head t1) (deSugar t2))
  else (Lambda (head t1) (deSugar t2))


-- simple version compared to main test case to check if working

checkterm1 :: Term
checkterm1 =Lambda "x" (Application (Lambda "y" (Var "y")) (Var "x"))
checkterm2 :: Term
checkterm2 =Application (Lambda "z" (Var "z")) (Var "y")
checktestcases :: Term
checktestcases = normalize(betaReduce (checkterm1) (checkterm2))


--Question 10 testCaseS + testCase


testCaseS :: TermS
testCaseS = (ApplicationS
             --first term
               (LambdaS ["t"](ApplicationS
                              ((LambdaS ["m","n"] (ApplicationS (VarS "n") [((LambdaS ["n","f","x"] (ApplicationS (VarS "n") [(VarS "f"),(ApplicationS (VarS "f") [(VarS "x")])]))),(VarS "m")] )))
                              
                              [((ApplicationS (LambdaS ["n"] (ApplicationS (LambdaS ["m","n","f"] (ApplicationS (VarS "m") [(VarS "n"),(VarS "f")])) [(VarS "n"),(VarS "n")] ))
                              [((ApplicationS ((LambdaS ["m","n","f"] (ApplicationS (VarS "m") [(VarS "n"),(VarS "f")]))) [(VarS "t")]))])),
                               
                               ((ApplicationS ((LambdaS ["m","n","f"] (ApplicationS (VarS "m") [(VarS "n"),(VarS "f")]))) [(VarS "t")]))]))
               --second term
               [((ApplicationS ((LambdaS ["m","n"] (ApplicationS (VarS "n") [((LambdaS ["n","f","x"] (ApplicationS (VarS "n") [(VarS "f"),(ApplicationS (VarS "f") [(VarS "x")])]))),(VarS "m")])))
                  [((ApplicationS
                     ((LambdaS ["m","n","f"] (ApplicationS (VarS "m") [(ApplicationS (VarS "n") [(VarS "f")])] )))
                     [((LambdaS ["f","x"] (VarS "x"))),
                      ((ApplicationS ((LambdaS ["m","n"] ((ApplicationS (VarS "n") [((LambdaS ["n","f","x"] (ApplicationS (VarS "n") [(VarS "f"),(ApplicationS (VarS "f") [(VarS "x")])]))),(VarS "m")]))))
                        [((ApplicationS ((LambdaS ["n","f","x"] (ApplicationS (VarS "n") [(VarS "f"),(ApplicationS (VarS "f") [(VarS "x")])]))) [((LambdaS ["f","x"] (VarS "x")))])),
                         ((ApplicationS ((LambdaS ["n","f","x"] (ApplicationS (VarS "n") [(VarS "f"),(ApplicationS (VarS "f") [(VarS "x")])]))) [((LambdaS ["f","x"] (VarS "x")))]))]))])),
                    ((ApplicationS ((LambdaS ["n","f","x"] (ApplicationS (VarS "n") [(VarS "f"),(ApplicationS (VarS "f") [(VarS "x")])]))) [((ApplicationS ((LambdaS ["n","f","x"] (ApplicationS (VarS "n") [(VarS "f"),(ApplicationS (VarS "f") [(VarS "x")])]))) [((LambdaS ["f","x"] (VarS "x")))]))]))]))])

  
testCase :: Term
testCase = (normalize . deSugar) testCaseS
