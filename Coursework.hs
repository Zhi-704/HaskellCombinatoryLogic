
-- imports chr function that converts integer to character, for assignment 4
-- import Data.Char (chr)
-- imports function that avoids duplicate variables, for assignment 5
import Data.List

------------------------- Auxiliary functions

merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys

variables :: [Var]
variables = [ [x] | x <- ['a'..'z'] ] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

removeAll :: [Var] -> [Var] -> [Var]
removeAll xs ys = [ x | x <- xs , not (elem x ys) ]

fresh :: [Var] -> Var
fresh = head . removeAll variables


-- - - - - - - - - - - -- Terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term

pretty :: Term -> String
pretty = f 0
    where
      f i (Variable x)   = x
      f i (Lambda x m)   = if elem i [2,3] then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 1 m 
      f i (Apply  m n)   = if elem i   [3] then "(" ++ s ++ ")" else s where s = f 2 m ++ " " ++ f 3 n

instance Show Term where
  show = pretty

-- - - - - - - - - - - -- Numerals


numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))


-- - - - - - - - - - - -- Renaming, substitution, beta-reduction


used :: Term -> [Var]
used (Variable x) = [x]
used (Lambda x m) = [x] `merge` used m
used (Apply  m n) = used n `merge` used m


rename :: Var -> Var -> Term -> Term
rename y z (Variable x)
    | y == x    = Variable z
    | otherwise = Variable x
rename y z (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda x (rename y z m)
rename y z (Apply m n) = Apply (rename y z m) (rename y z n)

substitute :: Var -> Term -> Term -> Term
substitute y p (Variable x)
    | y == x    = p
    | otherwise = Variable x
substitute y p (Lambda x m)
    | y == x    = Lambda x m
    | otherwise = Lambda z (substitute y p (rename x z m))
    where z = fresh (used p `merge` used m `merge` [x,y])
substitute y p (Apply m n) = Apply (substitute y p m) (substitute y p n)

beta :: Term -> [Term]
beta (Apply (Lambda x m) n) =
  [substitute x n m] ++ 
  [Apply (Lambda x m') n  | m' <- beta m] ++
  [Apply (Lambda x m ) n' | n' <- beta n]
beta (Variable _) = []
beta (Lambda x m) = [Lambda x m' | m' <- beta m]
beta (Apply  m n) =
  [Apply m' n  | m' <- beta m] ++
  [Apply m  n' | n' <- beta n]


-- - - - - - - - - - - -- Normalize


normalize :: Term -> IO ()
normalize m = do
  print m
  let ms = beta m
  if null ms then
    return ()
  else
    normalize (head ms)


------------------------- Assignment 1: Combinators

infixl 5 :@ 

data Combinator = I | K | S | B | C | Q | R | X | Y | Z | Combinator :@ Combinator | V String 

example1 :: Combinator
example1 = S :@ K :@ K :@ V "x"

example2 :: Combinator
example2 = S :@ (K :@ K) :@ I :@ V "x" :@ V "y"

-- - - - - - - - - - - -- show, parse

instance Show Combinator where
  show = f 0
    where
      f _ I = "I"
      f _ K = "K"
      f _ S = "S"
      f _ B = "B"
      f _ C = "C"
      f _ Q = "Q"
      f _ R = "R"
      f _ X = "X"
      f _ Y = "Y"
      f _ Z = "Z"
      f _ (V s) = s
      f i (c :@ d) = if i == 1 then "(" ++ s ++ ")" else s where s = f 0 c ++ " " ++ f 1 d

parse :: String -> Combinator
parse s = down [] s
  where
    down :: [Maybe Combinator] -> String -> Combinator
    down cs (' ':str) = down cs str
    down cs ('(':str) = down (Nothing : cs) str
    down cs ('I':str) = up cs I str
    down cs ('K':str) = up cs K str
    down cs ('S':str) = up cs S str
    down cs ('B':str) = up cs B str
    down cs ('C':str) = up cs C str
    down cs ('Q':str) = up cs Q str
    down cs ('R':str) = up cs R str
    down cs ('X':str) = up cs X str
    down cs ('Y':str) = up cs Y str
    down cs ('Z':str) = up cs Z str
    down cs ( c :str) = up cs (V [c]) str
    up :: [Maybe Combinator] -> Combinator -> String -> Combinator
    up    []  c [] = c 
    up (Just c  : cs) d      str  = up cs (c:@d) str
    up (Nothing : cs) d (')':str) = up cs     d  str
    up            cs  d      str  = down (Just d : cs) str



-- - - - - - - - - - - -- step, run

-- parse "S(SI)(KI)(SIK)I"
-- All ++ allows function to do every one-step reduction including brackets
step :: Combinator -> [Combinator]
step (I :@ x) = 
  [x] 
  ++ [I :@ x' | x' <- step x]
step (K :@ x :@ y) = 
  [x]
  ++ [K :@ x' :@ y | x' <- step x]
  ++ [K :@ x :@ y' | y' <- step y]
step (S :@ x :@ y :@ z) =
  [x :@ z :@ (y :@ z)]
  ++ [S :@ x' :@ y :@ z | x' <- step x]
  ++ [S :@ x :@ y' :@ z | y' <- step y]
  ++ [S :@ x :@ y :@ z' | z' <- step z]
step (B :@ x :@ y :@ z) =
  [x :@ (y :@ z)]
  ++ [B :@ x' :@ y :@ z | x' <- step x]
  ++ [B :@ x :@ y' :@ z | y' <- step y]
  ++ [B :@ x :@ y :@ z' | z' <- step z]
step (C :@ x :@ y :@ z) =
  [(x :@ z) :@ y]
  ++ [C :@ x' :@ y :@ z | x' <- step x]
  ++ [C :@ x :@ y' :@ z | y' <- step y]
  ++ [C :@ x :@ y :@ z' | z' <- step z]
step (Q :@ u :@ x :@ y) =
  [u :@ x]
  ++ [Q :@ u' :@ x :@ y | u' <- step u]
  ++ [Q :@ u :@ x' :@ y | x' <- step x]
  ++ [Q :@ u :@ x :@ y' | y' <- step y]
step (R :@ u :@ v :@ x :@ y) =
  [u :@ v :@ x]
  ++ [R :@ u' :@ v :@ x :@ y | u' <- step u]
  ++ [R :@ u :@ v' :@ x :@ y | v' <- step v]
  ++ [R :@ u :@ v :@ x' :@ y | x' <- step x]
  ++ [R :@ u :@ v :@ x :@ y' | y' <- step y]
step (X :@ u :@ x :@ y :@ z) =
  [u :@ x :@ (y :@ z)]
  ++ [X :@ u' :@ x :@ y :@ z | u' <- step u]
  ++ [X :@ u :@ x' :@ y :@ z | x' <- step x]
  ++ [X :@ u :@ x :@ y' :@ z | y' <- step y]
  ++ [X :@ u :@ x :@ y :@ z' | z' <- step z]
step (Y :@ u :@ x :@ y :@ z) =
  [u :@ (x :@ z) :@ y]
  ++ [Y :@ u' :@ x :@ y :@ z | u' <- step u]
  ++ [Y :@ u :@ x' :@ y :@ z | x' <- step x]
  ++ [Y :@ u :@ x :@ y' :@ z | y' <- step y]
  ++ [Y :@ u :@ x :@ y :@ z' | z' <- step z]
step (Z :@ u :@ x :@ y :@ z) =
  [u :@ (x :@ z) :@ (y :@ z)]
  ++ [Z :@ u' :@ x :@ y :@ z | u' <- step u]
  ++ [Z :@ u :@ x' :@ y :@ z | x' <- step x]
  ++ [Z :@ u :@ x :@ y' :@ z | y' <- step y]
  ++ [Z :@ u :@ x :@ y :@ z' | z' <- step z]
step (x:@ y) = [x' :@ y | x' <- step x] 
  ++ [x :@ y' | y' <- step y]
step _ = []


run :: Combinator -> IO ()
run c = do
  putStrLn $ show c
  case step c of
    (c':_) -> run c'
    [] -> return()

------------------------- Assignment 2: Combinators to Lambda-terms

toLambda :: Combinator -> Term
toLambda (V x) = Variable x
toLambda I = Lambda "x" (Variable "x")
toLambda K = Lambda "x" (Lambda "y" (Variable "x"))
toLambda S = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "x")(Variable "z"))(Apply (Variable "y")(Variable "z")))))
toLambda B = Lambda "x" (Lambda "y" (Lambda "z" (Apply (Variable "x") (Apply (Variable "y")(Variable "z")))))
toLambda C = Lambda "x" (Lambda "y" (Lambda "z" (Apply(Apply (Variable "x")(Variable "z"))(Variable "y"))))
toLambda Q = Lambda "u" (Lambda "x" (Lambda "y" (Apply (Variable "u")(Variable "x"))))
toLambda R = Lambda "u" (Lambda "v" (Lambda "x" (Lambda "y" (Apply (Apply (Variable "u")(Variable "v"))(Variable "x")))))
toLambda X = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u")(Variable "x"))(Apply (Variable "y")(Variable "z"))))))
toLambda Y = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u")(Apply (Variable "x")(Variable "z")))(Variable "y")))))
toLambda Z = Lambda "u" (Lambda "x" (Lambda "y" (Lambda "z" (Apply (Apply (Variable "u")(Apply (Variable "x")(Variable "z")))(Apply (Variable "y")(Variable "z"))))))
toLambda (t1 :@ t2) = Apply (toLambda t1) (toLambda t2)


------------------------- Assignment 3: Lambda-terms to Combinators

abstract :: Var -> Combinator -> Combinator
abstract x (V v) 
  | x == v = I
  | otherwise  = K :@ (V v)
abstract x (c :@ d) = S :@ abstract x c :@ abstract x d
abstract x c = K :@ c

toCombinator :: Term -> Combinator
toCombinator (Variable x) = V x
toCombinator (Lambda x m) = abstract x (toCombinator m)
toCombinator (Apply m n) = toCombinator m :@ toCombinator n

------------------------- Assignment 4: Estimating growth

sizeL :: Term -> Int
sizeL (Variable _)   = 1
sizeL (Lambda _ m) = 1 + sizeL m
sizeL (Apply m n) = 1 + sizeL m + sizeL n

sizeC :: Combinator -> Int
sizeC (x :@ y) = 1 + sizeC x + sizeC y
sizeC _ = 1

series :: Int -> Term
series 0 = Lambda "a" (Variable "a")
series n = Lambda ("a" ++ show n) (Apply (series (n-1)) (Variable ("a" ++ show n)))

------------------------- Assignment 5: Optimised interpretation

data Complexity = Linear | Quadratic | Cubic | Exponential

{-
Implementation of J abstraction function inspired from the paper "Efficient combinator code"
Reference: Joy, M.S., Rayward-Smith, V.J. and Burton, F.W., 1985. Efficient combinator code. Computer Languages [Online], 10(3–4), pp.211–224. Available from: https://doi.org/10.1016/0096-0551(85)90017-7 [Accessed 1 May 2023].

-- guide: \oc = notfreevariables, oc = freevariables, atom = not made of two combinators, no variables = K

-}

novariable :: Combinator -> Bool 
novariable (V v) = False
novariable (m :@ n) = novariable m && novariable n
novariable _ = True

freevariables :: Term -> [Var]
freevariables (Variable x) = [x]
freevariables (Lambda x m) = filter (/= x) (freevariables m)
freevariables (Apply m n) = nub (freevariables m ++ freevariables n)

abstraction :: Var -> Combinator -> Combinator
abstraction x (V v) 
  | x == v = I
  | otherwise  = Q :@ I :@ (V v)
abstraction x (k :@ m :@ n)
  | novariable k && x `elem` freevariables (toLambda m) && x `elem` freevariables (toLambda n) = Z :@ k :@ abstraction x m :@ abstraction x n
  | novariable k && x `elem` freevariables (toLambda m) && x `notElem` freevariables (toLambda n) = Y :@ k :@ abstraction x m :@ n 
  | novariable k && x `notElem` freevariables (toLambda m) && x `elem` freevariables (toLambda n) = X :@ k :@ m :@ abstraction x n
  | novariable k && x `notElem` freevariables (toLambda m) && x `notElem` freevariables (toLambda n) = R :@ k :@ m :@ n
abstraction x ((k :@ m1) :@ n)
  | novariable k = Q :@ I :@ (k :@ m1) :@ n
  | not (novariable k) && x `elem` freevariables (toLambda (k :@ m1)) && x `elem` freevariables (toLambda n) = S :@ abstraction x (k :@ m1) :@ abstraction x n
  | not (novariable k) && x `elem` freevariables (toLambda (k :@ m1)) && x `notElem` freevariables (toLambda n) = C :@ abstraction x (k :@ m1) :@ n
  | not (novariable k) && x `notElem` freevariables (toLambda (k :@ m1)) && x `elem` freevariables (toLambda n) = B :@ (k :@ m1) :@ abstraction x n
  | not (novariable k) && x `notElem` freevariables (toLambda (k :@ m1)) && x `notElem` freevariables (toLambda n) = Q :@ (k :@ m1) :@ n
abstraction x (m :@ n)
  | x `elem` freevariables (toLambda m) && x `elem` freevariables (toLambda n) = S :@ abstraction x m :@ abstraction x n
  | x `elem` freevariables (toLambda m) && x `notElem` freevariables (toLambda n) = C :@ abstraction x m :@ n
  | x `notElem` freevariables (toLambda m) && x `elem` freevariables (toLambda n) = B :@ m :@ abstraction x n
  | x `notElem` freevariables (toLambda m) && x `notElem` freevariables (toLambda n) = Q :@ m :@ n
abstraction x m = Q :@ I :@ m

comb :: Term -> Combinator
comb (Variable x) = V x
comb (Lambda x m) = abstraction x (comb m)
comb (Apply m n) = comb m :@ comb n

claim :: Complexity
claim = Quadratic

