{- 
- Behnam Saeedi
- Saeedib
- 932217697
- Homework 3
- Types
- Due 5/12/2016
-}

module HW3 where

{-Q1-a-}

{-Code provided by the assignment:-}
type Prog = [Cmd]
data Cmd = LD Int
         | ADD
         | MULT
         | DUP
         | INC
         | SWAP
         | POP Int
           deriving Show




{-Declearing the stack and double stack shortcut-}
type Stack = [Int]
type DblStk = Stack -> Stack

type Rank = Int
type CmdRank = (Int, Int)


{-semCmd:-}
semCmd :: Cmd -> DblStk
semCmd (LD x)  list         = [x] ++ list        {-LD adds the element x to the front of List-}
semCmd (ADD) (x0:x1:list)   = [x0+x1] ++ list    {-add puts the result of addition of the two top elements in the stackk to the top of the stack-}
semCmd (MULT) (x0:x1:list)  = [x0*x1] ++ list    {-add puts the result of multiplication of the two top elements in the stackk to the top of the stack-}
semCmd (DUP) (x0:list)      = [x0,x0] ++ list    {-Duplicates the first element of the list (note, since the list variable does not include the the x0 we need it again)-}
semCmd (INC) (x0:list)      = [succ x0] ++ list  {-increment the top by one and then add it to the list-}
semCmd (SWAP) (x0:x1:list)  = (x1:x0:list)       {-swap , swaps the two first elements of the list-}
semCmd (POP x) list         = drop x list        {-drop function removes an element from a list-}
semCmd _       _          = []                   {-Epty list for everything else-}



{-Sementics:-}
sem :: Prog -> DblStk
sem [] x = x
sem (fst:list) x = sem list (semCmd fst x)

{-Ranks:-}
rankC :: Cmd -> CmdRank
rankC (LD _)  = (0, 1)
rankC ADD     = (2, 1)
rankC MULT    = (2, 1)
rankC DUP     = (1, 2)
rankC INC     = (1, 1)
rankC SWAP    = (2, 2)
rankC (POP x) = (x, 0)

{-This code is provided in the assignment:-}
rankP :: Prog -> Maybe Rank
rankP list = rank list 0

{-Program raniking:-}
type RnkType = Prog -> Rank -> Maybe Rank
rank :: RnkType
rank []     x | x >= 0            = Just x
rank (fst:list) x | eq >= 0 = rank list (eq + additions)
              where (subtracts, additions) = rankC fst
                    eq        = x - subtracts
rank _ _                         = Nothing


{---------------------------}
{-Q1-b-}
{-Defining our type-}
data Type = A Stack | TypeError deriving Show


typeSafe :: Prog -> Bool
typeSafe p = (rankP p) /= Nothing

{-We process only if the type is safe otherwise we will return a type error similar to the example-}
semStatTC :: Prog -> Type
semStatTC x | typeSafe x = A (sem x [])
            | otherwise  = TypeError

{-
What is the new type of the function sem and why can the function definition be simplified to have this type?

-> The type of sem as we stated in the code above is Prog -> DblStk where DblStk is Stack -> Stack. Thereofre,
type of sem is: Prog -> Stack -> Stack
since we have a type checker , we do not need to worry about Maybe type anymore (it is taken care of by the typechecker)
-}

{---------------------------------------------------------------------------------------------------}
{-Q2-}

{-This code is provided in the assignment:-}
data Shape = X
           | TD Shape Shape
           | LR Shape Shape
           deriving Show

       {-(Width, Height)-}
type BBox = (Int, Int)

{---------------------------}
{-Q2-a-}
bbox :: Shape -> BBox
bbox (TD a b) | ax >= bx  = (ax, ay + by) {-TD adds the heights (because it is top to down, in this case bigger changes-}
              | ax < bx   = (bx, ay + by)  {-same as last one except if the b is the bigger box in length-}
                             where (ax, ay) = bbox a
                                   (bx, by) = bbox b
bbox (LR a b) | ay >= by  = (ax + bx, ay)
              | ay < by   = (ax + bx, by)
                             where (ax, ay) = bbox a
                                   (bx, by) = bbox b
bbox X = (1, 1)

{-Q2-b-}

rect :: Shape -> Maybe BBox
rect X = Just (1, 1)
rect (TD a b) = case rect a of Nothing -> Nothing
                               Just (ax, ay) -> case rect b of Nothing -> Nothing
                                                               Just (bx, by) -> case (ax == bx) of True -> Just (ax, ay + by) {-Similar to the definition above-}
                                                                                                   False -> Nothing
rect (LR a b) = case rect a of Nothing -> Nothing
                               Just (ax, ay) -> case rect b of Nothing -> Nothing
                                                               Just (bx, by) -> case (ay == by) of True -> Just (ax + bx, ay) {-Similar to the definition above-}
                                                                                                   False -> Nothing

{---------------------------------------------------------------------------------------------------}
{-Q3-}
{-

{-Q3-a-}
(1) 
   f::[a] -> a -> [a] 
   g::[a] -> b -> [b]

(2)
         f takes a list of values x and a value y of type a and return a list x or [y] (which have
	to have the same type for the code to be correct since the return type needs to match)

         g also takes a list x and any time y (we don't know what the y type is since it is not used)
	and returns a list (empty or [y]) of same type (type of y) (emty list can be of any type)

(3) Both type are general enough since they don't specify a specific type however there are two arguments here:
    1- f could be more general because it has no restriction on the input and both x and y can be of any type as
	   long as their type matches

	2- g could be the more general function because it mentions types a and b whcih means at a given code it 
	   supports more than 1 type

(4) Haskell type inference
    according to Haskell: (This contex is taken directly from Haskell website)

**** Type inference is a feature of the type system which means that concrete types are deduced by the type system
      whereever it is obvious.

	  it means if we add a variable of type x to a literal y, the type system concludes that variable similar to that
	  literal (y) could be represented with that specific literal's type (here x).
	  so if we see a number 10, and specify it as an Int, everytime we use 10 it automatically assumes it is an Int
	  (well 10 could be of ther types to , so haskell picks one that fits the type definition)


{---------------------------}
{-Q3-b-} 

h :: [b] -> [(a, b)] -> [b]
h x _ = x
OR
h x (fst:list) = x
h x [] = x


{---------------------------}
{-Q3-c-}

   k :: (a -> b) -> ((a -> b) -> a) -> b

   We can't. Such a definition cannot exist in Haskell.
        Here, we are trying to match the parameter's pattern in whle we are also trying to match the pattern of
   the function. Haskell, needs to know the parameter's pattern before hand.

        Now lets assume that the parameters are alread handled, there still isn't a way for us to properly represent
   the output of type b or ((a->b)->a)->b assuming one of which should be the output type.


{---------------------------}
{-Q3-d-}

No, there isn't a way for us to know what type b will contain. so there isn not a way for us to represent b.
There is a way for us to cheat however,
lets assume that type endlessLoopOfDeath has this propertye:
endlessLoopOfDeath :: a -> b

then we can simple create an endless loop of death (hence the name) that circles indefinitely

we can simply say:
endlessLoopOfDeath :: a -> b
endlessLoopOfDeath = endlessLoopOfDeath
 
-}
