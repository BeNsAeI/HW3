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

{- (b) Define a type checker for the shape language that assigns
       types only to rectangular shapes -}

rect :: Shape -> Maybe BBox
rect X = Just (1, 1)
rect (TD a b) =            -- widths must match, and bbox has that width and 
    case rect a of         -- its height is sum of heights. Else Nothing.
        Nothing -> Nothing
        Just (ax, ay) -> case rect b of 
                         Nothing -> Nothing
                         Just (bx, by) -> case (ax == bx) of
                                          True -> Just (ax, ay + by)
                                          False -> Nothing
rect (LR a b) =            -- heights must match, and bbox is that height
    case rect a of         -- with width the sum of widths. Else Nothing.
        Nothing -> Nothing
        Just (ax, ay) -> case rect b of 
                         Nothing -> Nothing
                         Just (bx, by) -> case (ay == by) of
                                          True -> Just (ax + bx, ay)
                                          False -> Nothing

-- Test Shapes
r1 = TD (LR X X) (LR X X) -- bbox (2,2), rect Just (2,2)
r2 = TD (LR X X) X -- bbox (2,2), rect Nothing
r3 = LR (TD r1 X) (LR r2 r2) -- bbox (6, 3), rect Nothing
r4 = LR (TD r1 r1) (TD r1 r1) -- bbox (4, 4), rect Nothing
r5 = LR r4 r4 -- bbox (8, 4), rect Just (8, 4)


{---------------------------------------------------------------------------------------------------}
{-Q3-}
{-

(a) Consider the functions f and g, which are given by the
    following two function definitions.  

f x y = if null x then [y] else x
g x y = if not (null x) then [] else [y]

(1) What are the types of f and g?
       f :: [a] -> a -> [a]
       g :: [a] -> b -> [b]

   (2) Explain why the functions have these types.
       Since f will return either [y] or x, and x is a list, the elements
       of x have to be of the same type as y. This is because, to the
       best of our knowledge) Haskell can't return two different types
       from a function.

       While similar to f, g will return either [] or [y]. The subtle
       difference here is that y now has no relation to x, since a list
       is a phantom type. This make Haskell assume the second argument
       to g is not the same type as the first.

   (3) Which type is more general?
       Because both f and g will work with any types they are both
       general, but one could make the argument that because g works
       with more than one type, it is more general.

   (4) Why do f and g have different types?
       f and g have different types because of the magic of Haskell type
       inference.



(b) Find a (simple) definition for a function h that has the
      following type.

h :: [b] -> [(a, b)] -> [b]
h b _ = b


(c) Find a (simple) definition for a function k that has the 
       following type.

   k :: (a -> b) -> ((a -> b) -> a) -> b

   We can not find a (simple) definition for function k, as there is no
   way in Haskell to pattern match a function and its parameters at the
   same time. Also since the function signature only defines b in the
   terms of being the return type of another function, we can not deduce
   anything about how b should be represented.

  (d) Can you define a function of type a -> b?
      If yes, explain your definition. If not, explain why it is
      so difficult.

      No. Defining a function of type a -> b requires knowing something
      about type b. Since we don't have that knowledge, we can not
      define how something of type b should be represented. Anything we
      might use would end up restricting what b might be, thus it would
      not be of any type.

      We could write:
          j :: a -> b
          j = j

      But this is a circular definition and will never terminate, thus
      we have not truly defined anything at all.

-}
