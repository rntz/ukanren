{-# LANGUAGE FlexibleInstances #-}
module MicroKanren where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Strict hiding (State)

import Data.Maybe (fromMaybe, mapMaybe)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM

type Var = Int

data Atom = Int Int
            deriving (Show, Eq, Ord)

data Term = V Var
          | A Atom
          | L [Term]
            deriving (Show, Eq, Ord)

type Subst = IntMap Term
type State = (Var, Subst)

--  A monad that can generate, bind, and look-up variables.
class Monad m => VarGen m where
    newVar :: m Var
    assign :: Var -> Term -> m ()
    deref :: Var -> m (Maybe Term)

-- Fair interleaving of finitely many lists.
interleaves :: [[a]] -> [a]
interleaves [] = []
interleaves l = [x | x:_ <- l] ++ interleaves [xs | _:xs <- l]

interleave a b = interleaves [a,b]


-- Search trees, so we can define the search algorithm separately.
data Tree a = Empty | Single a | Node (Tree a) (Tree a) deriving Show

instance Functor Tree where fmap = liftM
instance Applicative Tree where pure = return; (<*>) = ap
instance Monad Tree where
    return = Single
    Empty >>= _ = Empty
    Single x >>= f = f x
    Node l r >>= f = Node (l >>= f) (r >>= f)

-- NB. not a law-abiding Alternative/MonadPlus instance: not associative.
instance MonadPlus Tree where mzero = empty; mplus = (<|>)
instance Alternative Tree where empty = Empty; (<|>) = Node


-- Search strategies over Trees.
listify :: ([a] -> [a] -> [a]) -> Tree a -> [a]
listify f Empty = []
listify f (Single a) = [a]
listify f (Node l r) = f (listify f l) (listify f r)

dfs = listify (++)

-- Not sure if there's a standard name for this search strategy.
ifs = listify interleave

-- Unfortunately we can't write iterated deepening as a function on Trees,
-- because of Haskell's memoizing call-by-need evaluation. So we'll just do a
-- plain old memory-hogging BFS.
bfs t = search [] [t]
    -- we use the usual trick of encoding a queue as two stacks.
    where search [] [] = []
          search a [] = search [] (reverse a)
          search a (Empty : b) = search a b
          search a (Single x : b) = x : search a b
          search a (Node l r : b) = search (r:l:a) b


-- Implementation of the Kanren interface
type K = StateT State Tree
type Goal = K ()

instance Monad m => VarGen (StateT State m) where
    newVar = state (\(v,s) -> (v, (v+1, s)))
    assign v t = modify (fmap (IM.insert v t))
    deref v = gets (\(_,sub) -> IM.lookup v sub)

start :: State
start = (0, IM.empty)

runK :: K a -> State -> [(a, State)]
runK k st = bfs $ runStateT k st
-- NB. if we change bfs to ifs, then fivesR fails!
-- with dfs you get prolog-like behavior, and even more things fail.

evalK :: K a -> State -> [a]
evalK k st = map fst (runK k st)

execK :: K a -> State -> [State]
execK k st = map snd (runK k st)


-- Basic operators.
ok :: Goal
ok = pure ()

expand :: Term -> K Term
expand t@(V v) = fromMaybe t <$> deref v
expand t = return t

eq :: Term -> Term -> Goal
eq x y = join $ e <$> expand x <*> expand y
    where
      e (V x) (V y) | x == y = ok
      e (V x) t = assign x t
      e t (V x) = assign x t
      e (A x) (A y) | (x == y) = ok
      e (L xs) (L ys) | length xs == length ys = zipWithM_ eq xs ys
      e _ _ = mzero

disj, conj :: Goal -> Goal -> Goal
disj = (<|>)
conj = (>>)

-- equivalent of disj+, conj+
disjs, conjs :: [Goal] -> Goal
disjs = msum
conjs = sequence_


-- Convenience function: fresh
class Fresh a where fresh :: (a -> K b) -> K b
instance Fresh Var where fresh f = newVar >>= f
instance Fresh Term where fresh f = fresh (f . V)
instance (Fresh a, Fresh b) => Fresh (a,b) where
    fresh f = fresh (\a -> fresh (\b -> f (a,b)))
instance (Fresh a, Fresh b, Fresh c) => Fresh (a,b,c) where
    fresh f = fresh (\a -> fresh (\(b,c) -> f (a,b,c)))
instance (Fresh a, Fresh b, Fresh c, Fresh d) => Fresh (a,b,c,d) where
    fresh f = fresh (\(a,b) -> fresh (\(c,d) -> f (a,b,c,d)))
instance (Fresh a, Fresh b, Fresh c, Fresh d, Fresh e) => Fresh (a,b,c,d,e)where
    fresh f = fresh (\(a,b,c) -> fresh (\(d,e) -> f (a,b,c,d,e)))


-- Test cases
five :: Goal
five = fresh (\x -> eq x (A (Int 5)))

fives_ x = eq x (A (Int 5)) <|> fives_ x
fives = fresh fives_

fivesR_ x = fivesR_ x <|> eq x (A (Int 5))
fivesR = fresh fivesR_

aAndB = do fresh $ \a -> eq a (A (Int 7))
           fresh $ \b -> eq b (A (Int 5)) <|> eq b (A (Int 6))

test t = take 10 $ runK t start
