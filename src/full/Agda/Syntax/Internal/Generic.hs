
-- | Tree traversal for internal syntax.

module Agda.Syntax.Internal.Generic where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Utils.Functor
import Agda.Utils.List1 (List1)

-- | Generic term traversal.
--
--   Note: ignores sorts in terms!
--   (Does not traverse into or collect from them.)

class TermLike a where

  -- | Generic traversal with post-traversal action.
  --   Ignores sorts.
  traverseTermM :: Monad m => (Term -> m Term) -> a -> m a

  default traverseTermM :: (Monad m, Traversable f, TermLike b, f b ~ a)
                        => (Term -> m Term) -> a -> m a
  traverseTermM = traverse . traverseTermM

  -- | Generic fold, ignoring sorts.
  foldTerm :: Monoid m => (Term -> m) -> a -> m

  default foldTerm
    :: (Monoid m, Foldable f, TermLike b, f b ~ a) => (Term -> m) -> a -> m
  foldTerm = foldMap . foldTerm

-- Constants

instance TermLike Bool where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike Int where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike Integer where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike Char where
  traverseTermM _ = pure
  foldTerm _      = mempty

instance TermLike QName where
  traverseTermM _ = pure
  foldTerm _      = mempty

-- Functors

instance TermLike a => TermLike (Elim' a)      where
instance TermLike a => TermLike (Arg a)        where
instance TermLike a => TermLike (Dom a)        where
instance TermLike a => TermLike [a]            where
instance TermLike a => TermLike (List1 a)      where
instance TermLike a => TermLike (Maybe a)      where
instance TermLike a => TermLike (Blocked a)    where
instance TermLike a => TermLike (Abs a)        where
instance TermLike a => TermLike (Tele a)       where
instance TermLike a => TermLike (WithHiding a) where

-- Tuples

instance (TermLike a, TermLike b) => TermLike (a, b) where
  traverseTermM f (x, y) = (,) <$> traverseTermM f x <*> traverseTermM f y
  foldTerm f (x, y) = foldTerm f x `mappend` foldTerm f y

instance (TermLike a, TermLike b, TermLike c) => TermLike (a, b, c) where
  traverseTermM f (x, y, z) = (,,) <$> traverseTermM f x <*> traverseTermM f y <*> traverseTermM f z
  foldTerm f (x, y, z) = mconcat [foldTerm f x, foldTerm f y, foldTerm f z]

instance (TermLike a, TermLike b, TermLike c, TermLike d) => TermLike (a, b, c, d) where
  traverseTermM f (x, y, z, u) = (,,,) <$> traverseTermM f x <*> traverseTermM f y <*> traverseTermM f z <*> traverseTermM f u
  foldTerm f (x, y, z, u) = mconcat [foldTerm f x, foldTerm f y, foldTerm f z, foldTerm f u]

-- Real terms

instance TermLike Term where

  traverseTermM f = \case
    Var i xs    -> f =<< Var i <$> traverseTermM f xs
    Def c xs    -> f =<< Def c <$> traverseTermM f xs
    Con c ci xs -> f =<< Con c ci <$> traverseTermM f xs
    Lam h b     -> f =<< Lam h <$> traverseTermM f b
    Pi a b      -> f =<< uncurry Pi <$> traverseTermM f (a, b)
    MetaV m xs  -> f =<< MetaV m <$> traverseTermM f xs
    Level l     -> f =<< Level <$> traverseTermM f l
    t@Lit{}     -> f t
    Sort s      -> f =<< Sort <$> traverseTermM f s
    DontCare mv -> f =<< DontCare <$> traverseTermM f mv
    Dummy s xs  -> f =<< Dummy s <$> traverseTermM f xs

  foldTerm f t = f t `mappend` case t of
    Var i xs    -> foldTerm f xs
    Def c xs    -> foldTerm f xs
    Con c ci xs -> foldTerm f xs
    Lam h b     -> foldTerm f b
    Pi a b      -> foldTerm f (a, b)
    MetaV m xs  -> foldTerm f xs
    Level l     -> foldTerm f l
    Lit _       -> mempty
    Sort s      -> foldTerm f s
    DontCare mv -> foldTerm f mv
    Dummy _ xs  -> foldTerm f xs

instance TermLike Level where
  traverseTermM f (Max n as) = Max n <$> traverseTermM f as
  foldTerm f      (Max n as) = foldTerm f as

instance TermLike PlusLevel where
  traverseTermM f (Plus n l) = Plus n <$> traverseTermM f l
  foldTerm f (Plus _ l)      = foldTerm f l

instance TermLike Type where
  traverseTermM f (El s t) = El s <$> traverseTermM f t
  foldTerm f (El s t) = foldTerm f t

instance TermLike Sort where
  traverseTermM f = \case
    Univ u l   -> Univ u <$> traverseTermM f l
    s@(Inf _ _)-> pure s
    s@SizeUniv -> pure s
    s@LockUniv -> pure s
    s@LevelUniv -> pure s
    s@IntervalUniv -> pure s
    PiSort a b c -> PiSort   <$> traverseTermM f a <*> traverseTermM f b <*> traverseTermM f c
    FunSort a b -> FunSort   <$> traverseTermM f a <*> traverseTermM f b
    UnivSort a -> UnivSort <$> traverseTermM f a
    MetaS x es -> MetaS x  <$> traverseTermM f es
    DefS q es  -> DefS q   <$> traverseTermM f es
    s@(DummyS _) -> pure s

  foldTerm f = \case
    Univ _ l   -> foldTerm f l
    Inf _ _    -> mempty
    SizeUniv   -> mempty
    LockUniv   -> mempty
    LevelUniv  -> mempty
    IntervalUniv -> mempty
    PiSort a b c -> foldTerm f a <> foldTerm f b <> foldTerm f c
    FunSort a b -> foldTerm f a <> foldTerm f b
    UnivSort a -> foldTerm f a
    MetaS _ es -> foldTerm f es
    DefS _ es  -> foldTerm f es
    DummyS _   -> mempty

instance TermLike EqualityView where

  traverseTermM f = \case
    OtherType t -> OtherType
      <$> traverseTermM f t
    IdiomType t -> IdiomType
      <$> traverseTermM f t
    EqualityType r s eq l t a b -> EqualityType r s eq
      <$> traverse (traverseTermM f) l
      <*> traverseTermM f t
      <*> traverseTermM f a
      <*> traverseTermM f b

  foldTerm f = \case
    OtherType t -> foldTerm f t
    IdiomType t -> foldTerm f t
    EqualityType _r _s _eq l t a b -> foldTerm f (l ++ [t, a, b])

-- | Put it in a monad to make it possible to do strictly.
copyTerm :: (TermLike a, Monad m) => a -> m a
copyTerm = traverseTermM return
