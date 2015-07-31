-- | An implementation of Tarjan's UNION-FIND algorithm.  (Robert E
-- Tarjan. \"Efficiency of a Good But Not Linear Set Union Algorithm\", JACM
-- 22(2), 1975)
--
-- The algorithm implements three operations efficiently (all amortised
-- @O(1)@):
--
--  1. Check whether two elements are in the same equivalence class.
--
--  2. Create a union of two equivalence classes.
--
--  3. Look up the descriptor of the equivalence class.
-- 
-- The implementation is based on mutable references.  Each
-- equivalence class has exactly one member that serves as its
-- representative element.  Every element either is the representative
-- element of its equivalence class or points to another element in
-- the same equivalence class.  Equivalence testing thus consists of
-- following the pointers to the representative elements and then
-- comparing these for identity.
--
-- The algorithm performs lazy path compression.  That is, whenever we
-- walk along a path greater than length 1 we automatically update the
-- pointers along the path to directly point to the representative
-- element.  Consequently future lookups will be have a path length of
-- at most 1.
--
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
module Data.UnionFind.ZoneRef
  ( Point, fresh, repr, union, union', equivalent, redundant,
    descriptor, setDescriptor, modifyDescriptor )
where

-- import Control.Applicative
import Control.DeepSeq (NFData)
import Control.Monad ( when )
import Control.Monad.ST (ST)
import RefZone

-- | The abstract type of an element of the sets we work on.  It is
-- parameterised over the type of the descriptor.
newtype Point a = Pt (Ref (Link a)) deriving (Eq, NFData)

data Link a
    = Info {-# UNPACK #-} !(Ref (Info a))
      -- ^ This is the descriptive element of the equivalence class.
    | Link {-# UNPACK #-} !(Point a)
      -- ^ Pointer to some other element of the equivalence class.
     deriving Eq

data Info a = MkInfo
  { weight :: {-# UNPACK #-} !Int
    -- ^ The size of the equivalence class, used by 'union'.
  , descr  :: a
  } deriving Eq

-- | /O(1)/. Create a fresh point and return it.  A fresh point is in
-- the equivalence class that contains only itself.
fresh :: Zone s -> a -> ST s (Point a)
fresh zone desc = do
  info <- newRef zone (MkInfo { weight = 1, descr = desc })
  l <- newRef zone (Info info)
  return (Pt l)

-- | /O(1)/. @repr point@ returns the representative point of
-- @point@'s equivalence class.
--
-- This method performs the path compresssion.
repr :: Zone s -> Point a -> ST s (Point a)
repr zone point@(Pt l) = do
  link <- readRef zone l
  case link of
    Info _ -> return point
    Link pt'@(Pt l') -> do
      pt'' <- repr zone pt'
      when (pt'' /= pt') $ do
        -- At this point we know that @pt'@ is not the representative
        -- element of @point@'s equivalent class.  Therefore @pt'@'s
        -- link must be of the form @Link r@.  We write this same
        -- value into @point@'s link reference and thereby perform
        -- path compression.
        link' <- readRef zone l'
        writeRef zone l link'
      return pt''

-- | Return the reference to the point's equivalence class's
-- descriptor.
descrRef :: Zone s -> Point a -> ST s (Ref (Info a))
descrRef zone point@(Pt link_ref) = do
  link <- readRef zone link_ref
  case link of
    Info info -> return info
    Link (Pt link'_ref) -> do
      link' <- readRef zone link'_ref
      case link' of
        Info info -> return info
        _ -> descrRef zone =<< repr zone point

-- | /O(1)/. Return the descriptor associated with argument point's
-- equivalence class.
descriptor :: Zone s -> Point a -> ST s a
descriptor zone point = do
  descr <$> (readRef zone =<< descrRef zone point)

-- | /O(1)/. Replace the descriptor of the point's equivalence class
-- with the second argument.
setDescriptor :: Zone s -> Point a -> a -> ST s ()
setDescriptor zone point new_descr = do
  r <- descrRef zone point
  modifyRef zone r $ \i -> i { descr = new_descr }

modifyDescriptor :: Zone s -> Point a -> (a -> a) -> ST s ()
modifyDescriptor zone point f = do
  r <- descrRef zone point
  modifyRef zone r $ \i -> i { descr = f (descr i) }

-- | /O(1)/. Join the equivalence classes of the points (which must be
-- distinct).  The resulting equivalence class will get the descriptor
-- of the second argument.
union :: Zone s -> Point a -> Point a -> ST s ()
union zone p1 p2 = union' zone p1 p2 (\_ d2 -> return d2)

-- | Like 'union', but sets the descriptor returned from the callback.
-- 
-- The intention is to keep the descriptor of the second argument to
-- the callback, but the callback might adjust the information of the
-- descriptor or perform side effects.
union' :: Zone s -> Point a -> Point a -> (a -> a -> ST s a) -> ST s ()
union' zone p1 p2 update = do
  point1@(Pt link_ref1) <- repr zone p1
  point2@(Pt link_ref2) <- repr zone p2
  -- The precondition ensures that we don't create cyclic structures.
  when (point1 /= point2) $ do
    Info info_ref1 <- readRef zone link_ref1
    Info info_ref2 <- readRef zone link_ref2
    MkInfo w1 d1 <- readRef zone info_ref1 -- d1 is discarded
    MkInfo w2 d2 <- readRef zone info_ref2
    d2' <- update d1 d2
    -- Make the smaller tree a a subtree of the bigger one.  The idea
    -- is this: We increase the path length of one set by one.
    -- Assuming all elements are accessed equally often, this means
    -- the penalty is smaller if we do it for the smaller set of the
    -- two.
    if w1 >= w2 then do
      writeRef zone link_ref2 (Link point1)
      writeRef zone info_ref1 (MkInfo (w1 + w2) d2')
     else do
      writeRef zone link_ref1 (Link point2)
      writeRef zone info_ref2 (MkInfo (w1 + w2) d2')

-- | /O(1)/. Return @True@ if both points belong to the same
-- | equivalence class.
equivalent :: Zone s -> Point a -> Point a -> ST s Bool
equivalent zone p1 p2 = (==) <$> repr zone p1 <*> repr zone p2

-- | /O(1)/. Returns @True@ for all but one element of an equivalence
-- class.  That is, if @ps = [p1, .., pn]@ are all in the same
-- equivalence class, then the following assertion holds.
-- 
-- > do rs <- mapM redundant ps
-- >    assert (length (filter (==False) rs) == 1)
-- 
-- It is unspecified for which element function returns @False@, so be
-- really careful when using this.
redundant :: Zone s -> Point a -> ST s Bool
redundant zone (Pt link_r) = do
  link <- readRef zone link_r
  case link of
    Info _ -> return False
    Link _ -> return True
