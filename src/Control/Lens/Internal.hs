{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MagicHash #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 704
{-# LANGUAGE Trustworthy #-}
#endif

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Lens.Internal
-- Copyright   :  (C) 2012 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types
--
-- These are some of the explicit Functor instances that leak into the
-- type signatures of Control.Lens. You shouldn't need to import this
-- module directly, unless you are coming up with a whole new kind of
-- \"Family\" and need to add instances.
--
----------------------------------------------------------------------------
module Control.Lens.Internal where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Category
import Control.Comonad
import Control.Comonad.Store.Class
import Control.Lens.Isomorphic
import Control.Monad
import Prelude hiding ((.),id)
import Data.Foldable
import Data.Functor.Compose
import Data.Functor.Identity
import Data.List.NonEmpty as NonEmpty
import Data.Maybe
import Data.Monoid
import Data.Traversable
import Unsafe.Coerce

-- | Logically this function is a more strict form of function application.
--
-- Ideally this function is
--
-- @f # g = f `seq` g `seq` \x -> f (g x)@
--
-- This fixes pedantic issues with the strictness of functions. (See issue #75)

infixr 9 #
(#) :: (b -> c) -> (a -> b) -> a -> c
f # g = f `seq` g `seq` \x -> f (g x)
{-# NOINLINE (#) #-}

{-# RULES "Const#"          (#) Const          = unsafeCoerce #-}
{-# RULES "getConst#"       (#) getConst       = unsafeCoerce #-}

const# :: (a -> b) -> a -> Const b r
const# = unsafeCoerce

getConst# :: (a -> Const b r) -> a -> b
getConst# = unsafeCoerce

{-# RULES "ZipList#"        (#) ZipList        = unsafeCoerce #-}
{-# RULES "getZipList#"     (#) getZipList     = unsafeCoerce #-}

zipList# :: (a -> [b]) -> a -> ZipList b
zipList# = unsafeCoerce

getZipList# :: (a -> ZipList b) -> a -> [b]
getZipList# = unsafeCoerce

{-# RULES "WrapMonad#"      (#) WrapMonad      = unsafeCoerce #-}
{-# RULES "unwrapMonad#"    (#) unwrapMonad    = unsafeCoerce #-}
wrapMonad# :: (a -> m b) -> a -> WrappedMonad m b
wrapMonad# = unsafeCoerce

unwrapMonad# :: (a -> WrappedMonad m b) -> a -> m b
unwrapMonad# = unsafeCoerce

{-# RULES "Last#"           (#) Last           = unsafeCoerce #-}
{-# RULES "getLast#"        (#) getLast        = unsafeCoerce #-}

last# :: (a -> Maybe b) -> a -> Last b
last# = unsafeCoerce

getLast# :: (a -> Last b) -> a -> Maybe b
getLast# = unsafeCoerce

{-# RULES "First#"          (#) First          = unsafeCoerce #-}
{-# RULES "getFirst#"       (#) getFirst       = unsafeCoerce #-}

first# :: (a -> Maybe b) -> a -> First b
first# = unsafeCoerce

getFirst# :: (a -> First b) -> a -> Maybe b
getFirst# = unsafeCoerce

{-# RULES "Product#"        (#) Product        = unsafeCoerce #-}
{-# RULES "getProduct#"     (#) getProduct     = unsafeCoerce #-}

product# :: (a -> b) -> a -> Product b
product# = unsafeCoerce

getProduct# :: (a -> Product b) -> a -> b
getProduct# = unsafeCoerce

{-# RULES "Sum#"            (#) Sum            = unsafeCoerce #-}
{-# RULES "getSum#"         (#) getSum         = unsafeCoerce #-}

sum# :: (a -> b) -> a -> Sum b
sum# = unsafeCoerce

getSum# :: (a -> Sum b) -> a -> b
getSum# = unsafeCoerce

{-# RULES "Any#"            (#) Any            = unsafeCoerce #-}
{-# RULES "getAny#"         (#) getAny         = unsafeCoerce #-}

any# :: (a -> Bool) -> a -> Any
any# = unsafeCoerce

getAny# :: (a -> Any) -> a -> Bool
getAny# = unsafeCoerce

{-# RULES "All#"            (#) All            = unsafeCoerce #-}
{-# RULES "getAll#"         (#) getAll         = unsafeCoerce #-}

all# :: (a -> Bool) -> a -> All
all# = unsafeCoerce

getAll# :: (a -> All) -> a -> Bool
getAll# = unsafeCoerce

{-# RULES "Dual#"           (#) Dual           = unsafeCoerce #-}
{-# RULES "getDual#"        (#) getDual        = unsafeCoerce #-}

dual# :: (a -> b) -> a -> Dual b
dual# = unsafeCoerce

getDual# :: (a -> Dual b) -> a -> b
getDual# = unsafeCoerce

{-# RULES "Endo#"           (#) Endo           = unsafeCoerce #-}
{-# RULES "appEndo#"        (#) appEndo        = unsafeCoerce #-}

endo# :: (a -> b -> b) -> a -> Endo b
endo# = unsafeCoerce

appEndo# :: (a -> Endo b) -> a -> b -> b
appEndo# = unsafeCoerce

{-# RULES "May#"            (#) May            = unsafeCoerce #-}
{-# RULES "getMay#"         (#) getMay         = unsafeCoerce #-}

may# :: (a -> Maybe b) -> a -> May b
may# = unsafeCoerce

getMay# :: (a -> May b) -> a -> Maybe b
getMay# = unsafeCoerce

{-# RULES "Folding#"        (#) Folding        = unsafeCoerce #-}
{-# RULES "getFolding#"     (#) getFolding     = unsafeCoerce #-}

folding# :: (a -> f b) -> a -> Folding f b
folding# = unsafeCoerce

getFolding# :: (a -> Folding f b) -> a -> f b
getFolding# = unsafeCoerce

{-# RULES "Effect#"         (#) Effect         = unsafeCoerce #-}
{-# RULES "getEffect#"      (#) getEffect      = unsafeCoerce #-}

effect# :: (a -> m r) -> a -> Effect m r b
effect# = unsafeCoerce

getEffect# :: (a -> Effect m r b) -> a -> m r
getEffect# = unsafeCoerce

{-# RULES "EffectRWS#"      (#) EffectRWS      = unsafeCoerce #-}
{-# RULES "getEffectRWS#"   (#) getEffectRWS   = unsafeCoerce #-}

effectRWS# :: (a -> st -> m (s, st, w)) -> a -> EffectRWS w st m s b
effectRWS# = unsafeCoerce

getEffectRWS# :: (a -> EffectRWS w st m s b) -> a -> st -> m (s, st, w)
getEffectRWS# = unsafeCoerce

{-# RULES "Accessor#"       (#) Accessor       = unsafeCoerce #-}
{-# RULES "runAccessor#"    (#) runAccessor    = unsafeCoerce #-}

accessor# :: (a -> r) -> a -> Accessor r b
accessor# = unsafeCoerce

runAccessor# :: (a -> Accessor r b) -> a -> r
runAccessor# = unsafeCoerce

{-# RULES "Err#"            (#) Err            = unsafeCoerce #-}
{-# RULES "getErr#"         (#) getErr         = unsafeCoerce #-}

err# :: (a -> Either e b) -> a -> Err e b
err# = unsafeCoerce

getErr# :: (a -> Err e b) -> a -> Either e b
getErr# = unsafeCoerce

{-# RULES "Traversed#"      (#) Traversed      = unsafeCoerce #-}
{-# RULES "getTraversed#"   (#) getTraversed   = unsafeCoerce #-}

traversed# :: (a -> f ()) -> a -> Traversed f
traversed# = unsafeCoerce

getTraversed# :: (a -> Traversed f) -> a -> f ()
getTraversed# = unsafeCoerce

{-# RULES "Sequenced#"      (#) Sequenced      = unsafeCoerce #-}
{-# RULES "getSequenced#"   (#) getSequenced   = unsafeCoerce #-}

sequenced# :: (a -> f ()) -> a -> Sequenced f
sequenced# = unsafeCoerce

getSequenced# :: (a -> Sequenced f) -> a -> f ()
getSequenced# = unsafeCoerce

{-# RULES "Focusing#"       (#) Focusing       = unsafeCoerce #-}
{-# RULES "unfocusing#"     (#) unfocusing     = unsafeCoerce #-}

focusing# :: (a -> m (s, b)) -> a -> Focusing m s b
focusing# = unsafeCoerce

unfocusing# :: (a -> Focusing m s b) -> a -> m (s, b)
unfocusing# = unsafeCoerce

{-# RULES "FocusingWith#"   (#) FocusingWith   = unsafeCoerce #-}
{-# RULES "unfocusingWith#" (#) unfocusingWith = unsafeCoerce #-}

focusingWith# :: (a -> m (s, b, w)) -> a -> FocusingWith w m s b
focusingWith# = unsafeCoerce

unfocusingWith# :: (a -> FocusingWith w m s b) -> a -> m (s, b, w)
unfocusingWith# = unsafeCoerce

{-# RULES "FocusingPlus#"   (#) FocusingPlus   = unsafeCoerce #-}
{-# RULES "unfocusingPlus#" (#) unfocusingPlus = unsafeCoerce #-}

focusingPlus# :: (a -> k (s, w) b) -> a -> FocusingPlus w k s b
focusingPlus# = unsafeCoerce

unfocusingPlus# :: (a -> FocusingPlus w k s b) -> a -> k (s, w) b
unfocusingPlus# = unsafeCoerce

{-# RULES "FocusingOn#"     (#) FocusingOn     = unsafeCoerce #-}
{-# RULES "unfocusingOn#"   (#) unfocusingOn   = unsafeCoerce #-}

focusingOn# :: (a -> k (f s) b) -> a -> FocusingOn f k s b
focusingOn# = unsafeCoerce

unfocusingOn# :: (a -> FocusingOn f k s b) -> a -> k (f s) b
unfocusingOn# = unsafeCoerce

{-# RULES "FocusingMay#"    (#) FocusingMay    = unsafeCoerce #-}
{-# RULES "unfocusingMay#"  (#) unfocusingMay  = unsafeCoerce #-}

focusingMay# :: (a -> k (May s) b) -> a -> FocusingMay k s b
focusingMay# = unsafeCoerce

unfocusingMay# :: (a -> FocusingMay k s b) -> a -> k (May s) b
unfocusingMay# = unsafeCoerce

{-# RULES "FocusingErr#"    (#) FocusingErr    = unsafeCoerce #-}
{-# RULES "unfocusingErr#"  (#) unfocusingErr  = unsafeCoerce #-}

focusingErr# :: (a -> k (Err e s) b) -> a -> FocusingErr e k s b
focusingErr# = unsafeCoerce

unfocusingErr# :: (a -> FocusingErr e k s b) -> a -> k (Err e s) b
unfocusingErr# = unsafeCoerce

{-# RULES "Bazaar#"         (#) Bazaar         = unsafeCoerce #-}
{-# RULES "runBazaar#"      (#) runBazaar      = unsafeCoerce #-}

bazaar# :: (forall f. Applicative f => a -> (c -> f d) -> f t) -> a -> Bazaar c d t
bazaar# = unsafeCoerce

runBazaar# :: Applicative f => (a -> Bazaar c d t) -> a -> (c -> f d) -> f t
runBazaar# = unsafeCoerce

{-# RULES "Mutator#"        (#) Mutator        = unsafeCoerce #-}
{-# RULES "runMutator#"     (#) runMutator     = unsafeCoerce #-}

mutator# :: (a -> b) -> a -> Mutator b
mutator# = unsafeCoerce

runMutator# :: (a -> Mutator b) -> a -> b
runMutator# = unsafeCoerce

{-# RULES "Backwards#"      (#) Backwards      = unsafeCoerce #-}
{-# RULES "forwards#"       (#) forwards       = unsafeCoerce #-}

backwards# :: (a -> f b) -> a -> Backwards f b
backwards# = unsafeCoerce

forwards# :: (a -> Backwards f b) -> a -> f b
forwards# = unsafeCoerce

-----------------------------------------------------------------------------
-- Functors
-----------------------------------------------------------------------------

-- | Used by 'Control.Lens.Type.Zoom' to 'Control.Lens.Type.zoom' into 'Control.Monad.State.StateT'
newtype Focusing m s a = Focusing { unfocusing :: m (s, a) }

instance Monad m => Functor (Focusing m s) where
  fmap f (Focusing m) = Focusing $ do
     (s, a) <- m
     return (s, f a)

instance (Monad m, Monoid s) => Applicative (Focusing m s) where
  pure a = Focusing (return (mempty, a))
  Focusing mf <*> Focusing ma = Focusing $ do
    (s, f) <- mf
    (s', a) <- ma
    return (mappend s s', f a)

-- | Used by 'Control.Lens.Type.Zoom' to 'Control.Lens.Type.zoom' into 'Control.Monad.RWS.RWST'
newtype FocusingWith w m s a = FocusingWith { unfocusingWith :: m (s, a, w) }

instance Monad m => Functor (FocusingWith w m s) where
  fmap f (FocusingWith m) = FocusingWith $ do
     (s, a, w) <- m
     return (s, f a, w)

instance (Monad m, Monoid s, Monoid w) => Applicative (FocusingWith w m s) where
  pure a = FocusingWith (return (mempty, a, mempty))
  FocusingWith mf <*> FocusingWith ma = FocusingWith $ do
    (s, f, w) <- mf
    (s', a, w') <- ma
    return (mappend s s', f a, mappend w w')

-- | Used by 'Control.Lens.Type.Zoom' to 'Control.Lens.Type.zoom' into 'Control.Monad.Writer.WriterT'.
newtype FocusingPlus w k s a = FocusingPlus { unfocusingPlus :: k (s, w) a }

instance Functor (k (s, w)) => Functor (FocusingPlus w k s) where
  fmap f (FocusingPlus as) = FocusingPlus (fmap f as)

instance (Monoid w, Applicative (k (s, w))) => Applicative (FocusingPlus w k s) where
  pure = FocusingPlus . pure
  FocusingPlus kf <*> FocusingPlus ka = FocusingPlus (kf <*> ka)

-- | Used by 'Control.Lens.Type.Zoom' to 'Control.Lens.Type.zoom' into 'Control.Monad.Trans.Maybe.MaybeT' or 'Control.Monad.Trans.List.ListT'
newtype FocusingOn f k s a = FocusingOn { unfocusingOn :: k (f s) a }

instance Functor (k (f s)) => Functor (FocusingOn f k s) where
  fmap f (FocusingOn as) = FocusingOn (fmap f as)

instance Applicative (k (f s)) => Applicative (FocusingOn f k s) where
  pure = FocusingOn . pure
  FocusingOn kf <*> FocusingOn ka = FocusingOn (kf <*> ka)

-- | Make a monoid out of 'Maybe' for error handling
newtype May a = May { getMay :: Maybe a }

instance Monoid a => Monoid (May a) where
  mempty = May (Just mempty)
  May Nothing `mappend` _ = May Nothing
  _ `mappend` May Nothing = May Nothing
  May (Just a) `mappend` May (Just b) = May (Just (mappend a b))

-- | Used by 'Control.Lens.Type.Zoom' to 'Control.Lens.Type.zoom' into 'Control.Monad.Error.ErrorT'
newtype FocusingMay k s a = FocusingMay { unfocusingMay :: k (May s) a }

instance Functor (k (May s)) => Functor (FocusingMay k s) where
  fmap f (FocusingMay as) = FocusingMay (fmap f as)

instance Applicative (k (May s)) => Applicative (FocusingMay k s) where
  pure = FocusingMay . pure
  FocusingMay kf <*> FocusingMay ka = FocusingMay (kf <*> ka)

-- | Make a monoid out of 'Either' for error handling
newtype Err e a = Err { getErr :: Either e a }

instance Monoid a => Monoid (Err e a) where
  mempty = Err (Right mempty)
  Err (Left e) `mappend` _ = Err (Left e)
  _ `mappend` Err (Left e) = Err (Left e)
  Err (Right a) `mappend` Err (Right b) = Err (Right (mappend a b))

-- | Used by 'Control.Lens.Type.Zoom' to 'Control.Lens.Type.zoom' into 'Control.Monad.Error.ErrorT'
newtype FocusingErr e k s a = FocusingErr { unfocusingErr :: k (Err e s) a }

instance Functor (k (Err e s)) => Functor (FocusingErr e k s) where
  fmap f (FocusingErr as) = FocusingErr (fmap f as)

instance Applicative (k (Err e s)) => Applicative (FocusingErr e k s) where
  pure = FocusingErr . pure
  FocusingErr kf <*> FocusingErr ka = FocusingErr (kf <*> ka)

-- | The result of 'Indexing'
data IndexingResult f a = IndexingResult (f a) {-# UNPACK #-} !Int

instance Functor f => Functor (IndexingResult f) where
  fmap f (IndexingResult fa n) = IndexingResult (fmap f fa) n

-- | Applicative composition of @'Control.Monad.Trans.State.Lazy.State' 'Int'@ with a 'Functor', used
-- by 'Control.Lens.Indexed.indexed'
newtype Indexing f a = Indexing { runIndexing :: Int -> IndexingResult f a }

instance Functor f => Functor (Indexing f) where
  fmap f (Indexing m) = Indexing $ \i -> fmap f (m i)

instance Applicative f => Applicative (Indexing f) where
  pure = Indexing . IndexingResult . pure
  Indexing mf <*> Indexing ma = Indexing $ \i -> case mf i of
    IndexingResult ff j -> case ma j of
       IndexingResult fa k -> IndexingResult (ff <*> fa) k

instance Gettable f => Gettable (Indexing f) where
  coerce (Indexing m) = Indexing $ \i -> case m i of
    IndexingResult ff j -> IndexingResult (coerce ff) j

-- | Used internally by 'Control.Lens.Traversal.traverseOf_' and the like.
newtype Traversed f = Traversed { getTraversed :: f () }

instance Applicative f => Monoid (Traversed f) where
  mempty = Traversed (pure ())
  Traversed ma `mappend` Traversed mb = Traversed (ma *> mb)

-- | Used internally by 'Control.Lens.Traversal.mapM_' and the like.
newtype Sequenced m = Sequenced { getSequenced :: m () }

instance Monad m => Monoid (Sequenced m) where
  mempty = Sequenced (return ())
  Sequenced ma `mappend` Sequenced mb = Sequenced (ma >> mb)

-- | Used for 'Control.Lens.Fold.minimumOf'
data Min a = NoMin | Min a

instance Ord a => Monoid (Min a) where
  mempty = NoMin
  mappend NoMin m = m
  mappend m NoMin = m
  mappend (Min a) (Min b) = Min (min a b)

-- | Obtain the minimum.
getMin :: Min a -> Maybe a
getMin NoMin   = Nothing
getMin (Min a) = Just a

-- | Used for 'Control.Lens.Fold.maximumOf'
data Max a = NoMax | Max a

instance Ord a => Monoid (Max a) where
  mempty = NoMax
  mappend NoMax m = m
  mappend m NoMax = m
  mappend (Max a) (Max b) = Max (max a b)

-- | Obtain the maximum
getMax :: Max a -> Maybe a
getMax NoMax   = Nothing
getMax (Max a) = Just a


-- | The indexed store can be used to characterize a 'Control.Lens.Type.Lens'
-- and is used by 'Control.Lens.Type.clone'
--
-- @'Context' a b t@ is isomorphic to
-- @newtype Context a b t = Context { runContext :: forall f. Functor f => (a -> f b) -> f t }@,
-- and to @exists s. (s, 'Control.Lens.Type.Lens' s t a b)@.
--
-- A 'Context' is like a 'Control.Lens.Type.Lens' that has already been applied to a some structure.
data Context a b t = Context (b -> t) a

instance Functor (Context a b) where
  fmap f (Context g t) = Context (f . g) t

instance (a ~ b) => Comonad (Context a b) where
  extract   (Context f a) = f a
  duplicate (Context f a) = Context (Context f) a
  extend g  (Context f a) = Context (g . Context f) a

instance (a ~ b) => ComonadStore a (Context a b) where
  pos (Context _ a) = a
  peek b (Context g _) = g b
  peeks f (Context g a) = g (f a)
  seek a (Context g _) = Context g a
  seeks f (Context g a) = Context g (f a)
  experiment f (Context g a) = g <$> f a

-- | This is used to characterize a 'Control.Lens.Traversal.Traversal'.
--
-- a.k.a. indexed Cartesian store comonad, indexed Kleene store comonad, or an indexed 'FunList'.
--
-- <http://twanvl.nl/blog/haskell/non-regular1>
--
-- @'Bazaar' a b t@ is isomorphic to @data Bazaar a b t = Buy t | Trade (Bazaar a b (b -> t)) a@,
-- and to @exists s. (s, 'Control.Lens.Traversal.Traversal' s t a b)@.
--
-- A 'Bazaar' is like a 'Control.Lens.Traversal.Traversal' that has already been applied to some structure.
--
-- Where a @'Context' a b t@ holds an @a@ and a function from @b@ to
-- @t@, a @'Bazaar' a b t@ holds N @a@s and a function from N
-- @b@s to @t@.
--
-- Mnemonically, a 'Bazaar' holds many stores and you can easily add more.
--
-- This is a final encoding of 'Bazaar'.
newtype Bazaar a b t = Bazaar { runBazaar :: forall f. Applicative f => (a -> f b) -> f t }

instance Functor (Bazaar a b) where
  fmap f (Bazaar k) = Bazaar (fmap f . k)

instance Applicative (Bazaar a b) where
  pure a = Bazaar (\_ -> pure a)
  {-# INLINE pure #-}
  Bazaar mf <*> Bazaar ma = Bazaar (\k -> mf k <*> ma k)
  {-# INLINE (<*>) #-}

instance (a ~ b) => Comonad (Bazaar a b) where
  extract (Bazaar m) = runIdentity (m Identity)
  {-# INLINE extract #-}
  duplicate = duplicateBazaar
  {-# INLINE duplicate #-}

-- | Given an action to run for each matched pair, traverse a bazaar.
--
-- @'bazaar' :: 'Control.Lens.Traversal.Traversal' ('Bazaar' a b t) t a b@
bazaar :: Applicative f => (a -> f b) -> Bazaar a b t -> f t
bazaar afb (Bazaar m) = m afb
{-# INLINE bazaar #-}

-- | 'Bazaar' is an indexed 'Comonad'.
duplicateBazaar :: Bazaar a c t -> Bazaar a b (Bazaar b c t)
duplicateBazaar (Bazaar m) = getCompose (m (Compose . fmap sell . sell))
{-# INLINE duplicateBazaar #-}
-- duplicateBazaar' (Bazaar m) = Bazaar (\g -> getCompose (m (Compose . fmap sell . g)))

-- | A trivial 'Bazaar'.
sell :: a -> Bazaar a b b
sell i = Bazaar (\k -> k i)
{-# INLINE sell #-}

instance (a ~ b) => ComonadApply (Bazaar a b) where
  (<@>) = (<*>)

-- | Wrap a monadic effect with a phantom type argument.
newtype Effect m r a = Effect { getEffect :: m r }

instance Functor (Effect m r) where
  fmap _ (Effect m) = Effect m

instance (Monad m, Monoid r) => Monoid (Effect m r a) where
  mempty = Effect (return mempty)
  Effect ma `mappend` Effect mb = Effect (liftM2 mappend ma mb)

instance (Monad m, Monoid r) => Applicative (Effect m r) where
  pure _ = Effect (return mempty)
  Effect ma <*> Effect mb = Effect (liftM2 mappend ma mb)

-- | Wrap a monadic effect with a phantom type argument. Used when magnifying RWST.
newtype EffectRWS w st m s a = EffectRWS { getEffectRWS :: st -> m (s,st,w) }

instance Functor (EffectRWS w st m s) where
  fmap _ (EffectRWS m) = EffectRWS m

instance (Monoid s, Monoid w, Monad m) => Applicative (EffectRWS w st m s) where
  pure _ = EffectRWS $ \st -> return (mempty, st, mempty)
  EffectRWS m <*> EffectRWS n = EffectRWS $ \st -> m st >>= \ (s,t,w) -> n t >>= \ (s',u,w') -> return (mappend s s', u, mappend w w')

{-
-- | Wrap a monadic effect with a phantom type argument. Used when magnifying StateT.
newtype EffectS st k s a = EffectS { runEffect :: st -> k (s, st) a }

instance Functor (k (s, st)) => Functor (EffectS st m s) where
  fmap f (EffectS m) = EffectS (fmap f . m)

instance (Monoid s, Monad m) => Applicative (EffectS st m s) where
  pure _ = EffectS $ \st -> return (mempty, st)
  EffectS m <*> EffectS n = EffectS $ \st -> m st >>= \ (s,t) -> n st >>= \ (s', u) -> return (mappend s s', u)
-}

-------------------------------------------------------------------------------
-- Gettables & Accessors
-------------------------------------------------------------------------------

-- | Generalizing 'Const' so we can apply simple 'Applicative'
-- transformations to it and so we can get nicer error messages
--
-- A 'Gettable' 'Functor' ignores its argument, which it carries solely as a
-- phantom type parameter.
--
-- To ensure this, an instance of 'Gettable' is required to satisfy:
--
-- @'id' = 'fmap' f = 'coerce'@
class Functor f => Gettable f where
  -- | Replace the phantom type argument.
  coerce :: f a -> f b

instance Gettable (Const r) where
  coerce (Const m) = Const m

instance Gettable f => Gettable (Backwards f) where
  coerce = Backwards . coerce . forwards

instance (Functor f, Gettable g) => Gettable (Compose f g) where
  coerce = Compose . fmap coerce . getCompose

instance Gettable (Effect m r) where
  coerce (Effect m) = Effect m

instance Gettable (EffectRWS w st m s) where
  coerce (EffectRWS m) = EffectRWS m

--instance Gettable (EffectS st m s) where
--  coerce (EffectS m) = EffectS m

instance Gettable (Accessor r) where
  coerce (Accessor m) = Accessor m

-- | Used instead of 'Const' to report
--
-- @No instance of ('Control.Lens.Setter.Settable' 'Accessor')@
--
-- when the user attempts to misuse a 'Control.Lens.Setter.Setter' as a
-- 'Control.Lens.Getter.Getter', rather than a monolithic unification error.
newtype Accessor r a = Accessor { runAccessor :: r }

instance Functor (Accessor r) where
  fmap _ (Accessor m) = Accessor m

instance Monoid r => Applicative (Accessor r) where
  pure _ = Accessor mempty
  Accessor a <*> Accessor b = Accessor (mappend a b)

-- | An 'Effective' 'Functor' ignores its argument and is isomorphic to a monad wrapped around a value.
--
-- That said, the monad is possibly rather unrelated to any 'Applicative' structure.
class (Monad m, Gettable f) => Effective m r f | f -> m r where
  effective :: Isomorphic k => k (m r) (f a)

-- | A convenient antonym that is used internally.
ineffective :: Effective m r f => Isomorphic k => k (f a) (m r)
ineffective = from effective
{-# INLINE ineffective #-}

instance Effective Identity r (Accessor r) where
  effective = isomorphic (Accessor . runIdentity) (Identity . runAccessor)
  {-# INLINE effective #-}

instance Effective m r f => Effective m (Dual r) (Backwards f) where
  effective = isomorphic (Backwards . effective . liftM getDual) (liftM Dual . ineffective . forwards)

instance Monad m => Effective m r (Effect m r) where
  effective = isomorphic Effect getEffect
  {-# INLINE effective #-}

-- | A 'Monoid' for a 'Gettable' 'Applicative'.
newtype Folding f a = Folding { getFolding :: f a }

instance (Gettable f, Applicative f) => Monoid (Folding f a) where
  mempty = Folding noEffect
  {-# INLINE mempty #-}
  Folding fr `mappend` Folding fs = Folding (fr *> fs)
  {-# INLINE mappend #-}

-- | The 'mempty' equivalent for a 'Gettable' 'Applicative' 'Functor'.
noEffect :: (Applicative f, Gettable f) => f a
noEffect = coerce $ pure ()
{-# INLINE noEffect #-}

-----------------------------------------------------------------------------
-- Settables & Mutators
-----------------------------------------------------------------------------

-- | Anything 'Settable' must be isomorphic to the 'Identity' 'Functor'.
class Applicative f => Settable f where
  untainted :: f a -> a

  untainted# :: (b -> f a) -> b -> a
  untainted# f = untainted . f

-- | so you can pass our a 'Control.Lens.Setter.Setter' into combinators from other lens libraries
instance Settable Identity where
  untainted = runIdentity
  untainted# = unsafeCoerce
  {-# INLINE untainted #-}

-- | 'Control.Lens.Fold.backwards'
instance Settable f => Settable (Backwards f) where
  untainted = untainted . forwards
  -- untainted# = untainted# forwards
  {-# INLINE untainted #-}

instance (Settable f, Settable g) => Settable (Compose f g) where
  untainted = untainted . untainted . getCompose
  -- untainted# = untainted# (untainted# getCompose)
  {-# INLINE untainted #-}

instance Settable Mutator where
  untainted = runMutator
  untainted# = unsafeCoerce
  {-# INLINE untainted #-}

-- | 'Mutator' is just a renamed 'Identity' functor to give better error
-- messages when someone attempts to use a getter as a setter.
--
-- Most user code will never need to see this type.
newtype Mutator a = Mutator { runMutator :: a }

instance Functor Mutator where
  fmap f (Mutator a) = Mutator (f a)

instance Applicative Mutator where
  pure = Mutator
  Mutator f <*> Mutator a = Mutator (f a)

-----------------------------------------------------------------------------
-- Level
-----------------------------------------------------------------------------

-- | A basic non-empty list zipper
--
-- All combinators assume the invariant that the length stored matches the number
-- of elements in list of items to the left, and the list of items to the left is
-- stored reversed.
data Level a = Level {-# UNPACK #-} !Int [a] a [a]

-- | How many entries are there in this level?
levelWidth :: Level a -> Int
levelWidth (Level n _ _ rs) = n + 1 + length rs
{-# INLINE levelWidth #-}

-- | Pull the non-emtpy list zipper left one entry
leftLevel :: Level a -> Maybe (Level a)
leftLevel (Level _ []     _ _ ) = Nothing
leftLevel (Level n (l:ls) a rs) = Just (Level (n - 1) ls l (a:rs))
{-# INLINE leftLevel #-}

-- | Pull the non-empty list zipper left one entry, stopping at the first entry.
left1Level :: Level a -> Level a
left1Level z = fromMaybe z (leftLevel z)
{-# INLINE left1Level #-}

-- | Pull the non-empty list zipper all the way to the left.
leftmostLevel :: Level a -> Level a
leftmostLevel (Level _ ls m rs) = case Prelude.reverse ls ++ m : rs of
  (c:cs) -> Level 0 [] c cs
  _ -> error "the impossible happened"
{-# INLINE leftmostLevel #-}

-- | Pul the non-empty list zipper all the way to the right.
-- /NB:/, when given an infinite list this may not terminate.
rightmostLevel :: Level a -> Level a
rightmostLevel (Level _ ls m rs) = go 0 [] (Prelude.head xs) (Prelude.tail xs) where
  xs = Prelude.reverse ls ++ m : rs
  go n zs y []     = Level n zs y []
  go n zs y (w:ws) = (go $! n + 1) (y:zs) w ws
{-# INLINE rightmostLevel #-}

-- | Pull the non-empty list zipper right one entry.
rightLevel :: Level a -> Maybe (Level a)
rightLevel (Level _ _  _ []    ) = Nothing
rightLevel (Level n ls a (r:rs)) = Just (Level (n + 1) (a:ls) r rs)
{-# INLINE rightLevel #-}

-- | Pull the non-empty list zipper right one entry, stopping at the last entry.
right1Level :: Level a -> Level a
right1Level z = fromMaybe z (rightLevel z)
{-# INLINE right1Level #-}

-- | This is a 'Lens' targeting the value that we would 'extract' from the non-empty list zipper.
--
-- @'view' 'focusLevel' ≡ 'extract'@
--
-- @'focusLevel' :: 'Control.Lens.Type.Simple' 'Control.Lens.Type.Lens' ('Level' a) a@
focusLevel :: Functor f => (a -> f a) -> Level a -> f (Level a)
focusLevel f (Level n ls a rs) = (\b -> Level n ls b rs) <$> f a
{-# INLINE focusLevel #-}

instance Functor Level where
  fmap f (Level n ls a rs) = Level n (f <$> ls) (f a) (f <$> rs)

instance Foldable Level where
  foldMap f = foldMap f . rezipLevel

instance Traversable Level where
  traverse f (Level n ls a rs) = Level n <$> forwards (traverse (Backwards . f) ls) <*> f a <*> traverse f rs

-- | Zip a non-empty list zipper back up, and return the result.
rezipLevel :: Level a -> NonEmpty a
rezipLevel (Level _ ls a rs) = NonEmpty.fromList (Prelude.reverse ls ++ a : rs)
{-# INLINE rezipLevel #-}

instance Comonad Level where
  extract (Level _ _ a _) = a
  extend f w@(Level n ls m rs) = Level n (gol (n - 1) (m:rs) ls) (f w) (gor (n + 1) (m:ls) rs) where
    gol k zs (y:ys) = f (Level k ys y zs) : (gol $! k - 1) (y:zs) ys
    gol _ _ [] = []
    gor k ys (z:zs) = f (Level k ys z zs) : (gor $! k + 1) (z:ys) zs
    gor _ _ [] = []

instance ComonadStore Int Level where
  pos (Level n _ _ _) = n
  peek n (Level m ls a rs) = case compare n m of
    LT -> ls Prelude.!! (m - n)
    EQ -> a
    GT -> rs Prelude.!! (n - m)

