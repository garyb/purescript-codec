module Control.Monad.Codec where

import Prelude

import Control.Monad.Reader (ReaderT(..), ask, runReaderT, mapReaderT)
import Control.Monad.Writer (Writer, writer, execWriter, runWriter)
import Control.Monad.Trans.Class (lift)
import Data.Functor.Invariant (class Invariant, imapF)
import Data.Profunctor (class Profunctor, lmap)
import Data.Tuple (Tuple(..))

data GCodec m n a b = GCodec (m b) (a -> n b)

type GCodec' m n a = GCodec m n a a

instance functorGCodec :: (Functor m, Functor n) => Functor (GCodec m n a) where
  map f (GCodec dec enc) =
    GCodec (map f dec) (map f <$> enc)

instance invariantGCodec :: (Functor m, Functor n) => Invariant (GCodec m n a) where
  imap = imapF

instance applyGCodec :: (Apply m, Apply n) => Apply (GCodec m n a) where
  apply (GCodec decf encf) (GCodec decx encx) =
    GCodec (decf <*> decx) (\c -> encf c <*> encx c)

instance applicativeGCodec :: (Applicative m, Applicative n) => Applicative (GCodec m n a) where
  pure x = GCodec (pure x) (const (pure x))

instance bindGCodec :: (Bind m, Bind n) => Bind (GCodec m n a) where
  bind (GCodec dec enc) f =
    GCodec
      (dec >>= \x -> case f x of GCodec dec' _ -> dec')
      (\c -> enc c >>= \x -> case f x of GCodec _ enc' -> enc' c)

instance monadGCodec :: (Monad m, Monad n) => Monad (GCodec m n a)

instance profunctorGCodec :: (Functor m, Functor n) => Profunctor (GCodec m n) where
  dimap f g (GCodec dec enc) =
    GCodec (map g dec) (map g <<< enc <<< f)

gdecoder :: forall m n a b. GCodec m n a b -> m b
gdecoder (GCodec f _) = f

gencoder :: forall m n a b. GCodec m n a b -> a -> n b
gencoder (GCodec _ f) = f

bihoistGCodec
  :: forall m m' n n' a b
   . (m ~> m')
  -> (n ~> n')
  -> GCodec m n a b
  -> GCodec m' n' a b
bihoistGCodec f g (GCodec dec enc) = GCodec (f dec) (map g enc)

infixl 5 lmap as <~>

type Codec m a b c d = GCodec (ReaderT a m) (Writer b) c d

type Codec' m a b = Codec m a a b b

decoder :: forall m a b c d. Codec m a b c d -> ReaderT a m d
decoder (GCodec f _) = f

encoder :: forall m a b c d. Codec m a b c d -> c -> Writer b d
encoder (GCodec _ f) = f

decode :: forall m a b c d. Codec m a b c d -> a -> m d
decode codec = runReaderT (decoder codec)

encode :: forall m a b c d. Codec m a b c d -> c -> b
encode codec = execWriter <<< encoder codec

composeCodec
  :: forall a d f b e c m
   . Bind m
  => Codec m d c e f
  -> Codec m a b c d
  -> Codec m a b e f
composeCodec (GCodec decf encf) (GCodec decg encg) =
  GCodec
    (ReaderT \x -> runReaderT decf =<< runReaderT decg x)
    (\c -> do
      let (Tuple w x) = runWriter (encf c)
      let y = execWriter (encg x)
      writer $ Tuple w y)

basicCodec
  :: forall m a b
   . Monad m
  => (a -> m b)
  -> (b -> a)
  -> Codec' m a b
basicCodec f g =
  GCodec
    (lift <<< f =<< ask)
    (\x -> writer $ Tuple x (g x))

hoistCodec
  :: forall m m' a b c d
   . (m ~> m')
  -> Codec m a b c d
  -> Codec m' a b c d
hoistCodec f = bihoistGCodec (mapReaderT f) id
