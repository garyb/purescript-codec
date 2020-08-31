module Data.Codec where

import Prelude

import Control.Alternative (class Alt, class Alternative, class Plus, empty, (<|>))
import Control.Monad.Reader (ReaderT(..), mapReaderT, runReaderT)
import Control.Monad.Writer (Writer, writer, execWriter, runWriter)
import Control.MonadPlus (class MonadPlus)
import Control.MonadZero (class MonadZero)
import Data.Functor.Invariant (class Invariant, imapF)
import Data.Newtype (un)
import Data.Profunctor (class Profunctor, dimap, lcmap)
import Data.Profunctor.Star (Star(..))
import Data.Tuple (Tuple(..))

-- | A general type for codecs.
data GCodec m n a b = GCodec (m b) (Star n a b)

instance functorGCodec ∷ (Functor m, Functor n) ⇒ Functor (GCodec m n a) where
  map f (GCodec dec enc) =
    GCodec (map f dec) (map f enc)

instance invariantGCodec ∷ (Functor m, Functor n) ⇒ Invariant (GCodec m n a) where
  imap = imapF

instance applyGCodec ∷ (Apply m, Apply n) ⇒ Apply (GCodec m n a) where
  apply (GCodec decf encf) (GCodec decx encx) =
    GCodec (decf <*> decx) (encf <*> encx)

instance applicativeGCodec ∷ (Applicative m, Applicative n) ⇒ Applicative (GCodec m n a) where
  pure x =
    GCodec (pure x) (pure x)

instance bindGCodec ∷ (Bind m, Bind n) ⇒ Bind (GCodec m n a) where
  bind (GCodec dec enc) f =
    GCodec (dec >>= f >>> decoder) (enc >>= f >>> encoder)

instance monadGCodec ∷ (Monad m, Monad n) ⇒ Monad (GCodec m n a)

instance profunctorGCodec ∷ (Functor m, Functor n) ⇒ Profunctor (GCodec m n) where
  dimap f g (GCodec dec enc) =
    GCodec (map g dec) (dimap f g enc)

instance altGCodec ∷ (Alt m, Alt n) ⇒ Alt (GCodec m n a) where
  alt (GCodec decx encx) (GCodec decy ency) =
    GCodec (decx <|> decy) (encx <|> ency)

instance plusGCodec ∷ (Plus m, Plus n) ⇒ Plus (GCodec m n a) where
  empty = GCodec empty empty

instance alternativeGCodec ∷ (Alternative m, Alternative n) ⇒ Alternative (GCodec m n a)

instance monadZeroGCodec ∷ (MonadZero m, MonadZero n) ⇒ MonadZero (GCodec m n a)

instance monadPlusGCodec ∷ (MonadPlus m, MonadPlus n) ⇒ MonadPlus (GCodec m n a)

instance semigroupoidGCodec ∷ Bind n ⇒ Semigroupoid (GCodec m n) where
  compose (GCodec decx encx) (GCodec decy ency) =
    GCodec decx (compose encx ency)

-- | Extracts the decoder part of a `GCodec`
decoder ∷ ∀ m n a b. GCodec m n a b → m b
decoder (GCodec f _) = f

-- | Extracts the encoder part of a `GCodec`
encoder ∷ ∀ m n a b. GCodec m n a b → Star n a b
encoder (GCodec _ f) = f

-- | Changes the `m` and `n` functors used in the codec using the specified
-- | natural transformations.
bihoistGCodec
  ∷ ∀ m m' n n' a b
   . (m ~> m')
  → (n ~> n')
  → GCodec m n a b
  → GCodec m' n' a b
bihoistGCodec f g (GCodec dec (Star h)) = GCodec (f dec) (Star (g <<< h))

-- | `GCodec` is defined as a `Profunctor` so that `lcmap` can be used to target
-- | specific fields when defining a codec for a product type. This operator
-- | is a convenience for that:
-- |
-- | ``` purescript
-- | tupleCodec =
-- |   Tuple
-- |     <$> fst ~ fstCodec
-- |     <*> snd ~ sndCodec
-- | ```
infixl 5 lcmap as ~

type Codec m a b c d = GCodec (ReaderT a m) (Writer b) c d

decode ∷ ∀ m a b c d. Codec m a b c d → a → m d
decode = runReaderT <<< decoder

encode ∷ ∀ m a b c d. Codec m a b c d → c → b
encode codec = execWriter <<< un Star (encoder codec)

mapCodec
  ∷ ∀ m a b c d
  . Bind m
  ⇒ (a → m b)
  → (b → a)
  → Codec m c d a a
  → Codec m c d b b
mapCodec f g (GCodec decf encf) = GCodec dec enc
  where
  dec = ReaderT \x → f =<< runReaderT decf x
  enc = Star \a →
    let (Tuple w x) = runWriter (un Star encf (g a))
    in writer $ Tuple a x

composeCodec
  ∷ ∀ a d f b e c m
  . Bind m
  ⇒ Codec m d c e f
  → Codec m a b c d
  → Codec m a b e f
composeCodec (GCodec decf encf) (GCodec decg encg) =
  GCodec
    (ReaderT \x → runReaderT decf =<< runReaderT decg x)
    (Star \c →
      let (Tuple w x) = runWriter (un Star encf c)
      in writer $ Tuple w (execWriter (un Star encg x)))

infixr 8 composeCodec as <~<

composeCodecFlipped
  ∷ ∀ a d f b e c m
  . Bind m
  ⇒ Codec m a b c d
  → Codec m d c e f
  → Codec m a b e f
composeCodecFlipped = flip composeCodec

infixr 8 composeCodecFlipped as >~>

hoistCodec ∷ ∀ m m' a b c d. (m ~> m') → Codec m a b c d → Codec m' a b c d
hoistCodec f = bihoistGCodec (mapReaderT f) identity

type BasicCodec m a b = Codec m a a b b

basicCodec ∷ ∀ m a b. (a → m b) → (b → a) → BasicCodec m a b
basicCodec f g = GCodec (ReaderT f) (Star \x → writer $ Tuple x (g x))
