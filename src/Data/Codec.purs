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
data GCodec decoderF encoderF encoderInputType decoderTargetType = GCodec (decoderF decoderTargetType) (Star encoderF encoderInputType decoderTargetType)

instance functorGCodec ∷ (Functor decoderF, Functor encoderF) ⇒ Functor (GCodec decoderF encoderF encoderInputType) where
  map f (GCodec dec enc) =
    GCodec (map f dec) (map f enc)

instance invariantGCodec ∷ (Functor decoderF, Functor encoderF) ⇒ Invariant (GCodec decoderF encoderF encoderInputType) where
  imap = imapF

instance applyGCodec ∷ (Apply decoderF, Apply encoderF) ⇒ Apply (GCodec decoderF encoderF encoderInputType) where
  apply (GCodec decf encf) (GCodec decx encx) =
    GCodec (decf <*> decx) (encf <*> encx)

instance applicativeGCodec ∷ (Applicative decoderF, Applicative encoderF) ⇒ Applicative (GCodec decoderF encoderF encoderInputType) where
  pure x =
    GCodec (pure x) (pure x)

instance bindGCodec ∷ (Bind decoderF, Bind encoderF) ⇒ Bind (GCodec decoderF encoderF encoderInputType) where
  bind (GCodec dec enc) f =
    GCodec (dec >>= f >>> decoder) (enc >>= f >>> encoder)

instance monadGCodec ∷ (Monad decoderF, Monad encoderF) ⇒ Monad (GCodec decoderF encoderF encoderInputType)

instance profunctorGCodec ∷ (Functor decoderF, Functor encoderF) ⇒ Profunctor (GCodec decoderF encoderF) where
  dimap f g (GCodec dec enc) =
    GCodec (map g dec) (dimap f g enc)

instance altGCodec ∷ (Alt decoderF, Alt encoderF) ⇒ Alt (GCodec decoderF encoderF encoderInputType) where
  alt (GCodec decx encx) (GCodec decy ency) =
    GCodec (decx <|> decy) (encx <|> ency)

instance plusGCodec ∷ (Plus decoderF, Plus encoderF) ⇒ Plus (GCodec decoderF encoderF encoderInputType) where
  empty = GCodec empty empty

instance alternativeGCodec ∷ (Alternative decoderF, Alternative encoderF) ⇒ Alternative (GCodec decoderF encoderF encoderInputType)

instance monadZeroGCodec ∷ (MonadZero decoderF, MonadZero encoderF) ⇒ MonadZero (GCodec decoderF encoderF encoderInputType)

instance monadPlusGCodec ∷ (MonadPlus decoderF, MonadPlus encoderF) ⇒ MonadPlus (GCodec decoderF encoderF encoderInputType)

instance semigroupoidGCodec ∷ Bind encoderF ⇒ Semigroupoid (GCodec decoderF encoderF) where
  compose (GCodec decx encx) (GCodec decy ency) =
    GCodec decx (compose encx ency)

-- | Extracts the decoder part of a `GCodec`
decoder ∷ ∀ decoderF encoderF encoderInputType decoderTargetType. GCodec decoderF encoderF encoderInputType decoderTargetType → decoderF decoderTargetType
decoder (GCodec f _) = f

-- | Extracts the encoder part of a `GCodec`
encoder ∷ ∀ decoderF encoderF encoderInputType decoderTargetType. GCodec decoderF encoderF encoderInputType decoderTargetType → Star encoderF encoderInputType decoderTargetType
encoder (GCodec _ f) = f

-- | Changes the `decoderF` and `encoderF` functors used in the codec using the specified
-- | natural transformations.
bihoistGCodec
  ∷ ∀ decoderF decoderF' encoderF encoderF' encoderInputType decoderTargetType
   . (decoderF ~> decoderF')
  → (encoderF ~> encoderF')
  → GCodec decoderF encoderF encoderInputType decoderTargetType
  → GCodec decoderF' encoderF' encoderInputType decoderTargetType
bihoistGCodec f g (GCodec dec (Star h)) = GCodec (f dec) (Star (g <<< h))

-- | `GCodec` is defined as a `Profunctor` so that `lmap` can be used to target
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

type Codec decoderF decoderConfig encoderAccum encoderInputType decoderTargetType = GCodec (ReaderT decoderConfig decoderF) (Writer encoderAccum) encoderInputType decoderTargetType

decode
  ∷ ∀ decoderF decoderConfig encoderAccum encoderInputType decoderTargetType
  . Codec decoderF decoderConfig encoderAccum encoderInputType decoderTargetType
  → decoderConfig
  → decoderF decoderTargetType
decode = runReaderT <<< decoder

encode
  ∷ ∀ decoderF decoderConfig encoderAccum encoderInputType decoderTargetType
  . Codec decoderF decoderConfig encoderAccum encoderInputType decoderTargetType
  → encoderInputType
  → encoderAccum
encode codec = execWriter <<< un Star (encoder codec)

mapCodec
  ∷ ∀ decoderF a b decoderConfig encoderAccum
  . Bind decoderF
  ⇒ (a → decoderF b)
  → (b → a)
  → Codec decoderF decoderConfig encoderAccum a a
  → Codec decoderF decoderConfig encoderAccum b b
mapCodec f g (GCodec decf encf) = GCodec dec enc
  where
  dec = ReaderT \decoderConfig → f =<< runReaderT decf decoderConfig
  enc = Star \encoderInput →
    let (Tuple w x) = runWriter (un Star encf (g encoderInput))
    in writer $ Tuple encoderInput x

composeCodec
  ∷ ∀ a b c decoderConfig'a decoderConfig'b decoderConfig'c decoderF
  . Bind decoderF
  ⇒ Codec decoderF decoderConfig'b b c decoderConfig'c
  → Codec decoderF decoderConfig'a a b decoderConfig'b
  → Codec decoderF decoderConfig'a a c decoderConfig'c
composeCodec (GCodec decf encf) (GCodec decg encg) =
  GCodec
    (ReaderT \decoderConfig → runReaderT decf =<< runReaderT decg decoderConfig)
    (Star \encoderInput →
      let (Tuple w x) = runWriter (un Star encf encoderInput)
      in writer $ Tuple w (execWriter (un Star encg x)))

infixr 8 composeCodec as <~<

composeCodecFlipped
  ∷ ∀ a b c decoderConfig'a decoderConfig'b decoderConfig'c decoderF
  . Bind decoderF
  ⇒ Codec decoderF decoderConfig'a a b decoderConfig'b
  → Codec decoderF decoderConfig'b b c decoderConfig'c
  → Codec decoderF decoderConfig'a a c decoderConfig'c
composeCodecFlipped = flip composeCodec

infixr 8 composeCodecFlipped as >~>

hoistCodec
  ∷ ∀ decoderF decoderF' decoderConfig encoderAccum encoderInputType decoderTargetType
  . (decoderF ~> decoderF')
  → Codec decoderF decoderConfig encoderAccum encoderInputType decoderTargetType
  → Codec decoderF' decoderConfig encoderAccum encoderInputType decoderTargetType
hoistCodec f = bihoistGCodec (mapReaderT f) identity

type BasicCodec decoderF rawType targetType = Codec decoderF rawType rawType targetType targetType

basicCodec
  ∷ ∀ decoderF rawType targetType
  . (rawType → decoderF targetType)
  → (targetType → rawType)
  → BasicCodec decoderF rawType targetType
basicCodec f g = GCodec (ReaderT f) (Star \x → writer $ Tuple x (g x))
