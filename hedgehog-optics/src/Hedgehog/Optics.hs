module Hedgehog.Optics
  ( wellFormedPrism,
    wellFormedLens,
    wellFormedIso,
    prismExample,
  )
where

import Control.Monad (Monad (return))
import Data.Either (Either (Left, Right))
import Data.Eq (Eq)
import Data.Function ((.))
import Data.Maybe (Maybe (Just))
import Hedgehog (Gen, PropertyT, annotate, forAll, (===))
import Optics.AffineFold (preview)
import Optics.AffineTraversal (matching)
import Optics.Getter (view)
import Optics.Iso (Iso')
import Optics.Lens (Lens')
import Optics.Prism (Prism')
import Optics.Review (review)
import Optics.Setter (set)
import Text.Show (Show)

-- | Checks whether a prism respects the well-formedness
--    laws given in "Optics.Prism"
wellFormedPrism ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  Gen large ->
  Gen small ->
  -- | Prism signifying that the @small@ type
  --   is a subset of the @large@ type -}
  Prism' large small ->
  PropertyT m ()
wellFormedPrism genLarge genSmall o = do
  getSetPrismLaw genLarge o
  setGetPrismLaw genSmall o

getSetPrismLaw ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  Gen large ->
  Prism' large small ->
  PropertyT m ()
getSetPrismLaw genLarge o = do
  large <- forAll genLarge
  case matching o large of
    Right small -> do
      annotate "The get-set law must hold for a Prism"
      review o small === large
    Left _ -> return ()

setGetPrismLaw ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  Gen small ->
  Prism' large small ->
  PropertyT m ()
setGetPrismLaw genSmall o = do
  small <- forAll genSmall
  annotate "The set-get law must hold for a Prism"
  matching o (review o small) === Right small

-- | Checks whether a lens respects the well-formedness
--    laws given in "Optics.Lens"
wellFormedLens ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  Gen large ->
  Gen small ->
  -- | Lens signifying that the @small@ type is
  --   a constituent part of the @large@ type
  Lens' large small ->
  PropertyT m ()
wellFormedLens genLarge genSmall o = do
  getPutLensLaw genLarge genSmall o
  putGetLensLaw genLarge o
  putPutLensLaw genLarge genSmall o

getPutLensLaw ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  Gen large ->
  Gen small ->
  Lens' large small ->
  PropertyT m ()
getPutLensLaw genLarge genSmall o = do
  large <- forAll genLarge
  small <- forAll genSmall
  annotate "The set-get law must hold for a Lens"
  view o (set o small large) === small

putGetLensLaw ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  Gen large ->
  Lens' large small ->
  PropertyT m ()
putGetLensLaw genLarge o = do
  large <- forAll genLarge
  annotate "The get-set law must hold for a Lens"
  set o (view o large) large === large

putPutLensLaw ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  Gen large ->
  Gen small ->
  Lens' large small ->
  PropertyT m ()
putPutLensLaw genLarge genSmall o = do
  large <- forAll genLarge
  small1 <- forAll genSmall
  small2 <- forAll genSmall
  annotate "The set-set law must hold for a Lens"
  set o small2 (set o small1 large) === set o small2 large

-- | Checks whether an isomorphism respects the
--    well-formedness laws given in "Optics.Iso"
wellFormedIso ::
  Monad m =>
  (Show a, Eq a) =>
  (Show b, Eq b) =>
  Gen a ->
  Gen b ->
  -- | Isomorphism signifying that types
  --   @a@ and @b@ are basically the same thing
  Iso' a b ->
  PropertyT m ()
wellFormedIso genA genB o = do
  setGetIsoLaw genB o
  getSetIsoLaw genA o

setGetIsoLaw ::
  Monad m =>
  (Show a, Eq a) =>
  (Show b, Eq b) =>
  Gen b ->
  Iso' a b ->
  PropertyT m ()
setGetIsoLaw genB o = do
  b <- forAll genB
  annotate "The set-get law must hold for an Iso"
  (view o . review o) b === b

getSetIsoLaw ::
  Monad m =>
  (Show a, Eq a) =>
  (Show b, Eq b) =>
  Gen a ->
  Iso' a b ->
  PropertyT m ()
getSetIsoLaw genA o = do
  a <- forAll genA
  annotate "The get-set law must hold for an Iso"
  (review o . view o) a === a

-- | Assert that a prism matches for a particular set of values
--
-- A 'review' of the @small@ value should produce the @large@ value, and
-- a 'preview' of the @large@ value should produce the @small@ value.
prismExample ::
  Monad m =>
  (Show large, Eq large) =>
  (Show small, Eq small) =>
  -- | Prism signifying that the @small@
  --   type is a subset of the @large@ type
  Prism' large small ->
  large ->
  small ->
  PropertyT m ()
prismExample o large small = do
  review o small === large
  preview o large === Just small
