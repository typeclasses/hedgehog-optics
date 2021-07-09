module Hedgehog.Optics where

import Control.Applicative (Applicative ((*>)))
import Control.Monad (Monad (return))
import Data.Either (Either (Left, Right))
import Data.Eq (Eq)
import Data.Function ((.))
import Data.Maybe (Maybe (Just))
import Hedgehog (Gen, PropertyT, forAll, (===))
import Optics.AffineFold (preview)
import Optics.AffineTraversal (matching)
import Optics.Getter (view)
import Optics.Iso (Iso')
import Optics.Lens (Lens')
import Optics.Prism (Prism')
import Optics.Review (review)
import Optics.Setter (set)
import Text.Show (Show)

{- | Checks whether a prism respects the well-formedness
laws given in "Optics.Prism" -}
wellFormedPrism ::
    Monad m                =>
    (Show large, Eq large) =>
    (Show small, Eq small) =>

       Gen large
    -> Gen small
    -> Prism' large small {- ^ Prism signifying that the
          @small@ type is a subset of the @large@ type -}
    -> PropertyT m ()

wellFormedPrism genLarge genSmall o = part1 *> part2
  where
    part1 =
      do
        large <- forAll genLarge
        case matching o large of
            Right small -> review o small === large
            Left _ -> return ()

    part2 =
      do
        small <- forAll genSmall
        matching o (review o small) === Right small

{- | Checks whether a lens respects the well-formedness
laws given in "Optics.Lens" -}
wellFormedLens ::
    Monad m =>
    (Show large, Eq large) =>
    (Show small, Eq small) =>

       Gen large
    -> Gen small
    -> Lens' large small {- ^ Lens signifying that the @small@
          type is a constituent part of the @large@ type -}
    -> PropertyT m ()

wellFormedLens genLarge genSmall o = getPut *> putGet *> putPut
  where
    getPut =
      do
        large <- forAll genLarge
        small <- forAll genSmall
        view o (set o small large) === small

    putGet =
      do
        large <- forAll genLarge
        set o (view o large) large === large

    putPut =
      do
        large <- forAll genLarge
        small1 <- forAll genSmall
        small2 <- forAll genSmall
        set o small2 (set o small1 large) === set o small2 large

{- | Checks whether an isomorphism respects the
well-formedness laws given in "Optics.Iso" -}
wellFormedIso ::
    Monad m =>
    (Show a, Eq a) =>
    (Show b, Eq b) =>

       Gen a
    -> Gen b
    -> Iso' a b {- ^ Isomorphism signifying that types
          @a@ and @b@ are basically the same thing -}
    -> PropertyT m ()

wellFormedIso genA genB o = part1 *> part2
  where
    part1 =
      do
        b <- forAll genB
        (view o . review o) b === b

    part2 =
      do
        a <- forAll genA
        (review o . view o) a === a

{- | Assert that a prism matches for a particular set of values:
A 'review' of the @small@ value should produce the @large@ value, and
a 'preview' of the @large@ value should produce the @small@ value. -}
prismExample ::
    Monad m =>
    (Show large, Eq large) =>
    (Show small, Eq small) =>

       Prism' large small {- ^ Prism signifying that the
          @small@ type is a subset of the @large@ type -}
    -> large
    -> small
    -> PropertyT m ()

prismExample o large small =
  do
    review o small === large
    preview o large === Just small
