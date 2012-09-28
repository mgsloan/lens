{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction, ViewPatterns, TypeOperators, RankNTypes, TypeFamilies #-}
import Control.Lens
import Control.Lens.Dsl

$(lenq [d|

 leftNull :: Maybe a :<->: Either () a
 leftNull (Just x) = Right x
 leftNull Nothing = Left ()

 leftMaybe :: Maybe (Either a b) :<->: Either (Maybe a) b
 leftMaybe Nothing = Left Nothing
 leftMaybe (Just (Left x)) = Left (Just x)
 leftMaybe (Just (Right x)) = Right x

 boolMaybe :: Bool :<->: Maybe ()
 boolMaybe False = Nothing
 boolMaybe True = Just ()

 boolEither :: Bool :<->: Either () ()
 boolEither x = leftNull (boolMaybe x)

 fstLens :: LenqLens (a, b) (a', b) a a'
 fstLens (x, y) = x

 |] )

main = do
  print $ over fstLens (+3) (1, 2)
  print $ True ^. boolEither
  print $ Left () ^. from boolEither
  print $ Just 5 ^. leftNull