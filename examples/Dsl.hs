{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction, ViewPatterns, TypeOperators, RankNTypes #-}
import Control.Lens
import Control.Lens.Dsl
import qualified Control.Category as C

$(lenq [d|

 lastLens :: [a] :->: a
 lastLens [x] = x
 lastLens (_:xs) = lastLens xs

 |] )

$(lenq [d|

 nothingLeft :: Maybe a :<->: Either () a
 nothingLeft (Just x) = Right x
 nothingLeft Nothing = Left ()

 leftMaybe :: Maybe (Either a b) :<->: Either (Maybe a) b
 leftMaybe Nothing = Left Nothing
 leftMaybe (Just (Left x)) = Left (Just x)
 leftMaybe (Just (Right x)) = Right x

 boolMaybe :: Bool :<->: Maybe ()
 boolMaybe False = Nothing
 boolMaybe True = Just ()

 boolEither :: Bool :<->: Either () ()
 boolEither x = nothingLeft (boolMaybe x)

 fstLens :: LenqLens (a, b) (a', b) a a'
 fstLens (x, y) = x

 headLens :: [a] :->: a
 headLens (x:_) = x

 trueLastLast :: [[a]] :->: (Bool, a)
 trueLastLast x = (True, x ^. lastLens . lastLens)

{- TODO
 lastOfLens :: (a :-> b) -> [a] :->: b
 lastOfLens l [x] = x ^. l
 lastOfLens l (_:xs) = lastOfLens l xs
-}

 |] )


main = do
  print $ over fstLens (+3) (1, 2)
  print $ True       ^. boolEither
  print $ Left ()    ^. from boolEither
  print $ Just 5     ^. nothingLeft
  print $ Right "hi" ^. from nothingLeft
  print $ (Left () :: Either () String)
  	                 ^. from nothingLeft
  print $ [[1,2,3]]  ^. trueLastLast
  -- This works because trueLastLast is not properly injective
  print $ trueLastLast .~ (False, 5) $ [[1,2,3]]
