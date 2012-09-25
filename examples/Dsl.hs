{-# LANGUAGE TemplateHaskell, NoMonomorphismRestriction, ViewPatterns #-}
import Control.Lens
import Control.Lens.Dsl

$(lenqDecs isoConf [d|

 leftNull (Just x) = Left x
 leftNull Nothing = Right ()

 leftMaybe Nothing = Left Nothing
 leftMaybe (Just (Left x)) = Left (Just x)
 leftMaybe (Just (Right x)) = Right x

 boolMaybe False = Nothing
 boolMaybe True = Just ()

 boolEither x = leftNull (boolMaybe x)

 |] )
