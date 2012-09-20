{-# LANGUAGE TemplateHaskell #-}
module Control.Lens.Dsl where

import Control.Applicative
import Control.Lens
import Data.Generics (Data, extT, extM, mkQ, everything, everywhereM, listify)
import Data.List as List
import Data.Maybe (fromJust)
import Language.Haskell.TH

--TODO: use.
data LenqConf = IgnorePartial | WarnPartial | ErrorPartial

-- TODO: multiif
-- TODO: lambda case
-- TODO: guards??

lenq :: ExpQ -> ExpQ
lenq = lenqExp WarnPartial

lenqExp :: LenqConf -> ExpQ -> ExpQ
lenqExp conf qexpr = do
  expr <- qexpr
  case expr of
    (ParensE e) -> lenqExp conf $ return e
    (LamE ps (CaseE e ms)) -> checkCase (last ps) ps e ms
    (LamE ps e) -> buildExp ps [Match (last ps) (NormalB e) []]
    _ -> error "Expected a lambda expression and case statement."
 where
  checkCase (VarP v) ps e ms | (VarE v == e) = buildExp ps ms
  checkCase _ _ _ _ = rFail "Case statements must just case on the last parameter."
  buildExp ps ms = do
    f <- newName "_f"
    v <- newName "_v"
    ms' <- mapM (lenqMatch conf f) ms
    return . LamE (init ps ++ [VarP f, VarP v]) $ CaseE (VarE v) ms'

{-
lenqDec :: LenqConf -> DecsQ -> DecsQ
lenqDec conf decs = mapM doDec =<< decs
 where
  doDec (FunD n cs) = funD n $ lensDsl conf
-}

lenqMatch :: LenqConf -> Name -> Match -> Q Match
lenqMatch conf f (Match matchPat (NormalB matchExp) []) = do
  let vs = allVarP matchPat

  (outTup, inExp) <- doExpr vs matchExp

  inTup  <- patToExp (const $ imposs "In converting pattern for outer tuple representation.") outTup

  -- Replaces wildcards with variables, to preserve non-overwritten variables
  pat <- everywhereM (return `extM` replaceWild) matchPat
  outExp <- patToExp (const . rFail $ "Pattern " ++ pprint matchPat ++ " has no expression equivalent.") pat

  let expr = InfixE (Just $ LamE [outTup] outExp)
                    (VarE '(<$>))
                    (Just $ AppE (AppE inExp (VarE f)) inTup)

  return $ Match pat (NormalB expr) []
 where
  lamLens p e p' p'' e' = appsE [varE 'lens, lamE [p] e, lamE [p', p''] e']

  bijLens p e = lamLens (return p) (return e) wildP
    (expToPat (const $ imposs "When doing exp-to-pat for bijection.") e)
    (patToExp (const $ imposs "When doing pat-to-exp for bijection.") p)

  constLens e = lamLens wildP (return e) wildP wildP (return e)

  apps = foldl1 AppE

  comp l = infixE (Just $ return l) (varE '(.)) . Just

  -- This isn't gonna cut it - gotta inline alongside??
  doCompound :: (Pat -> [Exp] -> ExpQ) -> [Name] -> [Exp] -> Q (Pat, Exp)
  doCompound fe vs es = do
    args <- mapM (doExpr vs) es
    pns <- mapM (const $ newName "x") es
    let pat  = foldl1 (\x y -> TupP                  [x, y]) $ map fst args
        pat' = foldl1 (\x y -> TupP                  [x, y]) $ map VarP pns
        expr = foldl1 (\x y -> apps [VarE 'alongside, x, y]) $ map snd args
    out <- comp expr (fe pat' $ map VarE pns)
    return (pat, out)

  doExpr :: [Name] -> Exp -> Q (Pat, Exp)

--TODO: have customization for strictness
  doExpr _ e@(LitE l) = (\e' -> (LitP l   , e')) <$> constLens e
  doExpr _ e@(ConE n) = (\e' -> (ConP n [], e')) <$> constLens e

  doExpr vs (VarE vn)
    | vn `elem` vs = do
        p <- varP vn
        e <- varE 'id
        return (p, e)
    | otherwise = rFail $ "Non-lens variable " ++ pprint vn ++ " cannot be used in that way."

  doExpr vs e@(AppE _ _) = case collectAppE e [] of
    (ConE n:args) -> doCompound (\p es -> bijLens p . apps $ ConE n : es) vs args
    (VarE n:args)
      | not . any (`elem` vs) $ namesIn (init args)
        -> do (pat, expr) <- doExpr vs (last args)
              expr' <- comp expr (return . apps $ VarE n : init args)
              return (pat, expr')
      | otherwise
        -> rFail $ "Last parameter of function " ++ pprint n ++ " must be a lens variable."
    (InfixE l o r:args) -> do
      ifx <- doInfix l o r
      doExpr vs . apps $ ifx ++ args

  doExpr vs (TupE        es) = doCompound (\p -> bijLens p . TupE)        vs es
  doExpr vs (UnboxedTupE es) = doCompound (\p -> bijLens p . UnboxedTupE) vs es
  doExpr vs (ListE       es) = doCompound (\p -> bijLens p . ListE)       vs es

  doExpr vs (SigE e t) = do
    (p, e') <- doExpr vs e
    res <- comp e'
         $ sigE (varE 'id) [t| Simple Traversal $(varT =<< newName "a") $(return t) |]
    return (p, res)

  doExpr vs (ParensE e) = doExpr vs e
  doExpr vs (InfixE (Just l) o (Just r)) = doCompound (\p [e] -> return $ AppE (AppE o l) e) vs [r]

  doExpr _ e = rFail $ "Expression " ++ pprint e ++ " has no pattern equivalent."

  doInfix Nothing o Nothing = return [o]
  doInfix (Just l) o Nothing = return [o, l]
  doInfix (Just l) o (Just r) = return [o, l, r]
  doInfix _ _ _ = rFail "Right sections aren't supported."


  allVarP = everything (++) $ [] `mkQ` \x ->
    case x of
      (VarP n) -> [n]
      _ -> []

  isVarP (VarP _) = True
  isVarP _ = False

  namesIn :: Data a => a -> [Name]
  namesIn = listify (const True :: Name -> Bool)

  allNames = namesIn (matchPat, matchExp)

-- Name prefix of the non-changing variables in the structure.
  varName = fromJust . find (\v -> not . any (v `isPrefixOf`) $ map nameBase allNames)
          $ iterate ('\'':) "x"

-- Replace wildcard with new variable.
  replaceWild WildP = VarP <$> newName varName
  replaceWild p     = return p

-- | Converts a pattern to an expression.
-- Almost looks like a traversal, but isn't!
patToExp :: Applicative f => (Pat -> f Exp) -> Pat -> f Exp
patToExp _ (LitP l)         = pure $ LitE l
patToExp _ (VarP n)         = pure $ VarE n
patToExp f (TupP ps)        = TupE                     <$> traverse (patToExp f) ps
patToExp f (UnboxedTupP ps) = UnboxedTupE              <$> traverse (patToExp f) ps
patToExp f (ListP ps)       = ListE                    <$> traverse (patToExp f) ps
patToExp f (ConP n ps)      = List.foldl AppE (ConE n) <$> traverse (patToExp f) ps
patToExp f (RecP n fs)      = RecConE n                <$> traverse (_2 $ patToExp f) fs
patToExp f (InfixP l n r)   = InfixE  <$> (Just <$> patToExp f l) <*> pure (VarE n) <*> (Just <$> patToExp f r)
patToExp f (UInfixP l n r)  = UInfixE <$>           patToExp f l  <*> pure (VarE n) <*>           patToExp f r
patToExp f (SigP p t)       = SigE                     <$> patToExp f p <*> pure t
patToExp f (ParensP p)      = ParensE                  <$> patToExp f p
patToExp f (TildeP p)       = patToExp f p
patToExp f (BangP p)        = patToExp f p
patToExp f p                = f p

-- | Converts an expression to a pattern.
-- Almost looks like a traversal, but isn't!
expToPat :: Applicative f => (Exp -> f Pat) -> Exp -> f Pat
expToPat _ (LitE l)         = pure $ LitP l
expToPat _ (VarE n)         = pure $ VarP n
expToPat _ (ConE n)         = pure $ ConP n []
expToPat f (TupE ps)        = TupP        <$> traverse (expToPat f) ps
expToPat f (UnboxedTupE ps) = UnboxedTupP <$> traverse (expToPat f) ps
expToPat f (ListE ps)       = ListP       <$> traverse (expToPat f) ps
expToPat f (RecConE n fs)   = RecP n      <$> traverse (_2 $ expToPat f) fs 
expToPat f ( InfixE (Just l) (ConE n) (Just r)) =  InfixP <$> expToPat f l <*> pure n <*> expToPat f r
expToPat f (UInfixE       l  (ConE n)       r ) = UInfixP <$> expToPat f l <*> pure n <*> expToPat f r
expToPat f (SigE p t)       = SigP        <$> expToPat f p <*> pure t
expToPat f (ParensE p)      = ParensP     <$> expToPat f p
expToPat f e@(AppE _ _) = case collectAppE e [] of
  (ConE n:xs) -> ConP n <$> traverse (expToPat f) xs
  _ -> f e
expToPat f e = f e

collectAppE :: Exp -> [Exp] -> [Exp]
collectAppE (AppE l r) xs = collectAppE l (r:xs)
collectAppE x xs = x:xs


imposs = rFail . ("The impossible happened!! " ++)
--  rFail = (>> return undefined) . report True  . ("LENQ: "++)
rFail = error . ("LENQ: "++)
rWarn = (>> return undefined) . report False . ("LENQ: "++)