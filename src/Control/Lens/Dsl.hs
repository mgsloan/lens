{-# LANGUAGE TemplateHaskell, CPP #-}
module Control.Lens.Dsl where

import Control.Applicative
import Control.Lens
import Control.Monad (when)
import Data.Generics (Data, extT, extM, mkQ, everything, everywhere, everywhereM, listify, gmapT, gmapM)
import Data.List as List
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax


--TODO: use.
data LenqPartial = IgnorePartial | TraversePartial | WarnPartial | ErrorPartial

data LenqType = LenqLens | LenqIsomorphism | LenqTraversal | LenqProjection

data LenqConf = LenqConf
  { _lenqType :: LenqType
  , _lenqPartial :: LenqPartial
  }

$(makeLenses ''LenqConf)


-- TODO: multiif, lambda case
-- TODO: guards??

lensConf :: LenqConf
lensConf = LenqConf LenqLens WarnPartial

isoConf :: LenqConf
isoConf = LenqConf LenqIsomorphism WarnPartial

traversalConf :: LenqConf
traversalConf = LenqConf LenqTraversal TraversePartial

lenq :: ExpQ -> ExpQ
lenq = lenqExp lensConf

lenqIso :: ExpQ -> ExpQ
lenqIso = lenqExp isoConf

lenqTraversal :: ExpQ -> ExpQ
lenqTraversal = lenqExp traversalConf

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
    let ips = init ps
    case conf ^. lenqType of
      LenqIsomorphism -> do
        fr <- newName "fr"
        to <- newName "to"
        vs <- mapM (const $ newName "v") ips
        lamE (map varP vs)
          . letE [ funD fr $ map (isoClause conf True  ips) ms
                 , funD to $ map (isoClause conf False ips) ms ]
          $ appsE
          [ varE 'iso
          , appsE . map varE $ fr : vs
          , appsE . map varE $ to : vs
          ]
      _ -> do
        v <- newName "_v"
        f <- newName "_f"
        ms' <- mapM (lensMatch conf f) ms
        return . LamE (ips ++ [VarP f, VarP v]) $ CaseE (VarE v) ms'

lenqDecs :: LenqConf -> DecsQ -> DecsQ

lenqDecs conf decs = mapM doLens =<< decs
 where
  --
  doLens (FunD n cs)
  {-
    | conf ^. lenqType == LenqIsomorphism = do
        fr <- newName "fr"
        to <- newName "to"
        let (Clause patsExample _ _:_) = cs
        vs <- map (const $ newName "v") patsExample
        funD n'
          ( appsE [ varE 'iso
                  , appsE . map varE $ fr : vs
                  , appsE . map varE $ to : vs
                  ]
          )
          $ map isoClause cs
     where
      isoClause (Clause ps b ds) =
        let ips = init ps
            lp = last ps
        Match lp (NormalB ) ds
        cls <- isoClause conf
        clause
        [ funD fr $ map (isoClause conf True  ips) ms
                 , funD to $ map (isoClause conf False ips) ms ]
          $
      {-
      vs <- mapM (const $ newName "v") $ patsExample
      let expr = lenqExp conf . lamE (map varP vs)
               . caseE (varE $ last vs)
               $ map  cs
      valD (varP n') (normalB expr) []
      -}
    -}
    | otherwise = do
      let n' = mkName $ nameBase n
      f <- newName "f"
      funD n' . map (\c -> toClause <$> lensMatch conf f (fromJust $ toMatch c))
              $ processNames (M.singleton n n') cs
  doLens _ = rFail "Can only use lenq on function declarations."

-- TODO: extract out match checking to elsewhere (duplicated in lensMatch)
isoClause :: LenqConf -> Bool -> [Pat] -> Match -> Q Clause
isoClause _ _ _ (Match _ (GuardedB _) _) = rFail "Guard statements not yet supported."
isoClause conf forward ips (Match p (NormalB e) wheres) = do
  when (not $ null wheres) $ rFail "Where statements not yet supported."
  (p', e') <- if forward then return (p, processForward e) else
    (,) <$> expToPat processBackward e <*> patToExpFail p p
  return $ Clause (ips ++ [p']) (NormalB e') []
 where
  processForward :: Exp -> Exp
  processForward e@(AppE l r) = case collectAppE e [] of
    (ConE n:args) -> apps $ ConE n : map processForward args
    _ -> apps $ [VarE 'view, l, processForward r]
  processForward e = gmapT (id `extT` processForward) e

  recBackward :: Exp -> Q Pat
  recBackward = expToPat processBackward

  processBackward :: Exp -> Q Pat
  processBackward e@(AppE l r) = case collectAppE e [] of
    (ConE n:args) -> conP n $ map recBackward args
    _ -> viewP (appE (varE 'view) $ appE (varE 'from) (return l))
       $ recBackward r
  processBackward e = recBackward e

{-
traversalMatch :: LenqConf -> Name -> Match -> Q Match
traversalMatch _ _ (Match _ (GuardedB _) _) = rFail "Guard statements not yet supported."
traversalMatch conf f (Match matchPat (NormalB matchExp) wheres) = do
  when (not $ null wheres) $ rFail "Where statements not yet supported."
  pat <- everywhereM (return `extM` replaceWild)
-}

lensMatch :: LenqConf -> Name -> Match -> Q Match
lensMatch _ _ (Match _ (GuardedB _) _) = rFail "Guard statements not yet supported."
lensMatch conf f (Match matchPat (NormalB matchExp) wheres) = do
  when (not $ null wheres) $ rFail "Where statements not yet supported."

  let vs = allVarP matchPat

  (outTup, inExp) <- doExpr vs matchExp

  let dups = filter null . map tail . groupBy (==) . sort $ namesIn outTup

  when (null dups) . rFail
    $ "Cannot use a lens variable multiple times in an expression.  The following are duplicates:"
    ++ show dups

  inTup  <- patToExp (const $ imposs "In converting pattern for outer tuple representation.") outTup

  -- Replaces wildcards with variables, to preserve non-overwritten variables
  pat <- everywhereM (return `extM` replaceWild) matchPat
  outExp <- patToExpFail matchPat pat

  let expr = InfixE (Just $ LamE [outTup] outExp)
                    (VarE '(<$>))
                    (Just $ AppE (AppE inExp (VarE f)) inTup)

  return $ Match pat (NormalB expr) []
 where
  lamLens p e p' p'' e' = appsE [varE 'lens, lamE [p] e, lamE [p', p''] e']

  bijLens p e = lamLens (return p) (return e) wildP
    (expToPat (const $ imposs "When doing exp-to-pat for constructor-tuple bijection in lens.") e)
    (patToExp (const $ imposs "When doing pat-to-exp for constructor-tuple bijection in lens.") p)

  constLens e = lamLens wildP (return e) wildP wildP (return e)

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
    (InfixE l o r:args) -> do
      ifx <- doInfix l o r
      doExpr vs . apps $ ifx ++ args
    args
      | not . any (`elem` vs) $ namesIn (init args)
        -> do (pat, expr) <- doExpr vs (last args)
              expr' <- comp expr (return . apps $ init args)
              return (pat, expr')
      | otherwise
        -> rFail $ "All but the last parameter of " ++ pprint (head args) ++ " cannot contain lens variables."

  doExpr vs (TupE        es) = doCompound (\p -> bijLens p . TupE)        vs es
  doExpr vs (UnboxedTupE es) = doCompound (\p -> bijLens p . UnboxedTupE) vs es
  doExpr vs (ListE       es) = doCompound (\p -> bijLens p . ListE)       vs es

  doExpr vs (SigE e t) = do
    (p, e') <- doExpr vs e
    res <- comp e'
         $ sigE (varE 'id) [t| Simple Traversal $(varT =<< newName "a") $(return t) |]
    return (p, res)

  doExpr vs (ParensE e) = doExpr vs e
  doExpr vs (InfixE (Just l) o (Just r)) = doCompound (\_ [e] -> return $ AppE (AppE o l) e) vs [r]

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
          $ iterate (++"'") "x"

-- Replace wildcard with new variable.
  replaceWild WildP = VarP <$> newName varName
  replaceWild p     = return p

-- Takes unique names and makes them plain.
processNames :: Data a => M.Map Name Name -> a -> a
processNames mp = everywhere (id `extT` process)
 where
  process n = case M.lookup n mp of
    Just n' -> n'
    Nothing | isU n -> mkName $ pprint n
            | otherwise -> n
  isU (Name _ (NameU _)) = True
  isU _ = False

patToExpFail :: Applicative f => Pat -> Pat -> f Exp
patToExpFail userp p = patToExp (\pp -> rFail $ "Pattern " ++ pprint pp ++ ", from within " ++ pprint userp ++ " has no expression equivalent.") p

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
patToExp f (InfixP l n r)   = InfixE  <$> (Just <$> patToExp f l) <*> pure (ConE n) <*> (Just <$> patToExp f r)
patToExp f (UInfixP l n r)  = UInfixE <$>           patToExp f l  <*> pure (ConE n) <*>           patToExp f r
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

apps = foldl1 AppE

-- clauseToMatch :: Projection Clause Match
-- clauseToMatch = projection toClause toMatch

toClause :: Match -> Clause
toClause (Match p b ds) = Clause [p] b ds
toMatch :: Clause -> Maybe Match
toMatch (Clause [p] b ds) = Just $ Match p b ds
toMatch _ = Nothing

imposs :: String -> a
imposs = rFail . ("The impossible happened!! " ++)
rFail :: String -> a
--  rFail = (>> return undefined) . report True  . ("LENQ: "++)
rFail = error . ("LENQ: "++)
rWarn :: String -> Q a
rWarn = (>> return undefined) . report False . ("LENQ: "++)