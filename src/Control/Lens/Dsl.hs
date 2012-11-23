{-# LANGUAGE TemplateHaskell, CPP, TypeOperators, RankNTypes #-}
module Control.Lens.Dsl
  ( (:->:), (:=>:), (:<->:), LenqLens, LenqTraversal, LenqIso
  , lenq, lense, traversale, isoe
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad         (when)
import Data.Generics         (Data, extT, extM, mkQ, everything, everywhereM, listify, gmapT)
import Data.List as List
import qualified Data.Map as Map
import Language.Haskell.TH
import Language.Haskell.TH.Lens

type a :->:  b = a -> b
type a :=>:  b = a -> [b]
type a :<->: b = a -> b

type LenqLens      a b c d = a -> c
type LenqTraversal a b c d = a -> [c]
type LenqIso       a b c d = a -> c

lenq :: DecsQ -> DecsQ
lenq = (>>= lenqDecs)

lense, traversale, isoe :: ExpQ -> ExpQ
lense      = (>>= lenqExp LensVariety)
isoe       = (>>= lenqExp IsoVariety)
traversale = (>>= lenqExp TraversalVariety)

-- TODO: multiif, lambda case
-- TODO: guards!??

-- TODO: how would we handle a "x * y" where both are lens names?
type LenqFunc = Map.Map (Name, Int) Name

-- Enumeration of supported lens library types

-- (Traversal and Projection are still TODO)
-- Desired variety of lens library type (determines the conversion process).
-- This is a helper enumeration
data LenqVariety = LensVariety | IsoVariety | TraversalVariety | ProjectionVariety
  deriving (Eq, Show)

-- Internal helper function used to implement lense / traversale / isoe.
lenqExp :: LenqVariety -> Exp -> ExpQ
lenqExp variety (ParensE e) = lenqExp variety e
lenqExp variety expr = case expr of
  (LamE ps (CaseE e ms)) -> checkCase (last ps) ps e ms
  (LamE ps e) -> buildExp ps [Match (last ps) (NormalB e) []]
  _ -> lenqError "Expected a lambda expression and an optional case statement."
 where
  checkCase (VarP v) ps e ms | (VarE v == e) = buildExp ps ms
  checkCase _ _ _ _ = lenqError "Case statements must just case on the last parameter."
  buildExp ps ms = do
    func <- newName "func"
    dec <- lenqFunc variety func $ map (\(Match p b ds) -> Clause [p] b ds) ms
    return . LamE (init ps) $ LetE [dec] (VarE func)

-- Internal helper function used to implement lenq.  It consumes a list of
-- functions, and converts them to Lenses / Isos / Traversals.  This transformation
-- is conditional on the types.
lenqDecs :: [Dec] -> DecsQ
lenqDecs ds = fmap concat $ mapM doLens ds
 where
-- Map from names to types.
  sigMap = Map.fromList [(n, t) | SigD n t <- ds]

  doLens (FunD n cs) = case Map.lookup n sigMap of
-- By default they're treated as traversals
    Nothing -> fmap (:[]) $ lenqFunc TraversalVariety n cs
    (Just t) -> fmap (\dec -> [SigD n t', dec]) $ lenqFunc variety n cs
--"variety" determines how the transformation will proceed, while t' is the rewritten type
      where (variety, t') = processLenqType n t
  doLens (SigD _ _) = return []
  doLens _ = lenqError "Function declarations and signatures only."

processLenqType :: Name -> Type -> (LenqVariety, Type)
processLenqType n sigType =

  let simpleLensT      l r = (LensVariety,      rebuild $ appsT [ConT ''SimpleLens,      l, r])
      simpleTraversalT l r = (TraversalVariety, rebuild $ appsT [ConT ''SimpleTraversal, l, r])
      simpleIsoT       l r = (IsoVariety,       rebuild $ appsT [ConT ''SimpleIso,       l, r])

      traverseType f t@(ForallT _ _ _) = (traverseArrowT . forallLens) f t
      traverseType f t = traverseArrowT f t

      (Context rebuild resultType) = last $ holesOf traverseType sigType

  in case resultType of
-- Operators for the Simple types
      (AppT (AppT (ConT op) l) r)
        | op == ''(:->:)  -> simpleLensT      l r
        | op == ''(:=>:)  -> simpleTraversalT l r
        | op == ''(:<->:) -> simpleIsoT       l r
-- Usage of the "Simple" type synonym
      (AppT (AppT (AppT (ConT simpl) (ConT op)) l) r)
        | (simpl, op) == (''Simple, ''LenqLens)      -> simpleLensT      l r
        | (simpl, op) == (''Simple, ''LenqTraversal) -> simpleTraversalT l r
        | (simpl, op) == (''Simple, ''LenqIso)       -> simpleIsoT       l r
-- Full types given
      (AppT (AppT (AppT (AppT (ConT op) a) b) c) d)
        | op == ''LenqLens      -> (LensVariety,      rebuild $ appsT [ConT ''Lens,      a, b, c, d])
        | op == ''LenqTraversal -> (TraversalVariety, rebuild $ appsT [ConT ''Traversal, a, b, c, d])
        | op == ''LenqIso       -> (IsoVariety,       rebuild $ appsT [ConT ''Iso,       a, b, c, d])
-- Fallthrough case
      _ -> lenqError $ unlines
         [ "Expected a Lens, Traversal, or Iso in type signature of " ++ pprint n ++ "."
         , "In particular, this portion: " ++ pprint sigType
         ]


-- This is where the commonality between "lenqExp" and "lenqDecs" starts.
-- This function takes the variety of lens to produce, the name of the function
-- that should be generated
lenqFunc :: LenqVariety -> Name -> [Clause] -> DecQ
lenqFunc variety n cs = case variety of
  LensVariety -> do
    f <- newName "f"
    funD n $ map (lensClause f) cs
  IsoVariety -> do
    g <- newName "g"
    h <- newName "h"
    let (Clause pats _ _:_) = cs
    vs <- mapM (const $ newName "v") (tail pats)
    let body = normalB $ appsE
             [ varE 'iso
             , appsE . map varE $ g : vs
             , appsE . map varE $ h : vs
             ]
    funD n
      [clause (map varP vs) body
        [ funD g $ map (isoClause True ) cs
        , funD h $ map (isoClause False) cs
        ]
      ]
  _ -> lenqError $ show variety ++ " not yet supported."

-- Not really an isomorphism due to error partialness
checkedClause :: Simple Iso Clause ([Pat], Pat, Exp)
checkedClause = iso f g
 where
  f (Clause _ (GuardedB _) _) = lenqError "Guard statements not yet supported."
  f (Clause ps (NormalB e) ws)
    | null ps                  = lenqError "Lenq requires at least one pattern match."
    | not $ null ws            = lenqError "Where statements not yet supported."
    | otherwise                = (init ps, last ps, e)
  g (ps, p, e) = Clause (ps ++ [p]) (NormalB e) []

-- TODO: A better definition ought to exist.
overM :: Monad m => Lens a b c d -> (c -> m d) -> a -> m b
overM l f x = do
  v' <- f $ x ^. l
  return $ set l v' x

isoClause :: Bool -> Clause -> Q Clause
isoClause forward = overM checkedClause $ \(ps, p, expr) -> do
  (p', e') <- if forward then return (p, processForward expr) else
    (,) <$> expToPat processBackward expr <*> patToExpFail p p
  return (ps, p', e')
 where
  processForward :: Exp -> Exp
  processForward e@(AppE l r) = case toListOf traverseAppE e of
    (ConE n:args) -> apps $ ConE n : map processForward args
    _ -> apps $ [VarE 'view, l, processForward r]
  processForward e = gmapT (id `extT` processForward) e

  recBackward :: Exp -> Q Pat
  recBackward = expToPat processBackward

  processBackward :: Exp -> Q Pat
  processBackward e@(AppE l r) = case toListOf traverseAppE e of
    (ConE n:args) -> conP n $ map recBackward args
    _ -> viewP (appE (varE 'view) $ appE (varE 'from) (return l))
       $ recBackward r
  processBackward e = recBackward e

{-
traversalClause :: Name -> Clause -> Q Clause
traversalClause f = overM checkedClause $ \(pats, pat, expr) -> do
  let vars = allVarP p

  (outs, inExps) <- doExpr vars expr

  checkNames $ vars ++ outs

  pat' <- everywhereM (return `extM` replaceWild) pat
  outExp <- patToExpFail pat pat'

  case inExps of
    [] -> return $ AppE (VarE 'pure) outExp
    (e1:rest) -> return $ foldr (\l r -> InfixE (Just l) (VarE '(<*>)) (Just r)) initial rest
     where
      initial = InfixE
        (Just $ LamE (map VarE outs) outExp)
        (VarE '(<$>))
        (Just e1)
-}

checkNames :: [Name] -> Q ()
checkNames ns = do
  let grouped  = groupBy (==) $ sort ns
      showEm   = show . map (mkName . nameBase . head)
      unused   = filter ((<=1) . length) grouped
      overused = filter ((>2)  . length) grouped

  when (not (null unused) || not (null overused)) . lenqError . unlines
    $ [ "Variables bound in the lens pattern must be used exactly once in the result." ]
    ++ (if null unused   then [] else ["The following are unused: "  ++ showEm unused  ])
    ++ (if null overused then [] else ["The following are overused:" ++ showEm overused])

lensClause :: Name -> Clause -> Q Clause
lensClause f = overM checkedClause $ \(pats, pat, expr) -> do
  let vars = allVarP pat

  (outTup, inExp) <- doExpr vars expr

  checkNames $ vars ++ namesIn outTup

  inTup <- patToExp (const $ impossible "In converting pattern for outer tuple representation.") outTup

  -- Replaces wildcards with variables, to preserve non-overwritten variables
  pat' <- everywhereM (return `extM` replaceWild) pat
  outExp <- patToExpFail pat pat'

  let expr' = InfixE (Just $ LamE [outTup] outExp)
                     (VarE '(<$>))
                     (Just $ AppE (AppE inExp (VarE f)) inTup)

  return (pats ++ [VarP f], pat', expr')
 where
  lamLens p e p' p'' e' = appsE [varE 'lens, lamE [p] e, lamE [p', p''] e']

  bijLens p e = lamLens (return p) (return e) wildP
    (expToPat (const $ impossible "When doing exp-to-pat for constructor-tuple bijection in lens.") e)
    (patToExp (const $ impossible "When doing pat-to-exp for constructor-tuple bijection in lens.") p)

  constLens e = lamLens wildP (return e) wildP wildP (return e)

  composed l = infixE (Just $ return l) (varE '(.)) . Just

  -- This isn't gonna cut it - gotta inline alongside??
  doCompound :: (Pat -> [Exp] -> ExpQ) -> [Name] -> [Exp] -> Q (Pat, Exp)
  doCompound fe vs es = do
    args <- mapM (doExpr vs) es
    pns <- mapM (const $ newName "x") es
    let pat  = foldl1 (\x y -> TupP                  [x, y]) $ map fst args
        pat' = foldl1 (\x y -> TupP                  [x, y]) $ map VarP pns
        expr = foldl1 (\x y -> apps [VarE 'alongside, x, y]) $ map snd args
    out <- composed expr (fe pat' $ map VarE pns)
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
    | otherwise = lenqError $ "Expected a variable bound in the lens pattern. " ++ pprint vn ++ " comes from elsewhere."

  doExpr vs e@(AppE _ _) = case toListOf traverseAppE e of
    (ConE n:xs) -> doCompound (\p es -> bijLens p . apps $ ConE n : es) vs xs 
    (InfixE l o r:xs) -> doExpr vs . apps $ doInfix l o r ++ xs
    [VarE n, l, r] | n == '(^.) -> doExpr vs $ apps [r, l]
                   | n == 'view -> doExpr vs $ apps [l, r]
    xs -> case filter (any (`elem` vs) . namesIn) $ init xs of
      [] -> do
        (pat, expr) <- doExpr vs (last xs)
        expr' <- composed expr (return . apps $ init xs)
        return (pat, expr')
      ps -> lenqError $ unlines
        [ "The following arguments of " ++ pprint (head xs) ++ " reference variables bound in the lens pattern:"
        , unwords . ("[":) . (++["]"]) . intersperse "," $ map pprint ps
        , "Only use lens pattern variables in the last argument."
        ]
  doExpr vs (InfixE l o r) = doExpr vs . apps $ doInfix l o r

  doExpr vs (TupE        es) = doCompound (\p -> bijLens p . TupE)        vs es
  doExpr vs (UnboxedTupE es) = doCompound (\p -> bijLens p . UnboxedTupE) vs es
  doExpr vs (ListE       es) = doCompound (\p -> bijLens p . ListE)       vs es

  doExpr vs (SigE e t) = do
    (p, e') <- doExpr vs e
    res <- composed e'
         $ sigE (varE 'id) [t| Simple Traversal $(varT =<< newName "a") $(return t) |]
    return (p, res)

  doExpr vs (ParensE e) = doExpr vs e

  doExpr _ e = lenqError $ "Expression " ++ pprint e ++ " has no pattern equivalent."

  doInfix Nothing o Nothing = [o]
  doInfix (Just l) o Nothing = [o, l]
  doInfix (Just l) o (Just r) = [o, l, r]
  doInfix _ _ _ = lenqError "Right sections aren't supported."

  allVarP = everything (++) $ [] `mkQ` \x ->
    case x of
      (VarP n) -> [n]
      _ -> []

  isVarP (VarP _) = True
  isVarP _ = False

  namesIn :: Data a => a -> [Name]
  namesIn = listify (const True :: Name -> Bool)

-- Replace wildcard with new variable.
replaceWild :: Pat -> PatQ
replaceWild WildP = VarP <$> newName "x"
replaceWild p     = return p

patToExpFail :: Applicative f => Pat -> Pat -> f Exp
patToExpFail userp = patToExp (lenqError . msg)
  where
    msg pp = "Pattern " ++ pprint pp ++ ", from within " ++ pprint userp ++ " has no expression equivalent."

-- | Converts a pattern to an expression, with a user-provided function for failure cases.
-- Almost looks like a traversal, but isn't!
patToExp :: Applicative f => (Pat -> f Exp) -> Pat -> f Exp
patToExp _ (LitP l)         = pure $ LitE l
patToExp _ (VarP n)         = pure $ VarE n
patToExp f (ConP n ps)      = consE n     <$> traverse (patToExp f) ps
patToExp f (TupP ps)        = TupE        <$> traverse (patToExp f) ps
patToExp f (UnboxedTupP ps) = UnboxedTupE <$> traverse (patToExp f) ps
patToExp f (ListP ps)       = ListE       <$> traverse (patToExp f) ps
patToExp f (RecP n fs)      = RecConE n   <$> traverse (_2 $ patToExp f) fs
patToExp f (SigP p t)       = SigE        <$> patToExp f p <*> pure t
patToExp f (ParensP p)      = ParensE     <$> patToExp f p
patToExp f (UInfixP l n r)  = UInfixE <$>           patToExp f l  <*> pure (ConE n) <*>           patToExp f r
patToExp f (InfixP l n r)   = InfixE  <$> (Just <$> patToExp f l) <*> pure (ConE n) <*> (Just <$> patToExp f r)
patToExp f (TildeP p)       = patToExp f p
patToExp f (BangP p)        = patToExp f p
patToExp f p                = f p

-- | Converts an expression to a pattern, with a user-provided function for failure cases.
-- Almost looks like a traversal, but isn't!
expToPat :: Applicative f => (Exp -> f Pat) -> Exp -> f Pat
expToPat _ (LitE l)         = pure $ LitP l
expToPat _ (VarE n)         = pure $ VarP n
expToPat _ (ConE n)         = pure $ ConP n []
expToPat f e@(AppE _ _) = case e ^.. traverseAppE of
  (ConE n:xs) -> ConP n <$> traverse (expToPat f) xs
  _ -> f e
expToPat f (TupE ps)        = TupP        <$> traverse (expToPat f) ps
expToPat f (UnboxedTupE ps) = UnboxedTupP <$> traverse (expToPat f) ps
expToPat f (ListE ps)       = ListP       <$> traverse (expToPat f) ps
expToPat f (RecConE n fs)   = RecP n      <$> traverse (_2 $ expToPat f) fs 
expToPat f (SigE p t)       = SigP        <$> expToPat f p <*> pure t
expToPat f (ParensE p)      = ParensP     <$> expToPat f p
expToPat f (UInfixE       l  (ConE n)       r ) = UInfixP <$> expToPat f l <*> pure n <*> expToPat f r
expToPat f ( InfixE (Just l) (ConE n) (Just r)) =  InfixP <$> expToPat f l <*> pure n <*> expToPat f r
expToPat f e = f e

apps :: [Exp] -> Exp
apps = foldl1 AppE

consE :: Name -> [Exp] -> Exp
consE n = apps . (ConE n:)

appsT :: [Type] -> Type
appsT = foldl1 AppT

impossible :: String -> a
impossible = lenqError . ("The impossible happened!! " ++)

lenqError :: String -> a
--  lenqError = (>> return undefined) . report True  . ("LENQ: "++)
lenqError = error . ("LENQ: "++)

rWarn :: String -> Q a
rWarn = (>> return undefined) . report False . ("LENQ: "++)


{-
traversalMatch :: LenqConf -> Name -> Match -> Q Match
traversalMatch _ _ (Match _ (GuardedB _) _) = lenqError "Guard statements not yet supported."
traversalMatch conf f (Match matchPat (NormalB matchExp) wheres) = do
  when (not $ null wheres) $ lenqError "Where statements not yet supported."
  pat <- everywhereM (return `extM` replaceWild)
-}

{-
lensConf :: LenqConf
lensConf = LenqConf LenqLens WarnPartial

isoConf :: LenqConf
isoConf = LenqConf LenqIso WarnPartial

traversalConf :: LenqConf
traversalConf = LenqConf LenqTraversal TraversePartial

lenq :: ExpQ -> ExpQ
lenq = lenqExp lensConf

lenqIso :: ExpQ -> ExpQ
lenqIso = lenqExp isoConf

lenqTraversal :: ExpQ -> ExpQ
lenqTraversal = lenqExp traversalConf
-}

-- Takes unique names and makes them plain.
{-
processNames :: Data a => M.Map Name Name -> a -> a
processNames mp = everywhere (id `extT` process)
 where
  process n = case M.lookup n mp of
    Just n' -> n'
    Nothing | isU n -> mkName $ pprint n
            | otherwise -> n
  isU (Name _ (NameU _)) = True
  isU _ = False
-}
