{-# LANGUAGE QuasiQuotes, FlexibleInstances #-}
module Language.Javascript.JMacro.Typed where

import Prelude hiding (tail, init, head, last, minimum, maximum, foldr1, foldl1, (!!), read)

import Language.Javascript.JMacro.Base
import Language.Javascript.JMacro.QQ
import Control.Monad
import Control.Monad.State
import Control.Monad.Error
import Control.Applicative
import Data.List (intercalate, deleteFirstsBy, find)
import Data.Function(on)
import qualified Data.Map as M
import Data.Map(Map)
import Data.Maybe(fromMaybe)
import qualified Data.Set as S
import Data.Set(Set)
import Text.PrettyPrint.HughesPJ
import Debug.Trace


--todo: collect errors
--pretty types, bump down variable nums
--infer missing vs. assert missing
--type parser
--intersection types
--lists, new/this, extensible records
--flag to automatically introduce new things into environment
--seperate resAtoms function

{--------------------------------------------------------------------
  Main Interface
--------------------------------------------------------------------}

runTypecheck :: JTypeCheck a => a -> IO ()
runTypecheck x =  either putStrLn print $ evalState (runErrorT go) tcStateEmpty
    where go = do
            res <- typecheck x
            showenv <- do
                 (env:topenv:_) <- tc_env <$> get
                 r@(JTRec i) <- newRec
                 putRec i (M.toList env)
                 r'@(JTRec i') <- newRec
                 putRec i' (M.toList topenv)
--                 killSats
                 s <- showType r
                 s' <- prettyType' r'
                 pres <- showType res
                 return (pres,s,s')
            return showenv

{--------------------------------------------------------------------
  Types
--------------------------------------------------------------------}

data JType = JTNum
           | JTStr
           | JTBool
           | JTRec Int
           | JTFunc [JType] JType
           | JTList (Maybe Int) (Maybe JType) --can be multityped, monotyped, or neither
                                              --jtint is an index into a record
           | JTStat
           | JTSat Int
           | BotOf JType
           | JTVar Int deriving (Show, Eq)

data JConstr = Sub JType | Super JType deriving Show

--canextend needs scoping, to deal with inner lambdas. oyvey. things can only be extended in the scope that they are introduced in. this scoping should be introduced in a scopedRecs thang
data TCState = TCS {tc_env :: [Map Ident JType],
                    tc_vars :: Map Int JType,
                    tc_constrs :: Map Int [JConstr],
                    tc_recs :: Map Int [(Ident, JType)],
                    tc_scopedSat :: [Set Int],
                    tc_varCt :: Int,
                    tc_strictnull :: Bool,
                    tc_canextend :: Bool,
                    tc_debug :: Bool,
                    tc_expandFree :: Bool} deriving Show

tcStateEmpty :: TCState
tcStateEmpty = TCS [M.empty,M.empty] M.empty M.empty M.empty [S.empty] 0 True True True True


type JMonad a = ErrorT String (State TCState) a

orElse :: JMonad a -> JMonad a -> JMonad a
x `orElse` y = do
  st <- get
  x `catchError` \e1 -> do
       put st
       y `catchError` \e2 -> do
          throwError $ e1 ++ ",\n" ++ e2

{--------------------------------------------------------------------
  Env utilities
--------------------------------------------------------------------}

--fix to maybe do it, or insert top level
lookupEnvErr :: Ident -> JMonad JType
lookupEnvErr i@(StrI s) = do
  ans <- msum . map (M.lookup i) . tc_env <$> get
  case ans of
    Just x -> return x
    Nothing -> do
             b <- tc_expandFree <$> get
             if b
                then do
                  ns <- newTopSat
                  addTopEnv i ns
                  return ns
                else throwError $ "Variable not in scope: " ++ s

--puts idents in scope, as constrained free variables
withLocalScope :: [Ident] -> JMonad a -> JMonad a
withLocalScope args act = do
  env <- tc_env <$> get
  sats <- tc_scopedSat <$> get
  modify (\tcs -> tcs {tc_scopedSat = S.empty : sats, tc_env = M.empty : env})
  mapM (addNewSat) args
  res <- act
  (_:restSats) <- tc_scopedSat <$> get
  (_:restEnv) <- tc_env <$> get
  modify (\tcs -> tcs {tc_env = restEnv, tc_scopedSat = restSats})
  return res

--puts idents in scope, as normal free variables
withLocalScope' :: [Ident] -> JMonad a -> JMonad a
withLocalScope' args act = do
  env <- tc_env <$> get
  modify (\tcs -> tcs {tc_env = M.empty : env})
  mapM (addNewVar) args
  res <- act
  (_:restEnv) <- tc_env <$> get
  modify (\tcs -> tcs {tc_env = restEnv})
  return res

inConditional :: JMonad a -> JMonad a
inConditional act = do
  oldCE <- tc_canextend <$> get
  modify (\tcs -> tcs {tc_canextend = False})
  res <- act
  modify (\tcs -> tcs {tc_canextend = oldCE})
  return res

addEnv :: Ident -> JType -> JMonad ()
addEnv i t = do
  (env:envs) <- tc_env <$> get
  modify (\tcs -> tcs {tc_env = M.insert i t env : envs})

addTopEnv :: Ident -> JType -> JMonad ()
addTopEnv i t = do
  (env:envs) <- reverse . tc_env <$> get
  modify (\tcs -> tcs {tc_env = reverse $ M.insert i t env : envs})

newV :: JMonad Int
newV = do
  x <- tc_varCt <$> get
  modify (\tcs -> tcs {tc_varCt = x + 1})
  return x

newVar :: JMonad JType
newVar = JTVar <$> newV

newSat :: JMonad JType
newSat = do
  x <- newV
  (sat:sats) <- tc_scopedSat <$> get
  modify (\tcs -> tcs {tc_scopedSat = S.insert x sat : sats})
  return (JTSat x)

addNewSat :: Ident -> JMonad ()
addNewSat i = addEnv i =<< newSat

addNewVar :: Ident -> JMonad ()
addNewVar i = addEnv i =<< newVar

newTopSat :: JMonad JType
newTopSat = do
  x <- newV
  (sat:sats) <- reverse . tc_scopedSat <$> get
  modify (\tcs -> tcs {tc_scopedSat = reverse $ S.insert x sat : sats})
  return (JTSat x)

killSats :: JMonad ()
killSats = modify (\tcs -> tcs {tc_scopedSat = [S.empty]})

newSatAtScope :: [Int] -> JMonad JType
newSatAtScope is = do
  x <- newV
  let go (s:ss) = if any (flip S.member s) is
                  then S.insert x s : ss
                  else s : go ss
      go [] = []
  modify (\tcs -> tcs {tc_scopedSat = reverse $ go $ reverse (tc_scopedSat tcs)})
--  trace ("nsas: " ++ show is ++ ", " ++ show x) $ return ()
  return (JTSat x)

satInScope :: Int -> JMonad Bool
satInScope i = any (S.member i) . tc_scopedSat <$> get

incScope :: Int -> Int -> JMonad ()
incScope i ni = do --move i up to scope of ni
  let go (s:ss) = if S.member ni s && not (S.member i s)
                  then S.insert i s : ss
                  else s : go ss
      go [] = []
  modify (\tcs -> tcs {tc_scopedSat = reverse $ go $ reverse (tc_scopedSat tcs)})


bumpScope :: Int -> JType -> JMonad ()
bumpScope i x@(JTVar _) = do
  xt <- resolveType x
  case xt of
    (JTVar _) -> return ()
    _ -> bumpScope i xt

--bump constraints?
bumpScope i (JTSat i') = incScope i' i

bumpScope i (JTFunc args ret) = do
  mapM (bumpScope i) args
  bumpScope i ret

bumpScope i(JTRec i') = mapM_ go =<< getRec i'
  where go (_,v) = bumpScope i v
bumpScope _ _ = return ()


{--------------------------------------------------------------------
  Record utilities
--------------------------------------------------------------------}

getRec :: Int -> JMonad [(Ident, JType)]
getRec i = fromMaybe [] . (M.lookup i) . tc_recs <$> get

putRec :: Int -> [(Ident, JType)] -> JMonad ()
putRec i xs = do
  recs <- tc_recs <$> get
  modify (\tcs -> tcs {tc_recs = M.insert i xs recs})

recLookup :: Ident -> JType -> JMonad (Maybe JType)
recLookup v (JTRec i) = maybe Nothing (lookup v) . M.lookup i . tc_recs <$> get
recLookup _ _ = return $ Nothing

newRec :: JMonad JType
newRec = do
  x <- tc_varCt <$> get
  modify (\tcs -> tcs {tc_varCt = x + 1})
  return (JTRec x)

{--------------------------------------------------------------------
  Constraint utilities
--------------------------------------------------------------------}

unzipConstrs :: [JConstr] -> ([JType],[JType])
unzipConstrs = foldr go ([],[])
            where
              go (Sub l)   ~(ls, rs) = (l:ls, rs)
              go (Super r) ~(ls, rs) = (ls, r:rs)

zipConstrs :: [JType] -> [JType] -> [JConstr]
zipConstrs subs supers = map Sub subs ++ map Super supers

lookupConstraints :: Int -> JMonad [JConstr]
lookupConstraints i = fromMaybe [] . M.lookup i . tc_constrs <$> get

--move simplification away from here, delay to last possible moment
addConstraint :: Int -> JConstr -> JMonad ()
addConstraint i c = do
  cs <- lookupConstraints i
  constrs <- tc_constrs <$> get
  modify (\tcs -> tcs {tc_constrs = M.insert i (c:cs) constrs})


{--------------------------------------------------------------------
  Type utilities
--------------------------------------------------------------------}

chkNoNull :: [JType] -> JMonad ()
chkNoNull xs = do
    strictnull <- tc_strictnull <$> get
    if strictnull
       then mapM_ (chkNull <=< resolveType) xs
       else return ()
  where chkNull x@(JTVar _) = tyErr1 "Attempt to return a (potentially) null variable" x
        chkNull _ = return ()

showType :: JType -> JMonad String
showType (JTVar (-1)) = return ""
showType x@(JTVar _) = do
  xt <- resolveType x
  case xt of
    (JTVar i') -> return $ "t"++show i'
    _ -> showType xt
showType (JTSat i) = do
    cs <- lookupConstraints i
    case cs of
      [] -> return $ "ct" ++ show i
      _ -> do
        cst <- mapM go cs
        return $ "ct" ++ show i ++ " <= [" ++ intercalate ", " cst ++ "]"
  where go (Sub x) = do
             str <- showType x
             return ("<: " ++ str)
        go (Super x) = do
             str <- showType x
             return (">: " ++ str)


showType JTNum = return "Num"
showType JTStr = return "String"
showType JTBool = return "Bool"
showType (JTRec i) = do
  rs <- getRec i
  strs <- mapM go rs
  return $ "{" ++ intercalate ", " strs ++ "...}"
    where go (StrI s, t) = do
                           st <- showType t
                           return (s ++ ": " ++ st)
showType (JTFunc args res) = do
  strs <- mapM showType args
  rest <- showType res
  if length strs == -1 --fixme
     then return $ concat strs ++ " -> " ++  rest
     else return $ "((" ++ intercalate ", " strs ++ ") -> " ++ rest++")"
showType JTStat = return $ "()"

showType (JTList _ (Just mono)) = do
  m <- showType mono
  return $ "[" ++ m ++ "]"

showType (JTList (Just multi) _) = do
  showType (JTRec multi)

showType (JTList Nothing Nothing) = error "trying to show bad list"

prettyType :: JType -> JMonad String
prettyType x = showType x -- =<< resC False x

prettyType' :: JType -> JMonad String
prettyType' x = showType =<< resC False x

resolveType :: JType -> JMonad JType
resolveType (JTSat i) = return $ JTSat i
resolveType (JTVar i) = do
  vars <- tc_vars <$> get
  case M.lookup i vars of
    Just t -> do
      rt <- resolveType t
      when (t /= rt) $ do
                modify (\tcs -> tcs {tc_vars = M.insert i rt vars})
      return rt
    _ -> return (JTVar i)
resolveType r@(JTRec i) = do
  (is, ts) <- unzip <$> getRec i
  ts' <-  mapM resolveType ts
  putRec i (zip is ts')
  return r

resolveType (JTFunc argst rett) = do
  argst' <- mapM resolveType argst
  rett' <- resolveType rett
  return (JTFunc argst' rett')
resolveType x = return x

resolveState :: JMonad ()
resolveState = do
  envs <- tc_env <$> get
  envs' <- forM envs $ \env ->
                      let (is,ts) = unzip $ M.toList env
                      in  M.fromList . zip is <$> mapM (resC False <=< resolveType) ts
  modify (\tcs -> tcs {tc_env = envs'})

{--------------------------------------------------------------------
  Trace/Error utilities
--------------------------------------------------------------------}

ifDbg :: JMonad () -> JMonad ()
ifDbg x = flip when x . tc_debug =<< get

traceSats :: JMonad ()
traceSats = ifDbg $ do
              ss <- tc_scopedSat <$> get
              trace ("scoped sats: " ++ show ss) $ return ()

traceVars :: JMonad ()
traceVars = ifDbg $ do
  resolveState
  vars <- tc_vars <$> get
  trace (show vars) $ return ()

traceConstrs:: JMonad ()
traceConstrs = ifDbg $ do
  resolveState
  cs <- tc_constrs <$> get
  trace (show cs) $ return ()

tyErr1 :: String -> JType -> JMonad a
tyErr1 s t = do
  st <- prettyType t
  throwError $ s ++ ": " ++ st

tyErr2 :: String -> JType -> JType -> JMonad a
tyErr2 s t t' = do
  st <- prettyType t
  st' <- prettyType t'
  throwError $ s ++ ". Expected: " ++ st ++ ", Inferred: " ++ st'

tyErr2l :: String -> [JType] -> [JType] -> JMonad a
tyErr2l s t t' = do
  sts <- mapM showType t
  sts' <- mapM showType t'
  throwError $ s ++ ". Expected: (" ++ intercalate ", " sts ++
                 "), Inferred: (" ++ intercalate "," sts' ++")"

traceTy :: String -> JType -> JMonad ()
traceTy s x = ifDbg $ do
    xt <- showType x
    trace (s ++ ": " ++ show xt) $ return ()

traceTys :: String -> JType -> JType -> JMonad ()
traceTys s x y = ifDbg $ do
       xt <- showType x
       yt <- showType y
       trace (s ++": " ++ xt ++ ", " ++ yt) $ return ()

{--------------------------------------------------------------------
  Subtyping
--------------------------------------------------------------------}

--subtype {} {x:a} fails
--subtype {x:a} {} succeeds with {}
-- x is a subtype of y
--subtype enforces subtype relation
(<:) :: JType -> JType -> JMonad ()
x <: y = do
  xr <- resolveType x
  yr <- resolveType y
  if xr == yr
     then return ()
     else traceTys "subtyping" xr yr >> subtype xr yr

subtype :: JType -> JType -> JMonad ()
subtype x@(JTSat i) y@(JTSat i') = do
  addConstraint i (Sub y)
  bumpScope i y

--assigning a free variable to a fixed type
--is incoherent, as it implies usage of a null variable
subtype x@(JTVar _) y = do
  x' <- resolveType x
  case x' of
    JTVar _ -> tyErr1 "Cannot subtype a free variable in" y
    _ -> x' <: y

--assigning to a free variable fixes it
subtype x y@(JTVar _) = do
  y' <- resolveType y
  case y' of
    JTVar _ -> do
            y' =.= x
    _ -> x <: y'

subtype x (JTSat i') = do
  cs <- lookupConstraints i'
  mapM_ go cs
  addConstraint i' (Super x)
      where go (Sub c) = x <: c
            go (Super c) = c <: x

subtype (JTSat i) y = do
  cs <- lookupConstraints i
  mapM_ go cs
  addConstraint i (Sub y)
      where go (Sub c) = c <: y
            go (Super c) = y <: c

--lookup ys in xs
subtype x@(JTRec i) y@(JTRec i') = do
  yl <- getRec i'
  xl <- getRec i
  let go [] = return ()
      go ((ident@(StrI s),v):ls) = do
            case lookup ident xl of
              Just t -> do
                        t <: v
                        go ls
              Nothing -> tyErr2 ("Couldn't subtype, missing property " ++ s) x y

  go yl


--List case
subtype x y
    | x == y = return ()
    | otherwise = tyErr2 "Couldn't subtype" x y


{--------------------------------------------------------------------
  Unification
--------------------------------------------------------------------}

--Unification should be very limited, and really only occur with
--free variables or atoms. Everything else is constraints.

--deal with constraints!?
occursCheck :: Int -> JType -> JMonad ()
occursCheck i typ = go typ >>= \b -> if b
                  then do
                    xt <- showType (JTVar i)
                    yt <- showType typ
                    throwError $ "Could not construct infinite type when unifying " ++ xt ++" and " ++ yt
                  else return ()
    where go t@(JTVar _) = resolveType t >>= \rt -> case rt of
                                                      (JTVar i') -> return (i==i')
                                                      _ -> go rt
          go (JTRec i') = or <$> (mapM (go . snd) =<< getRec i')
          go (JTFunc args ret) = or <$> mapM go (ret:args)
          go _ = return False
          --list case

--unify, but fail if first argument is free
(<=.=) :: JType -> JType -> JMonad ()
x <=.= y = do
    strictnull <- tc_strictnull <$> get
    xr <- resolveType x
    if strictnull
        then case xr of
               (JTVar _) -> tyErr1 "Attempt to use null variable as type" y
               _ -> return ()
        else return ()
    case xr of
      (JTSat _) -> xr <: y
      _ -> do
        yr <- resolveType y
        case yr of
          (JTSat _) -> yr <: xr
          _ -> xr =.= yr

(=.=) :: JType -> JType -> JMonad ()
x =.= y = do
  xr <- resolveType x
  yr <- resolveType y
  if (xr == yr)
     then return ()
     else traceTys "unifying" xr yr >> unify xr yr

unify (JTVar i) t' = do
  occursCheck i t'
  case t' of
    (JTVar i') -> do
            newt <- newVar
            vars <- tc_vars <$> get
            modify (\tcs -> tcs {tc_vars = M.insert i' newt $
                                           M.insert i  newt $
                                           vars})
    _ -> do
      vars <- tc_vars <$> get
      modify (\tcs -> tcs {tc_vars = M.insert i t' vars})

unify t t'@(JTVar _)  =  t' =.= t

--force actual unification with free vars?
{-
unify :: JType -> JType -> JMonad ()
unify (JTSat _) (JTSat _) = throwError "unification of two constrained type variables is unimplemented"

unify (JTSat i) t' = do
  cs <- lookupConstraints i
  mapM_ go cs
  let (subs,supers) = unzipConstrs cs
  luball subs
  glball supers
  addConstraint i (Sub t')
  b <- satInScope i
  when (not b) $ addConstraint i (Super t')
      where go (Sub x) = t' <: x
            go (Super x) = x <: t'

unify y x@(JTSat _) = unify x y

unify (JTRec i) (JTRec i') = do
  xl <- getRec i
  yl <- getRec i'

  --find every value in x in y, and unify each
  let go ((l,v):lvs) = case find ((==l) . fst) yl of
                         Nothing -> go lvs
                         Just (_,v') -> v =.= v'
      go _ = return ()

  go xl

  let xld = deleteFirstsBy ((==) `on` fst) xl yl --xs not in ys
      yld = deleteFirstsBy ((==) `on` fst) yl xl --ys not in xs

  putRec i  (xl++yld)
  putRec i' (yl++xld)
  return ()

unify x@(JTFunc argsx retx) y@(JTFunc argsy rety) = do
 when (length argsx /= length argsy) $ tyErr2 "Couldn't match functions" x y
 zipWithM_ (=.=) argsx argsy
 retx =.= rety
-}
unify t t' = do
  rt  <- resolveType t
  rt' <- resolveType t'
  if rt == rt'
     then return ()
     else tyErr2 "Type error" t t'


{--------------------------------------------------------------------
  Clone -- i.e. schema instantiation
--------------------------------------------------------------------}
type JMonadClone a = StateT [(Int,JType)] (ErrorT String (State TCState)) a

addSub :: (Int,JType) -> JMonadClone ()
addSub x = do
  st <- get
  put (x:st)

findSub :: Int -> JMonadClone (Maybe JType)
findSub i = do
  sub <- lookup i <$> get
  case sub of
    Just x -> do
              newsub <- case x of
                          (JTVar i') -> if i' /= i then findSub i' else return $ Just x
                          (JTRec i') -> if i' /= i then findSub i' else return $ Just x
                          (JTSat i') -> if i' /= i then findSub i' else return $ Just x
                          _ -> return $ Just x
              case newsub of
                Just ans -> return $ Just ans
                Nothing -> return $ Just x
    _ -> return Nothing

traceSubs :: JMonadClone ()
traceSubs = do
  st <- get
  trace (show st) $ return ()

traceC :: JConstr -> JMonadClone ()
traceC (Sub x) = lift $ traceTy "Sub" x
traceC (Super x) = lift $ traceTy "Super" x

clone :: JType -> JMonad JType
clone t = evalStateT (clone'' t) []

cloneMany :: [JType] -> JMonad [JType]
cloneMany ts = evalStateT (mapM clone'' ts) []

--clone just replaces free variables
clone'' :: JType -> JMonadClone JType
clone'' x = do
  lift $ traceTy "Cloning" x
  c <- clone' x
  lift $ traceTy "Clone Result" c
  return c

clone' :: JType -> JMonadClone JType
clone' x@(JTVar _) = do
  xt <- lift $ resolveType x
  case xt of
    (JTVar i) -> do
            mbsub <- findSub i
            case mbsub of
              Just sub -> return sub
              _ -> do
                   nv <- lift $ newVar
                   addSub (i,nv)
                   return $ nv
    _ -> clone' xt

clone' (JTSat i) = do
    mbsub <- findSub i
    b <- lift $ satInScope i
    case (mbsub,b) of
      (Just sub,_) -> return sub
      (_,False) -> do
        cs <- lift $ lookupConstraints i
        let (subs,supers) = unzipConstrs cs
        subs' <- mapM clone' subs
        supers' <- mapM clone' supers
        ns@(JTSat i') <- lift $ newSatAtScope [i]
        lift $ mapM (addConstraint i') $ zipConstrs subs' supers'
        addSub (i,ns)
        return ns
      _ -> do
        cs <- lift $ lookupConstraints i
        let (subs,supers) = unzipConstrs cs
        subs' <- mapM clone' subs
        supers' <- mapM clone' supers
        constrs <- lift $ tc_constrs <$> get
        lift $ modify (\tcs -> tcs {tc_constrs = M.insert i (zipConstrs subs' supers') constrs})
        addSub (i,JTSat i)
        return (JTSat i)

clone' (JTFunc args ret) = do
  args' <- mapM clone' args
  ret' <- clone' ret
  return (JTFunc args' ret')

clone' (JTRec i) = do
    mbsub <- findSub i
    case mbsub of
      Just sub -> return sub
      _ -> do
        rl <- lift $ getRec i
        rl' <- mapM go rl
        r'@(JTRec i') <- lift $ newRec
        lift $ putRec i' rl'
        return r'
  where go (i',v) = do
             v' <- clone' v
             return (i',v')

clone' (JTList mbmulti mbmono) = do
  mbmulti' <- maybe (return Nothing) (fmap Just . cloneRec) mbmulti
  mbmono'  <- maybe (return Nothing) (fmap Just . clone') mbmono
  return $ JTList mbmulti' mbmono'
         where cloneRec x = do
                 (JTRec i) <- clone' (JTRec x)
                 return i

clone' x = return x

substitute :: JType -> JMonadClone JType
substitute x@(JTVar _) = do
  xt <- lift $ resolveType x
  case xt of
    (JTVar i) -> do
            mbsub <- findSub i
            case mbsub of
              Just sub -> return sub
              _ -> return xt
    _ -> substitute xt

substitute (JTSat i) = do
    mbsub <- findSub i
    b <- lift $ satInScope i
    case (mbsub,b) of
      (Just sub,_) -> return sub
      (_,False) -> do
        cs <- lift $ lookupConstraints i
        let (subs,supers) = unzipConstrs cs
        subs' <- mapM substitute subs
        supers' <- mapM substitute supers
        ns@(JTSat i') <- lift $ newSatAtScope [i]
        lift $ mapM (addConstraint i') $ zipConstrs subs' supers'
        addSub (i,ns)
        return ns
      _ -> do
        cs <- lift $ lookupConstraints i
        let (subs,supers) = unzipConstrs cs
        subs' <- mapM substitute subs
        supers' <- mapM substitute supers
        constrs <- lift $ tc_constrs <$> get
        lift $ modify (\tcs -> tcs {tc_constrs = M.insert i (zipConstrs subs' supers') constrs})
        return (JTSat i)

substitute (JTFunc args ret) = do
  args' <- mapM substitute args
  ret' <- substitute ret
  return (JTFunc args' ret')

substitute (JTRec i) = do
    mbsub <- findSub i
    case mbsub of
      Just sub -> return sub
      _ -> do
        rl <- lift $ getRec i
        rl' <- mapM go rl
        r'@(JTRec i') <- lift $ newRec
        lift $ putRec i' rl'
        return r'
  where go (i',v) = do
          v' <- substitute v
          return (i',v')
substitute x = return x


{--------------------------------------------------------------------
  Constraint Resolution
--------------------------------------------------------------------}

resC :: Bool -> JType -> JMonad JType
resC inApp x = flip evalStateT [] $ do
  lift $ traceTy "resC" x
  c <- resC' inApp False x
  lift $ traceTy "resC Ans" c
  return c

resC' :: Bool -> Bool -> JType -> JMonadClone JType
resC' inApp contra x@(JTVar _) = do
  xt <- lift $ resolveType x
  case xt of
    (JTVar i) -> return (JTVar i)
    _ -> resC' inApp contra xt

resC' inApp contra (JTFunc args ret) = do
  args' <- mapM (resC' inApp True) args --mapM (resC' (not contra)) args
  ret'  <- resC' False False ret
  return (JTFunc args' ret')

resC' inApp contra r@(JTRec i) = do
  rl  <- lift $ getRec i
  rl' <- mapM go rl
  lift $ putRec i rl'
  return r
      where go (i',v) = do
              v' <- resC' inApp contra v
              return (i',v')

--in app we substitute, otherwise we keep as constrained
resC' inApp contra x@(JTSat i) = do
    mbsub <- findSub i
    b <- lift $ satInScope i
    case (mbsub,b) of
      (Just sub, _) -> return sub
      (_, False) -> do
        JTSat (i') <- substitute (JTSat i)
        cs <- lift (lookupConstraints i')
        cs' <- simplifyCs cs
        mapM traceC cs'
        ans <- resCs cs'
        --keep supertype, subtype constraints distinct
        ans' <- case (contra && not inApp, ans) of
          (True,(JTRec _)) -> trace "wao" $do
                      ns@(JTSat i'') <- lift $ newSat --newSatAtScope [i]
                      lift $ addConstraint i'' (Sub ans)
                      addSub (i,ns)
                      return ns
          (True,(JTFunc _ _ )) -> do
                      ns@(JTSat i'') <- lift $ newSat --newSatAtScope [i]
                      lift $ addConstraint i'' (Sub ans)
                      addSub (i,ns)
                      return ns
          _ -> return ans
        addSub (i,ans')
        lift $ traceTy "hai" ans'
        return ans'
      _ -> do
        cs <- lift (lookupConstraints i)
        cs' <- simplifyCs cs
        if any isAtom cs'
          then do
              ans <- resCs cs'
              addSub (i,ans)
              return ans
          else return x {- do
              ns@(JTSat i') <- lift $ newSat
              mapM (addConstraint i') cs'
              addSub (i,ns)
              return ns-}
    where
      resCs cs = do
        let (subs,supers) = unzipConstrs cs
        subs' <- mapM (resC' inApp contra) subs
        supers' <- mapM (resC' inApp contra) supers
        lubsubs   <- lift $ resolveType =<< luball subs'
        glbsupers <- lift $ resolveType =<< glball supers'
        case (length subs', length supers') of
          (0,0) -> return lubsubs
          (0,_) -> return glbsupers
          (_,0) -> return lubsubs
          _     -> lift $ glbsupers \/ lubsubs
      isAtom (Sub JTNum) = True
      isAtom (Super JTNum) = True
      isAtom (Sub JTStr) = True
      isAtom (Super JTStr) = True
      isAtom _ = False
      --isatom should go deeper into sats

resC' inApp contra (JTList mbmulti mbmono) = do
  mbmulti' <- maybe (return Nothing) (fmap Just . resRec) mbmulti
  mbmono'  <- maybe (return Nothing) (fmap Just . (resC' inApp contra)) mbmono
  return (JTList mbmulti' mbmono')
         where resRec x = do
                 (JTRec i) <- resC' inApp contra (JTRec x)
                 return i

resC' _ _ x = return x

getBot (JTRec _) = return $ JTRec (-1)
getBot (JTFunc _ ret) = do
  ret' <- getBot ret
  return $ JTFunc [] ret'
getBot x@(JTVar _) = do
  rx <- resolveType x
  case rx of
    (JTVar _) -> return $ BotOf rx
    _ -> getBot rx
getBot x@(JTList mbmulti mbmono) = do
  mbmono' <- maybe (return Nothing) (\x -> Just <$> getBot x) mbmono
  return $ JTList (fmap (const (negate 1)) mbmulti) mbmono --only bot of multi if multi, only bot of mono if mono!!!! TODO
getBot x = return x

simplifyCs :: [JConstr] -> JMonadClone [JConstr]
simplifyCs cs = concat <$> mapM simplifyC cs

simplifyC :: JConstr -> JMonadClone [JConstr]
simplifyC (Sub c) = case c of
                      JTSat i -> do
                             b <- lift $ satInScope i
                             if b
                               then return [Sub c]
                               else do
                                   cs <- lift $ lookupConstraints i
                                   (subs, supers) <- unzipConstrs <$> simplifyCs cs
                                   supers' <- lift $ map Sub <$> mapM getBot supers
                                   return $ map Sub subs ++ supers'
                      _ -> return [Sub c]

simplifyC (Super c) = case c of
                      JTSat i -> do
                             b <- lift $ satInScope i
                             if b
                               then return [Super c]
                               else do
                                   cs <- lift $ lookupConstraints i
                                   (subs, supers) <- unzipConstrs <$> simplifyCs cs
                                   subs' <- lift $ map Sub <$> mapM getBot subs
                                   return $ map Super supers ++ subs'
                      _ -> return [Super c]

{--------------------------------------------------------------------
  Least upper bound
--------------------------------------------------------------------}

--{} \/ {a} = {a}
(\/) :: JType -> JType -> JMonad JType
x \/ y = do
  xr <- resolveType x
  yr <- resolveType y
  if xr == yr
     then return xr
     else do
       traceTys "lub" xr yr
       ans <- lub xr yr
       traceTy "lub ans" ans
       return ans

lub :: JType -> JType -> JMonad JType

lub x@(JTSat i) y@(JTSat i') = do
  ns@(JTSat i'') <- newSatAtScope [i, i']
  addConstraint i'' (Sub y)
  addConstraint i'' (Sub x)
  return ns

--check if value satisfies constraint then proceed with constraint
lub (JTSat i) y = do
  cs <- lookupConstraints i
  mapM_ go cs
  ns@(JTSat i') <- newSatAtScope [i]
  mapM (addConstraint i') (Sub y : cs)
  return ns
      where go (Sub c) = y <: c
            go (Super c) = c <: y

lub x y@(JTSat _) = y \/ x

lub x@(JTVar _) y = do
  xt <- resolveType x
  case xt of
    (JTVar _) ->  do
            ns@(JTSat i'') <- newSat
            addConstraint i'' (Sub y)
--            addConstraint i'' (Sub x)
            x =.= ns -- ?
            return ns
    _ -> xt \/ y

lub x y@(JTVar _) = y \/ x

lub (JTFunc args ret) (JTFunc args' ret') = do
  args'' <- zipWithM (/\) args args'
  ret'' <- ret \/ ret'
  return $ JTFunc args'' ret''

lub (JTRec i) (JTRec i') = do
  xl <- getRec i
  yl <- getRec i'
  --find every value in x in y, and return lub of each
  let go ((l,v):lvs) = case find ((==l) . fst) yl of
                         Nothing -> go lvs
                         Just (_,v') -> do
                                    newv <- v \/ v'
                                    ((l,newv) :) <$> go lvs
      go _ = return []
  xlyl <- go xl

  --then add every value of x not in y and every value of y not in x
  let xld = deleteFirstsBy ((==) `on` fst) xl yl --xs not in ys
      yld = deleteFirstsBy ((==) `on` fst) yl xl --ys not in xs

  r'@(JTRec i'') <- newRec
  putRec i'' $ xlyl ++ xld ++ yld
  return r'

lub (JTList mbmulti mbmono) (JTList mbmulti' mbmono') = do
  mbmulti'' <- case (mbmulti, mbmulti') of
                 (Just multi, Just multi') -> do
                      (JTRec i) <- (JTRec multi) \/ (JTRec multi')
                      return $ Just i
                 _ -> return Nothing
  mbmono'' <- case (mbmono, mbmono') of
                (Just mono, Just mono') -> Just <$> mono \/ mono'
                _ -> return Nothing
  return $ JTList mbmulti'' mbmono''

lub x y
  | x == y = return x
  | otherwise = do
        tyErr2 "No Least Upper Bound Exists" x y

luball :: [JType] -> JMonad JType
luball (h:xs) = do
  foldM (\x y -> x \/ y) h xs
luball [] = newVar


{--------------------------------------------------------------------
 Greatest Lower bound
--------------------------------------------------------------------}

(/\) :: JType -> JType -> JMonad JType
x /\ y = do
  xr <- resolveType x
  yr <- resolveType y
  if xr == yr
     then return xr
     else do
       traceTys "glb" xr yr
       ans <- glb xr yr
       traceTy "glb ans" ans
       return ans

glb :: JType -> JType -> JMonad JType
glb (JTSat i) (JTSat i') = do
  ns <- newSatAtScope [i, i']
  addConstraint i (Super ns)
  addConstraint i' (Super ns)
  return ns

--glb of a free variable and anything is a subtype of the free var and the other thing
glb x@(JTVar _) y = do
  xt <- resolveType x
  case xt of
    (JTVar _) -> do
            ns@(JTSat i) <- newSatAtScope [-1] --always right?
--            addConstraint i (Super x)
            addConstraint i (Super y)
            x =.= ns -- ?
            return ns
    _ -> x /\ y

glb x y@(JTVar _) = y /\ x

glb x@(JTSat i) y = do
  ns@(JTSat i') <- newSatAtScope [i]
  addConstraint i' (Super y)
  addConstraint i' (Super x)
  return ns

glb x y@(JTSat _) = y /\ x

glb (JTFunc args ret) (JTFunc args' ret') = do
  args'' <- zipWithM (\/) args args'
  ret'' <- ret /\ ret'
  return $ JTFunc args'' ret''

glb (JTRec i) (JTRec i') = do
  xl <- getRec i
  yl <- getRec i'
    --find every value in x in y, and return glb of each
  let go ((l,v):lvs) = case find ((==l) . fst) yl of
                         Nothing -> go lvs
                         Just (_,v') -> do
                                    newv <- err2may (v /\ v')
                                    case newv of
                                      Just nv -> ((l,nv) :) <$> go lvs
                                      Nothing -> go lvs
      go _ = return []
  r'@(JTRec i'') <- newRec
  putRec i'' =<< go xl
  return r'
           where err2may v = fmap Just v `orElse` return Nothing

glb (JTList mbmulti mbmono) (JTList mbmulti' mbmono') = do
  mbmulti'' <- case (mbmulti, mbmulti') of
                 (Just multi, Just multi') -> do
                      (JTRec i) <- (JTRec multi) /\ (JTRec multi')
                      return $ Just i
                 _ -> return Nothing
  mbmono'' <- case (mbmono, mbmono') of
                (Just mono, Just mono') -> Just <$> mono /\ mono'
                _ -> return Nothing
  return $ JTList mbmulti'' mbmono''


glb x y
  | x == y = return x
  | otherwise = tyErr2 "No Greatest Lower Bound Exists" x y

glball :: [JType] -> JMonad JType
glball (h:xs) = do
  foldM (\x y -> x /\ y) h xs
glball [] = newVar

{--------------------------------------------------------------------
  Typecheck
--------------------------------------------------------------------}

class JTypeCheck a where
    typecheck :: a -> JMonad JType

instance JTypeCheck JStat where
    typecheck (DeclStat i) = addNewVar i >> return JTStat
    typecheck (ReturnStat e) = typecheck e
    typecheck (BlockStat xs) = typecheck xs
    typecheck (AssignStat x y) = do
                            xt <- typecheckLhs x
                            yt <- typecheck y
                            yt <: xt
                            return JTStat

    typecheck (IfStat e s s') = do
      (<=.= JTBool) =<< typecheck e
      if (s' == BlockStat [])
        then inConditional $ typecheck s
        else inConditional $ do
          --can we allow assignments that happen in both, or is this way too hard?
          st <- typecheck s
          st' <- typecheck s'
          chkNoNull [st,st']
          st /\ st'
    typecheck (WhileStat e s) = do
      (<=.= JTBool) =<< typecheck e
      inConditional $ typecheck s

    --for in statements iterate over names
    typecheck (ForInStat False i e s) = withLocalScope' [i] $ do
      (JTStr =.=) =<< lookupEnvErr i
      et <- resolveType =<< typecheck e
      case et of
          --list case
          JTRec _ -> return ()
          _ -> tyErr1 "Attempt to use 'for in' construct with improper type" et
      inConditional $ typecheck s

    --for each in statements iterate over property values
    typecheck (ForInStat True ident e s) = withLocalScope' [ident] $ do
      et <- resolveType =<< typecheck e
      case et of
        --list case
        JTRec i -> do
                --el <- map snd . init <$> rec2list et
                el <- map snd <$> getRec i
                case el of
                  [] -> return ()
                  es -> do
                       e' <- glball es
                       (e' =.=) =<< lookupEnvErr ident
        _ -> tyErr1 "Attempt to use 'for each in' construct with improper type" et
      inConditional $ typecheck s
    typecheck (ApplStat e args) = typecheck (ApplExpr e args) >> return JTStat
    typecheck (PostStat s e) = typecheck (PostExpr s e) >> return JTStat
    typecheck BreakStat = return JTStat
    --Switch
    --Unsat $ Anti -- anti can take signature!?

---add special cases in selectors for lists, etc!

typecheckLhs :: JExpr -> JMonad JType
typecheckLhs (SelExpr e1 ident@(StrI s)) = do
  e1t <- typecheck e1
  case e1t of
    JTRec i -> do
             newt <- recLookup ident e1t
             canextend <- tc_canextend <$> get
             case newt of
               Just t -> return t
               Nothing -> if canextend
                           then do
                             v <- newVar
                             rs <- getRec i
                             putRec i $ (ident,v):rs
                             return v
                           else tyErr1 "Attempt to extend record in conditional code" e1t
    JTSat i -> do
             ns <- newSatAtScope [i]
             nr@(JTRec i') <- newRec
             putRec i' [(ident,ns)]
             addConstraint i (Sub nr)
             return ns
    _ -> tyErr1 ("No property " ++ s ++ " in type") e1t

typecheckLhs x = typecheck x


instance JTypeCheck JExpr where
    typecheck (ValExpr v) = typecheck v
    typecheck (SelExpr e1 ident@(StrI s)) = do
                            e1t <- typecheck e1
                            newt <- recLookup ident e1t
                            case (newt, e1t) of
                              (Just t, _) -> return t
                              (Nothing, JTSat i) -> do
                                   ns <- newSatAtScope [i]
                                   nr@(JTRec i') <- newRec
                                   putRec i' [(ident,ns)]
                                   addConstraint i (Sub nr)
                                   return ns
                              (Nothing, _) -> tyErr1 ("No property " ++ s ++ " in type") e1t

    --NewExpr -- this is really a special appl
    --Unsat & Anti
    typecheck (InfixExpr s e1 e2)
        | s `elem` ["-","/","*"] = setFixed JTNum
        | s == "+" = setFixed JTNum `orElse` setFixed JTStr --TODO: Intersection types
        | s `elem` [">","<","==","/="] = setFixed JTNum >> return JTBool
        | s `elem` ["||","&&"] = setFixed JTBool
        | otherwise = throwError $ "Unhandled operator: " ++ s
      where setFixed t = do
              (<=.=) t =<< typecheck e1
              (<=.=) t =<< typecheck e2
              return t

    --check that e is either a selexpr or a var or an idxexpr
    typecheck (PostExpr _ e) = case e of
                                 (SelExpr _ _) -> go
                                 (ValExpr (JVar _)) -> go
                                 (IdxExpr _ _) -> go
                                 _ -> tyErr1 "Value not compatible with postfix assignment" =<< typecheck e
        where go = ((<=.= JTNum) =<< typecheck e) >> return JTNum

    typecheck (IfExpr e e1 e2) = do
                            (<=.= JTBool) =<< typecheck e
                            e1t <- typecheck e1
                            e2t <- typecheck e2
                            e1t /\ e2t

    typecheck (ApplExpr e args) = do
                            et <- resolveType =<< typecheck e
                            argst <- mapM (resolveType <=< typecheck) args
                            appFun et argst
    typecheck (IdxExpr e1 e2) = do
                            e1t <- resolveType =<< typecheck e1
                            e2t <- resolveType =<< typecheck e2
                            case e1t of
                              (JTList _ (Just t)) -> return t
                              (JTList (Just r) _)  -> case e2 of
                                        (ValExpr (JStr i)) -> do
                                          newt <- recLookup (StrI i) (JTRec r)
                                          case newt of
                                            Just t -> return t
                                            Nothing -> tyErr1 ("No property " ++ i ++ " in type") e1t
                                        (ValExpr (JInt i)) -> do
                                          newt <- recLookup (StrI $ show i) (JTRec r)
                                          case newt of
                                            Just t -> return t
                                            Nothing -> tyErr1 ("No property " ++ show i ++ " in type") e1t
                                        _ -> tyErr1 "Cannot index into hash/tuple with runtime expression" e1t
                              (JTList _ _) -> tyErr1 "List/Hash with no inhabited types" e1t
                              (JTSat i) -> do
                                      ns <- newSatAtScope [i]
                                      mbrec <- case e2 of
                                         (ValExpr (JStr i)) -> do
                                            nr@(JTRec i') <- newRec
                                            putRec i' [(StrI i,ns)]
                                            return $ Just i'
                                         (ValExpr (JInt i)) -> do
                                            nr@(JTRec i') <- newRec
                                            putRec i' [(StrI $ show i,ns)]
                                            return $ Just i'
                                         _ -> return Nothing
                                      addConstraint i (Sub $ JTList mbrec (Just ns))
                                      return ns
                              _ -> tyErr1 "Attempting to index into something of type" e1t

appFun :: JType -> [JType] -> JMonad JType
appFun(JTFunc args ret) appArgs = do
    when (length args > length appArgs) $ tyErr2l "Mismatched argument lengths" args appArgs
    appArgs' <- cloneMany appArgs
    (JTFunc args' ret') <- clone (JTFunc args ret)
    zipWithM (<:) appArgs' args'
    (JTFunc args'' ret'') <- withLocalScope [] $ resC True $ JTFunc args' ret'
--    zipWithM (=.=) args'' appArgs'
    return ret''
--    withLocalScope [] $ resC True ret''

appFun (JTSat i) args' = do
  s  <- newSatAtScope [i]
  mapM (bumpScope i) args'
  addConstraint i (Sub $ JTFunc args' s)
  return s

appFun x _ = tyErr1 "Attempting to apply as a function something of type"  x

instance JTypeCheck JVal where
    typecheck (JVar i) = case i of
                           StrI "true" -> return JTBool
                           StrI "false" -> return JTBool
                           StrI "null"  -> newVar
                           StrI _ -> resolveType =<< lookupEnvErr i
    typecheck (JInt _) = return JTNum
    typecheck (JDouble _) = return JTNum
    typecheck (JStr _) = return JTStr
    typecheck (JFunc args stat) =
                           withLocalScope args ( do
                             argst <- mapM (typecheck . JVar) args
                             rett <- typecheck stat
                             resC False $ JTFunc argst rett)
    typecheck (JHash m) = do
            let (is, es) = unzip $ M.toList m
            ets <- mapM typecheck es
            let initialrec
                    | null is = []
                    | otherwise =  zip (map StrI is) ets
            r@(JTRec i) <- newRec
            putRec i initialrec
            return r
    typecheck (JList es) = do
            (JTRec i) <- typecheck $ JHash $ M.fromList (zip (map show [1..]) es)
            es' <- mapM typecheck es
            e'' <- (Just <$> glball es') `orElse` return Nothing
            return $ JTList (Just i) e''
    --List

instance JTypeCheck [JStat] where
    typecheck [] = return JTStat
    typecheck stats = do
      ts <- filter (/=JTStat) <$> (mapM resolveType =<< mapM typecheckAnnotated stats)
      case ts of
        [] -> return JTStat
        _ -> chkNoNull ts >> glball ts

typecheckAnnotated :: (JMacro a, JsToDoc a, JTypeCheck a) => a -> JMonad JType
typecheckAnnotated stat = typecheck stat `catchError` \ e -> throwError $ e ++ "\nIn statement:\n" ++ renderStyle (style {mode = OneLineMode}) (renderJs stat)