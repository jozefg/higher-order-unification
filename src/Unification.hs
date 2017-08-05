{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
module Unification where
import           Control.Monad
import           Control.Monad.Gen
import           Control.Monad.Logic
import           Control.Monad.Trans
import qualified Data.Map.Strict     as M
import           Data.Maybe
import           Data.Foldable
import           Data.Monoid
import qualified Data.Set            as S

type Id = Int
type Index = Int
data Term = FreeVar Id
          | LocalVar Index
          | MetaVar Id
          | Uni
          | Ap Term Term
          | Lam Term
          | Pi Term Term
          deriving (Eq, Show, Ord)

raise :: Int -> Term -> Term
raise = go 0
  where go lower i t = case t of
          FreeVar i -> FreeVar i
          LocalVar j -> if i > lower then LocalVar (i + j) else LocalVar j
          MetaVar i -> MetaVar i
          Uni -> Uni
          Ap l r -> go lower i l `Ap` go lower i r
          Lam body -> Lam (go (lower + 1) i body)
          Pi tp body -> Pi (go lower i tp) (go (lower + 1) i body)

subst :: Term -> Int -> Term -> Term
subst new i t = case t of
  FreeVar i -> FreeVar i
  LocalVar j -> case compare j i of
    LT -> LocalVar j
    EQ -> new
    GT -> LocalVar (j - 1)
  MetaVar i -> MetaVar i
  Uni -> Uni
  Ap l r -> subst new i l `Ap` subst new i r
  Lam body -> Lam (subst (raise 1 new) (i + 1) body)
  Pi tp body -> Pi (subst new i tp) (subst (raise 1 new) (i + 1) body)

substMV :: Term -> Id -> Term -> Term
substMV new i t = case t of
  FreeVar i -> FreeVar i
  LocalVar i -> LocalVar i
  MetaVar j -> if i == j then new else MetaVar j
  Uni -> Uni
  Ap l r -> substMV new i l `Ap` substMV new i r
  Lam body -> Lam (substMV (raise 1 new) i body)
  Pi tp body -> Pi (substMV new i tp) (substMV (raise 1 new) i body)

metavars :: Term -> S.Set Id
metavars t = case t of
  FreeVar i -> S.empty
  LocalVar i -> S.empty
  MetaVar j -> S.singleton j
  Uni -> S.empty
  Ap l r -> metavars l <> metavars r
  Lam body -> metavars body
  Pi tp body -> metavars tp <> metavars body

isClosed :: Term -> Bool
isClosed t = case t of
  FreeVar i -> False
  LocalVar i -> True
  MetaVar j -> True
  Uni -> True
  Ap l r -> isClosed l && isClosed r
  Lam body -> isClosed body
  Pi tp body -> isClosed tp && isClosed body

reduce :: Term -> Term
reduce t = case t of
  FreeVar i -> FreeVar i
  LocalVar j -> LocalVar j
  MetaVar i -> MetaVar i
  Uni -> Uni
  Ap l r -> case reduce l of
    Lam body -> reduce (subst r 0 body)
    l' -> Ap l' (reduce r)
  Lam body -> Lam (reduce body)
  Pi tp body -> Pi (reduce tp) (reduce body)

type FreshM = LogicT (Gen Id)

isStuck :: Term -> Bool
isStuck MetaVar {} = True
isStuck (Ap f _) = isStuck f
isStuck _ = False

peelApTelescope :: Term -> (Term, [Term])
peelApTelescope t = go t []
  where go (Ap f r) rest = go f (r : rest)
        go t rest = (t, rest)

applyApTelescope :: Term -> [Term] -> Term
applyApTelescope = foldl' Ap

applyLamTelescope :: Term -> [Term] -> Term
applyLamTelescope retTp [] = retTp
applyLamTelescope retTp (argTp : rest) =
  Lam . applyLamTelescope retTp $ map (raise 1) rest

type Constraint = (Term, Term)

simplify :: Constraint -> FreshM (S.Set Constraint)
simplify (t1, t2)
  | t1 == t2 = return S.empty
  | reduce t1 /= t1 = simplify (reduce t1, t2)
  | reduce t2 /= t2 = simplify (t1, reduce t2)
  | (FreeVar i, cxt) <- peelApTelescope t1,
    (FreeVar j, cxt') <- peelApTelescope t2 = do
      guard (i == j && length cxt == length cxt')
      fold <$> mapM simplify (zip cxt cxt')
  | Lam body1 <- t1,
    Lam body2 <- t2 = do
      v <- FreeVar <$> lift gen
      return $ S.singleton (subst v 0 body1, subst v 0 body2)
  | Pi tp1 body1 <- t1,
    Pi tp2 body2 <- t2 = do
      v <- FreeVar <$> lift gen
      return $ S.fromList
        [(subst v 0 body1, subst v 0 body2),
         (tp1, tp2)]
  | otherwise =
    if isStuck t1 || isStuck t2 then return $ S.singleton (t1, t2) else mzero

type Subst = M.Map Id Term

manySubst :: Subst -> Term -> Term
manySubst s t = M.foldrWithKey (\mv sol t -> substMV sol mv t) t s

(<+>) :: Subst -> Subst -> Subst
s1 <+> s2 | not (M.null (M.intersection s1 s2)) = error "Impossible"
s1 <+> s2 = M.union (manySubst s1 <$> s2) s1

tryFlexRigid :: Constraint -> [FreshM [Subst]]
tryFlexRigid (t1, t2)
  | (MetaVar i, cxt1) <- peelApTelescope t1,
    (stuckTerm, cxt2) <- peelApTelescope t2,
    not (i `S.member` metavars t2) = proj (length cxt1) i stuckTerm 0
  | (MetaVar i, cxt1) <- peelApTelescope t2,
    (stuckTerm, cxt2) <- peelApTelescope t1,
    not (i `S.member` metavars t1) = proj (length cxt1) i stuckTerm 0
  | otherwise = []
  where proj bvars mv f nargs =
          generateSubst bvars mv f nargs : proj bvars mv f (nargs + 1)
        generateSubst bvars mv f nargs = do
          let mkLam tm = foldr ($) tm (replicate bvars Lam)
          let saturateMV tm = foldl' Ap tm (map LocalVar [0..bvars - 1])
          let mkSubst = M.singleton mv
          args <- map saturateMV . map MetaVar <$> replicateM nargs (lift gen)
          return [mkSubst . mkLam $ applyApTelescope t args
                 | t <- map LocalVar [0..bvars - 1] ++
                        if isClosed f then [f] else []]

repeatedlySimplify :: S.Set Constraint -> FreshM (S.Set Constraint)
repeatedlySimplify cs = do
  cs' <- fold <$> traverse simplify (S.toList cs)
  if cs' == cs then return cs else repeatedlySimplify cs'

unify :: Subst -> S.Set Constraint -> FreshM (Subst, S.Set Constraint)
unify s cs = do
  let cs' = applySubst s cs
  cs'' <- repeatedlySimplify cs'
  let (flexflexes, flexrigids) = S.partition flexflex cs''
  if S.null flexrigids
    then return (s, flexflexes)
    else do
      let psubsts = tryFlexRigid (S.findMax flexrigids)
      trySubsts psubsts (flexrigids <> flexflexes)
  where applySubst s = S.map (\(t1, t2) -> (manySubst s t1, manySubst s t2))
        flexflex (t1, t2) = isStuck t1 && isStuck t2
        trySubsts [] cs = mzero
        trySubsts (mss : psubsts) cs = do
          ss <- mss
          let these = foldr mplus mzero [unify (newS <+> s) cs | newS <- ss]
          let those = trySubsts psubsts cs
          these `interleave` those

-- | Solve a constraint and return the remaining flex-flex constraints
-- and the substitution for it.
driver :: Constraint -> Maybe (Subst, S.Set Constraint)
driver = listToMaybe . runGenFrom 100 . observeAllT . unify M.empty . S.singleton
