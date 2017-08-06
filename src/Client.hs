module Client (infer) where
import           Control.Monad
import           Control.Monad.Gen
import           Control.Monad.Trans
import qualified Data.Map      as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set      as S
import           Unification

typeOf :: M.Map Id Term
       -> M.Map Id Term
       -> Term
       -> UnifyM (Term, S.Set Constraint)
typeOf mcxt cxt t = case t of
  LocalVar i -> mzero
  FreeVar i -> maybe mzero (\x -> return (x, S.empty)) $ M.lookup i cxt
  MetaVar i -> maybe mzero (\x -> return (x, S.empty)) $ M.lookup i mcxt
  Uni -> return (Uni, S.empty)
  Ap l r -> do
    (tpl, cl) <- typeOf mcxt cxt l
    (tpr, cr) <- typeOf mcxt cxt r
    case tpl of
      Pi from to -> return (subst r 0 to, cl <> cr <> S.singleton (from, tpr))
      _ -> do
        (m1, m2) <- (,) <$> lift gen <*> lift gen
        return ( MetaVar m2 `Ap` r
               , cl <> cr <>
                 S.fromList [ (tpl, Pi (MetaVar m1) (MetaVar m2 `Ap` LocalVar 0))
                            , (tpr, MetaVar m1) ])
  Lam b -> do
    (v, m) <- (,) <$> lift gen <*> lift gen
    (to, cs) <-
      typeOf (M.insert m Uni mcxt) (M.insert v (MetaVar m) cxt)
      (subst (FreeVar v) 0 b)
    return ( Pi (MetaVar m) (substFV (LocalVar 0) v (raise 1 to))
           , cs <> S.singleton (MetaVar m, MetaVar m))
  Pi from to -> do
    v <- lift gen
    (fromTp, fromCs) <- typeOf mcxt cxt from
    (toTp, toCs) <- typeOf mcxt (M.insert v from cxt) (subst (FreeVar v) 0 from)
    return (Uni, fromCs <> toCs <> S.fromList [(Uni, fromTp), (Uni, toTp)])

infer :: Term -> Maybe (Term, S.Set Constraint)
infer t = listToMaybe . runUnifyM $ go
  where go = do
          (tp, cs) <- typeOf M.empty M.empty t
          (subst, flexflex) <- unify M.empty cs
          return (manySubst subst tp, flexflex)
