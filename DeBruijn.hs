import Data.Map

type Symb = String 
infixl 4 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)

infixl 4 :@:

data Term = Idx Int
          | Term :@: Term
          | Lmb Symb Term
          deriving (Read, Show)

type Context = [Symb]

-- перегруженное равенство, игнорирующее имя связываемой переменной
instance Eq Term where
  Idx m     == Idx n      =  m == n
  (t1:@:s1) == (t2:@:s2)  =  t1 == t2 && s1 == s2
  Lmb _ t1  == Lmb _ t2   =  t1 == t2
  _         == _          =  False

shift :: Int -> Term -> Term
shift val term = go 0 val term
  where
    go thres inc t@(Idx x) | x < thres = t
                           | otherwise = Idx (x + inc)
    go thres inc (t1 :@: t2) = go thres inc t1 :@: go thres inc t2
    go thres inc (Lmb name t) = Lmb name $ go (thres + 1) inc t

substDB :: Int -> Term -> Term -> Term
substDB j s t@(Idx x) | x == j    = s
                      | otherwise = t
substDB j s (t1 :@: t2) = substDB j s t1 :@: substDB j s t2
substDB j s (Lmb name t) = Lmb name $ substDB (j + 1) (shift 1 s) t


betaRuleDB :: Term -> Term
betaRuleDB (Lmb _ t :@: s) = shift (-1) $ substDB 0 (shift 1 s) t

oneStepDBN :: Term -> Maybe Term
oneStepDBN (Idx _) = Nothing
oneStepDBN t@(Lmb _ _ :@: _) = Just $ betaRuleDB t
oneStepDBN (t1 :@: t2) = case oneStepDBN t1 of
                            Just t -> Just $ t :@: t2
                            Nothing -> case oneStepDBN t2 of
                                Just t' -> Just $ t1 :@: t'
                                Nothing -> Nothing
oneStepDBN (Lmb name t) = case oneStepDBN t of
                            Just t' -> Just $ Lmb name t'
                            Nothing -> Nothing

oneStepDBA :: Term -> Maybe Term
oneStepDBA (Idx _) = Nothing
oneStepDBA t@(t1@(Lmb _ _) :@: t2) = case oneStepDBA t2 of
                            Just t' -> Just $ t1 :@: t'
                            Nothing -> Just $ betaRuleDB t
oneStepDBA (t1 :@: t2) = case oneStepDBA t2 of
                            Just t' -> Just $ t1 :@: t'
                            Nothing -> case oneStepDBA t1 of
                                Just t -> Just $ t :@: t2
                                Nothing -> Nothing
oneStepDBA (Lmb name t) = case oneStepDBA t of
                            Just t' -> Just $ Lmb name t'
                            Nothing -> Nothing


nfDB :: (Term -> Maybe Term) -> Term -> Term 
nfDB f t = case f t of
                Just t' -> nfDB f t'
                Nothing -> t

freeVars :: Expr -> Map Symb ()
freeVars (Var s) = fromList [(s, ())]
freeVars (e1 :@ e2) = freeVars e1 `union` freeVars e2
freeVars (Lam s e) = freeVars e \\ fromList [(s, ())]

enumerateDict :: Map Symb () -> Map Symb Int
enumerateDict dict = fromList $ zip (fmap fst (toList dict)) [0..]

e2t :: Expr -> (Context, Term)
e2t exp = let context = (enumerateDict $ freeVars exp) in (keys context, go context exp)
  where
    go dict (Var name) = case Data.Map.lookup name dict of
                                   Just id -> Idx id
                                   Nothing -> Idx 0
    go dict (e1 :@ e2) = go dict e1 :@: go dict e2
    go dict (Lam name e) = let
                  newdict = insert name 0 $ fmap succ dict
                in Lmb name $ go newdict e

addToContext :: Context -> Symb -> Context
addToContext ctx e | elem e ctx = addToContext ctx (e ++ "'")
                   | otherwise  = e : ctx

t2e :: Context -> Term -> Expr
t2e ctx (Idx x) = Var (ctx !! x)
t2e ctx (e1 :@: e2) = t2e ctx e1 :@ t2e ctx e2
t2e ctx (Lmb name t) = let newctx = addToContext ctx name in Lam (head newctx) $ t2e newctx t
