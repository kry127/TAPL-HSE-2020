type Symb = String
infixl 4 :@: 
infixr 3 :->
infixl 5 :*

data Type = Boo
          | Type :-> Type
          | Type :* Type
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PPair Pat Pat
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Pair Term Term
          | Fst Term
          | Snd Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Pair u w  == Pair u1 w1   =  u == u1 && w == w1
  Fst z     == Fst z1       =  z == z1
  Snd z     == Snd z1       =  z == z1
  _         == _            =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)

pairCount :: Pat -> Int
pairCount (PPair p1 p2) = pairCount p1 + pairCount p2
pairCount (PVar _) = 1

shift :: Int -> Term -> Term
shift val term = go 0 val term
  where
    go thres inc t@(Idx x) | x < thres = t
                           | otherwise = Idx (x + inc)
    go thres inc (t1 :@: t2) = go thres inc t1 :@: go thres inc t2
    go thres inc (Lmb name type' t) = Lmb name type' $ go (thres + 1) inc t
    go thres inc (If t1 t2 t3) = If (go thres inc t1) (go thres inc t2) (go thres inc t3)
    go thres inc (Let p trm t) = Let p (go thres inc trm) (go (thres+(pairCount p)) inc t)
    go thres inc (Pair t1 t2) = Pair (go thres inc t1) (go thres inc t2)
    go thres inc (Fst t) = Fst (go thres inc t)
    go thres inc (Snd t) = Snd (go thres inc t)
    go thres inc t = t -- Tru, Fls

substDB :: Int -> Term -> Term -> Term
substDB j s t@(Idx x) | x == j    = s
                      | otherwise = t
substDB j s (t1 :@: t2) = substDB j s t1 :@: substDB j s t2
substDB j s (Lmb name type' t) = Lmb name type' $ substDB (j + 1) (shift 1 s) t
substDB j s (If t1 t2 t3) = If (substDB j s t1) (substDB j s t2) (substDB j s t3)
substDB j s (Let p t1 t2) = let off = (pairCount p) in Let p (substDB j s t1) (substDB (j + off) (shift off s) t2)
substDB j s (Pair t1 t2) = Pair (substDB j s t1) (substDB j s t2)
substDB j s (Fst t) = Fst (substDB j s t)
substDB j s (Snd t) = Snd (substDB j s t)
substDB j s t = t -- Tru, Fls

isValue :: Term -> Bool
isValue Tru = True
isValue Fls = True
isValue (Lmb _ _ _) = True
isValue (Pair a b) = isValue a && isValue b
isValue _   = False

match :: Pat -> Term -> Maybe [(Symb,Term)]
match (PVar name) t | isValue t = Just[(name, t)]
match (PPair p1 p2) (Pair t1 t2) = (++) <$> match p1 t1 <*> match p2 t2
match _             _            = Nothing

betaRuleDB :: Term -> Term
betaRuleDB (Lmb _ _ t :@: s) = shift (-1) $ substDB 0 (shift 1 s) t

sequentialBetaRule :: [(Symb, Term)] -> Term -> Term
sequentialBetaRule ((_,s):hs) t = sequentialBetaRule hs (shift (-1) $ substDB 0 (shift 1 s) t)
sequentialBetaRule _          t = t


oneStep :: Term -> Maybe Term
oneStep (If Tru t1 t2) = Just t1
oneStep (If Fls t1 t2) = Just t2
oneStep (If t t1 t2) = fmap (\t -> If t t1 t2) (oneStep t)
oneStep (Let pat trm t) | isValue trm, Just ls <- match pat trm = Just $ sequentialBetaRule (reverse ls) t
oneStep (Let pat trm t) | Just r <- oneStep trm = Just $ Let pat r t
oneStep (Fst t@(Pair t1 t2)) | isValue t1 && isValue t2 = Just t1
                             | otherwise                = Fst <$> oneStep t
oneStep (Snd t@(Pair t1 t2)) | isValue t1 && isValue t2 = Just t2
                             | otherwise                = Snd <$> oneStep t
oneStep (Pair t1 t2) | Just n1 <- oneStep t1 = Just $ Pair n1 t2
oneStep (Pair t1 t2) | isValue t1, Just n2 <- oneStep t2 = Just $ Pair t1 n2
oneStep t@(t1@(Lmb _ _ _) :@: t2) | isValue t2 = Just $ betaRuleDB t
                                  | otherwise  = (t1 :@:) <$> (oneStep t2)
oneStep (t1 :@: t2) | Just n1 <- oneStep t1 = Just $ n1 :@: t2
oneStep _ = Nothing -- whnf -- no lambda or val reduction


nfDB :: (Term -> Maybe Term) -> Term -> Term 
nfDB f t = case f t of
                Just t' -> nfDB f t'
                Nothing -> t

whnf = nfDB oneStep

inferPat :: Pat -> Type -> Maybe [(Symb, Type)]
inferPat (PVar name) t = Just $ [(name, t)]
inferPat (PPair p1 p2) (t1 :* t2) | Just e1 <- inferPat p1 t1
                                  , Just e2 <- inferPat p2 t2
                                  = Just $ e2 ++ e1
inferPat _             _          = Nothing

checkPat :: Pat -> Type -> Maybe Env
checkPat p t = Env <$> inferPat p t

infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

infer :: Env -> Term -> Maybe Type
infer env Tru = Just Boo
infer env Fls = Just Boo
infer env (If cond a b) | Just Boo <- infer env cond
                        , t1 <- infer env a
                        , t2 <- infer env b
                        = if t1 == t2 then t1 else Nothing
infer (Env env) (Idx id) = Just (snd $ env !! id)
infer (Env env) (Lmb name typt t) = fmap (\typs -> typt :-> typs) $ infer (Env$(name, typt):env) t
infer env (t1 :@: t2) | Just typt <- infer env t2
                      , Just (typt' :-> typs) <- infer env t1
                      = if typt == typt' then Just typs else Nothing
infer e@(Env env) (Let pat pt t) = do
                     ptt <- infer e pt
                     env' <- inferPat pat ptt
                     infer (Env $ env' ++ env) t
infer e@(Env env) (Pair a b) | Just t1 <- infer e a
                             , Just t2 <- infer e b
                             =  Just (t1 :* t2)
infer env (Fst t) | Just (t1 :* t2) <- infer env t = Just t1
infer env (Snd t) | Just (t1 :* t2) <- infer env t = Just t2
infer _   _ = Nothing