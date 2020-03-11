import Data.Monoid
import Data.Semigroup

type Symb = String
infixl 4 :@: 
infixr 3 :->

data Type = Boo
          | Type :-> Type
          | TRcd [(Symb,Type)] 
    deriving (Read,Show,Eq)

data Pat = PVar Symb
         | PRcd [(Symb,Pat)] 
    deriving (Read,Show,Eq)

data Term = Fls
          | Tru
          | If Term Term Term
          | Idx Int
          | Term :@: Term
          | Lmb Symb Type Term
          | Let Pat Term Term
          | Rcd [(Symb,Term)]
          | Prj Symb Term
          deriving (Read,Show)

instance Eq Term where
  Fls       == Fls          =  True
  Tru       == Tru          =  True
  If b u w  == If b1 u1 w1  =  b == b1 && u == u1 && w == w1
  Idx m     == Idx m1       =  m == m1
  (u:@:w)   == (u1:@:w1)    =  u == u1 && w == w1
  Lmb _ t u == Lmb _ t1 u1  =  t == t1 && u == u1
  Let p u w == Let p1 u1 w1 =  p == p1 && u == u1 && w == w1
  Rcd xs    == Rcd xs1      =  xs == xs1
  Prj l u   == Prj l1 u1    =  l == l1 && u == u1
  _         == _            =  False

newtype Env = Env [(Symb,Type)]
  deriving (Read,Show,Eq)
------------------------------------

-- ============================ --
-- == операционная семантика == --
-- ============================ --

countPatVars :: Pat -> Int
countPatVars (PVar _) = 1
countPatVars (PRcd pdict) = foldr ((+) . countPatVars . snd) 0 pdict

-- добавляет к индексам СВОБОДНЫХ термов величину val
-- лямбды и паттерн-матчинг увеличивают уровень на один
shift :: Int -> Term -> Term
shift val term = go 0 val term
  where
    go thres inc t@(Idx x) | x < thres = t
                           | otherwise = Idx (x + inc)
    go thres inc (t1 :@: t2) = go thres inc t1 :@: go thres inc t2
    go thres inc (Lmb name type' t) = Lmb name type' $ go (thres + 1) inc t
    go thres inc (If t1 t2 t3) = If (go thres inc t1) (go thres inc t2) (go thres inc t3)
    go thres inc (Let pat rcd t) = Let pat rcd $ go (thres + (countPatVars pat)) inc t
    go thres inc (Rcd dict) = Rcd $ (go thres inc <$>) <$> dict
    go thres inc (Prj s t) = Prj s (go thres inc t)
    go thres inc t = t -- Tru, Fls

-- подстановка терма с индексом i в терминах де Брюйна
substDB :: Int -> Term -> Term -> Term
substDB j s t@(Idx x) | x == j    = s
                      | otherwise = t
substDB j s (t1 :@: t2) = substDB j s t1 :@: substDB j s t2
substDB j s (Lmb name type' t) = Lmb name type' $ substDB (j + 1) (shift 1 s) t
substDB j s (If t1 t2 t3) = If (substDB j s t1) (substDB j s t2) (substDB j s t3)
substDB j s (Let pat rcd t) = let
                  l = countPatVars pat
                in Let pat (substDB j s rcd) (substDB (j + l) (shift l s) t)
substDB j s (Rcd dict) = Rcd $ (fmap (substDB j s)) <$> dict
substDB j s (Prj s' t) = Prj s' (substDB j s t)
substDB j s t = t -- Tru, Fls

-- Проверяем, является ли терм значением
isValue :: Term -> Bool
isValue Fls = True
isValue Tru = True
isValue (Lmb _ _ _) = True
--isValue (Let _ t _) = isValue t-- or False? or True?
isValue (Rcd dict) = foldr (&&) True $ fmap (\(_, t) -> isValue t) dict
isValue _   = False

-- паттерн матчинг кортежей
match :: Pat -> Term -> Maybe [(Symb,Term)]
match (PVar name) t = Just [(name, t)]
match (PRcd patDict) (Rcd termDict) = foldMap id <$> sequenceA [getMatch name pat | (name, pat) <- patDict]
  where
    -- наверное, имеет смысл переписать этот кошмар в монаде списков...
    getMatch name pat = let ls = [smth | (name', term) <- termDict, name == name', let res = match pat term, res /= Nothing, let Just smth = res] in if ls == [] then Nothing else Just (foldMap id ls)
match _             _  = Nothing

-- правило одношаговой бета-редукции для частных случаев: лямбды и let
betaRuleDB :: Term -> Term
betaRuleDB (Lmb _ _ t :@: s) = shift (-1) $ substDB 0 (shift 1 s) t
betaRuleDB (Let pat term t) = case match pat term of
            Just matchlist -> foldr (\(v,t') t -> shift (-1) $ substDB 0 (shift 1 t') t) t matchlist
            _              -> t

-- одношаговая бета-редукция в общем случае
oneStep :: Term -> Maybe Term
oneStep (If Tru t1 t2) = Just t1
oneStep (If Fls t1 t2) = Just t2
oneStep (If t t1 t2) = fmap (\t -> If t t1 t2) (oneStep t)
oneStep t@(Let s t1 t2) | isValue t1 = Just $ betaRuleDB t
                        | otherwise  = (\x -> Let s x t2) <$> (oneStep t1)
oneStep (Prj name rcd@(Rcd map)) | isValue rcd = lookup name map
                                 | otherwise   = case oneStep rcd of
                                     Just x -> Just $ Prj name x
                                     _      -> lookup name map
oneStep (Prj name inner@(Prj _ _)) = (Prj name) <$> oneStep inner
oneStep (Rcd []) = Nothing
oneStep (Rcd [(name,t)]) = (\t -> Rcd [(name, t)]) <$> oneStep t
oneStep (Rcd ((name,t):tail)) = case oneStep t of
                            Just t' -> Just (Rcd $ (name,t'):tail)
                            Nothing -> case oneStep (Rcd tail) of
                                  Just (Rcd tail') -> Just (Rcd ((name,t):tail'))
                                  _                -> Nothing

oneStep t@(t1@(Lmb _ _ _) :@: t2) | isValue t2 = Just $ betaRuleDB t
                                  | otherwise  = (t1 :@:) <$> (oneStep t2)
oneStep (t1 :@: t2) = case oneStep t1 of
                            Just t' -> Just $ t' :@: t2
                            Nothing -> Nothing
oneStep _ = Nothing -- whnf -- no lambda or val reduction


-- аппликативная стратегия редукции (если редуцируется)
nfDB :: (Term -> Maybe Term) -> Term -> Term 
nfDB f t = maybe t (nfDB f) (f t)

-- аппликативная нормальная форма (возможна расходимость)
whnf = nfDB oneStep

-- ================= --
-- == вывод типов == --
-- ================= --

-- служебные функции
instance Semigroup Env where
  (Env e1) <> (Env e2) = Env (e1 ++ e2)

instance Monoid Env where
  mempty = Env []
-- конец служебных функций


checkPat :: Pat -> Type -> Maybe Env
checkPat (PVar name) t = Env <$> pure [(name, t)] -- Boo и :-> точно, а вот TRcd ??
checkPat (PRcd patDict) (TRcd typeDict) = foldr (flip (<>)) (Env []) <$> sequenceA [getMatch name pat | (name, pat) <- patDict]
  where
    -- наверное, имеет смысл переписать этот кошмар в монаде списков...
    getMatch name pat = let ls = [smth | (name', typ) <- typeDict, name == name', let res = checkPat pat typ, res /= Nothing, let Just smth = res] in if ls == [] then Nothing else Just (foldMap id ls)
checkPat _             _  = Nothing

{-
checkPat (PRcd ((name, pat):patDict)) (TRcd ((name', typ):termDict)) | name /= name' = Nothing
checkPat (PRcd ((_, pat):patDict)) (TRcd ((_, typ):termDict)) = (flip (<>)) <$> checkPat pat typ <*> checkPat (PRcd patDict) (TRcd termDict)
checkPat (PRcd []) (TRcd []) = Just (Env [])
checkPat (PRcd _) (TRcd _) = Nothing
checkPat _             _  = Nothing
-}


infer0 :: Term -> Maybe Type
infer0 = infer $ Env []

infer :: Env -> Term -> Maybe Type
infer env Fls = Just Boo
infer env Tru = Just Boo
infer env (If cond a b) = case infer env cond of
            Just Boo -> let
                         t1 = infer env a
                         t2 = infer env b
                        in if t1 == t2 then t1 else Nothing
            _        -> Nothing
infer (Env env) (Idx id) = snd <$> Just (env !! id)
infer env (t1 :@: t2) = case infer env t2 of
                          Just typt -> case infer env t1 of
                              Just (typt' :-> typs) -> if typt == typt' then Just typs else Nothing
                              _                     -> Nothing
                          _         -> Nothing
infer (Env env) (Lmb name typt t) = fmap (\typs -> typt :-> typs) $ infer (Env$(name, typt):env) t
infer env (Let pat tpat t) = maybe Nothing (\env' -> infer (env' <> env) t) (maybe Nothing (checkPat pat) (infer env tpat))
infer env (Rcd dict) = TRcd <$> sequenceA ((\(p, t) -> fmap ((,) p) (infer env t)) <$> dict)
infer env (Prj name t) = case infer env t of
                            Just (TRcd db) -> lookup name db
                            _              -> Nothing

--- тесты
pat' = PRcd [("ly",PVar "py"), ("lx",PVar "px")]
rec' = Rcd  [("lx",Tru),      ("ly",Fls)      ]
m1 = match pat' rec'
os1 = oneStep $ Let pat' rec' $ If Tru (Idx 1) (Idx 0)
whnf1 = whnf $ Let pat' rec' $ If Tru (Idx 1) (Idx 0)

oneDB = Idx 1
twoDB = Idx 2
biRec0 = Rcd [("subRcd",Rcd [("y",Fls),("m",oneDB)]),("n",twoDB),("x",Tru)]
whnfBiRec0 = whnf (Prj "m" (Prj "subRcd" biRec0))
test2 = whnfBiRec0 == oneDB

-- infer type
typectx = (Env [("x", Boo), ("y", (Boo :-> Boo) :-> Boo), ("n", (Boo :-> Boo))])
complexPat = PRcd [("n",PRcd [("n2",PVar "py2"),("n1",PVar "py1")]),("m",PRcd [("m2", PVar "px2"),("m1",PVar "px1")])]
complexRcd = Rcd  [("m",Rcd [("m1", Tru), ("m2", Fls)]), ("n",Rcd [("n1", Fls), ("n2", Tru)]) ]
complexMatch = match complexPat complexRcd
complexExpr = Let complexPat complexRcd $ If Tru (If Tru (Idx 1) (Idx 0)) (Idx 3)


emptyPat = PRcd []
emptyRcd = Rcd []
emptyMatch = match emptyPat emptyRcd
emptyExpr = Let emptyPat emptyRcd $ If Tru (If Tru (Idx 1) (Idx 0)) (Idx 3)

-- notStrictType check
complexPatNS = PRcd [("n",PRcd [("n2",PVar "py2"),("n1",PVar "py1")]),("m",PRcd [("m2", PVar "px2"),("m1",PVar "px1")])]
complexRcdNS = Rcd  [("m",Rcd [("m1", Tru), ("m2", Fls)]), ("n",Rcd [("n1", Fls)]) ]
complexMatchNS = match complexPatNS complexRcdNS -- should be Nothing

-- types step
cK = Lmb "x" Boo (Lmb "y" Boo (Idx 1))
rec = Rcd  [("lB",Tru),     ("lK",cK)      ]
pat = PRcd [("lB",PVar "x"),("lK",PVar "y")]