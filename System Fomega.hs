type Symb = String 

infixl 4 :@:
infixr 3 :->

data Expr = Idx Int          -- переменная как индекс Де Брауна
          | Ast              -- константа, базовый атом для кайндов
          | Box              -- константа высшего уровня
          | Expr :@: Expr    -- аппликация терма к терму или типа к типу
          | Lmb Decl Expr    -- абстракция терма или типа 
          | Expr :-> Expr    -- стрелочный тип или кайнд
    deriving (Read,Show,Ord)

instance Eq Expr where
  Idx n1      == Idx n2      = n1 == n2
  Ast         == Ast         = True
  Box         == Box         = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3   == Lmb d2 u4   = d1 == d2 && u3 == u4
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  _           == _           = False

data Decl = EDecl Symb Expr --  объявление биндера с типом/кайндом, Symb - справочное имя переменной
    deriving (Read,Show,Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
-------------------------
-- вывод типов F omega --
-------------------------

-- служебные функции (старт) --
fromDecl :: Decl -> Expr
fromDecl (EDecl _ t) = t

isNf :: Expr -> Bool
isNf (Lmb (EDecl _ expr) term) = isNf expr && isNf term
isNf t = isNanf t

isNanf :: Expr -> Bool
isNanf Ast = True
isNanf Box = True
isNanf (Idx _) = True
isNanf (a :-> b) = isNf a && isNf b
isNanf (a :@: b) = isNanf a && isNf b
isNanf _         = False

isNa :: Expr -> Bool
isNa (Idx _) = True
isNa (_ :-> _) = True
isNa (_ :@: _) = True
isNa  _        = False
-- служебные функции (конец) --

validEnv :: Env -> Bool
validEnv [] = True -- пустой контекст корректен: \varempty |-
validEnv ((EDecl n t):es) = maybe False (const True) (infer es t) && validEnv es -- Г |- A:s && Г |-


shift :: Int -> Expr -> Expr
shift = go 0
  where
   go th ic Ast = Ast -- Ast не трогаем
   go th ic Box = Box -- Box не трогаем
   go th ic (Idx i) = if (i > th) then Idx (i + ic) else (Idx i)
   go th ic (e1 :@: e2) = go th ic e1 :@: go th ic e2
   go th ic (Lmb (EDecl n ed) el) = Lmb (EDecl n (go th ic ed)) (go (th+1) ic el) -- А может быть и не +1? может внутреннее выражение связывает БОЛЬШЕ свободных переменных из выражения el???
   go th ic (e1 :-> e2) = go th ic e1 :-> go th ic e2

subst :: Int -> Expr -> Expr -> Expr
subst j s Ast = Ast -- Ast не трогаем
subst j s Box = Box -- Box не трогаем
subst j s (Idx i) = if (i == j) then s else (Idx i) -- самая важная часть
subst j s (e1 :@: e2) = subst j s e1 :@: subst j s e2 -- нестареющая классика
subst j s (Lmb (EDecl n ed) el) = Lmb (EDecl n (subst j s ed)) (subst (j+1) (shift 1 s) el) -- и получилось то же самое правило -- буду снова на него смотреть как на новые ворота, ничего не меняется же...
subst j s (e1 :-> e2) = subst j s e1 :-> subst j s e2 -- я даже не знаю, есть ли тут другие альтернативы, как и в :@:

infer :: Env -> Expr -> Maybe Expr
-- T-axiom: * : #
infer env Ast = Just Box -- звёздочка это квадратик
-- T-var
infer env t@(Idx id) | validEnv env && id < length env = case fromDecl (env !! id) of
   Ast     -> Just Ast -- тип обыкновенный
   Box     -> Just Box -- сорт
   _       -> Nothing -- но как же типизировать сами термы?
-- T-arrow -- проверяем, что выводится одинаковый сорт, и назначаем его
infer env (a :-> b) = do
  kinda <- nf <$> infer env a
  kindb <- nf <$> infer env b
  kinda <- Just kindb
  return kinda
-- T-App
infer env (m :@: n) = do
  c <- nf <$> infer env m
  a <- nf <$> infer env n
  let anf = nf a
  anf :-> res <- Just (nf c)
  return res
-- T-Abs, возможно, самое важное правило
infer env (Lmb e@(EDecl x a) m) = do
  let nfe = (EDecl x (nf a))
  b <- nf <$> infer (nfe:env) m
  kind <- nf <$> infer (nfe:env) (a :-> b) -- монада упадёт, если a и b не одного кайнда
  return (a :-> b)

infer0 :: Expr -> Maybe Expr
infer0 = infer []

oneStep :: Expr -> Maybe Expr
oneStep (Idx _) = Nothing
oneStep Ast = Nothing
oneStep Box = Nothing
oneStep (a :@: b) | Just res <- oneStep a = Just (res :@: b)
oneStep (a :-> b) | Just res <- oneStep a = Just (res :-> b)
oneStep (a :@: b) | Just res <- oneStep b = Just (a :@: res)
oneStep (a :-> b) | Just res <- oneStep b = Just (a :-> res)
oneStep (Lmb (EDecl x a) m) | Just r <- oneStep a = Just $ Lmb (EDecl x r) m
                            | Just r <- oneStep m = Just $ Lmb (EDecl x a) r
oneStep ((Lmb _ m) :@: n) = Just $ shift (-1) $ subst 0 (shift 1 n) m
oneStep _                 = Nothing

-- нормальная форма (возможна расходимость)
nf = nfDB oneStep
 where
  nfDB :: (Expr -> Maybe Expr) -> Expr -> Expr 
  nfDB f t = maybe t (nfDB f) (f t)