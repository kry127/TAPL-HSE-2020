import Control.Applicative

type Symb = String

infixl 4 :@:
infixr 3 :->

data Expr = Idx Int               -- переменная как индекс Де Брауна
          | Ast                   -- константа, базовый атом для кайндов
          | Box                   -- константа высшего уровня
          | Expr :@: Expr         -- аппликация терма к терму или типа к типу
          | Lmb Decl Expr         -- абстракция терма или типа
          | Expr :-> Expr         -- стрелочный тип или кайнд
          | ForAll Symb Expr Expr -- полиморфный тип, второй аргумент - кайнд типовой переменной
    deriving (Read,Show,Ord)

instance Eq Expr where
  Idx n1      == Idx n2      = n1 == n2
  Ast         == Ast         = True
  Box         == Box         = True
  (u1 :@: u3) == (u2 :@: u4) = u1 == u2 && u3 == u4
  Lmb d1 u3   == Lmb d2 u4   = d1 == d2 && u3 == u4
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ s1 t3 == ForAll _ s2 t4 = s1 == s2 && t3 == t4
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

isKind :: Expr -> Bool
isKind Ast = True
isKind Box = True
isKind _   = False
-- служебные функции (конец) --

validEnv :: Env -> Bool
validEnv [] = True -- пустой контекст корректен: \varempty |-
validEnv ((EDecl x a):es) = maybe False isKind (infer es a) && validEnv es -- Г |- A:s && Г |-


shift :: Int -> Expr -> Expr
shift = go 0
  where
   go th ic Ast = Ast -- Ast не трогаем
   go th ic Box = Box -- Box не трогаем
   go th ic (Idx i) = if (i >= th) then Idx (i + ic) else (Idx i)
   go th ic (e1 :@: e2) = go th ic e1 :@: go th ic e2
   go th ic (Lmb (EDecl n ed) el) = Lmb (EDecl n (go th ic ed)) (go (th+1) ic el) -- А может быть и не +1? может внутреннее выражение связывает БОЛЬШЕ свободных переменных из выражения el???
   go th ic (e1 :-> e2) = go th ic e1 :-> go th ic e2
   go th ic (ForAll n e1 e2) = ForAll n e1 (go (th+1) ic e2) -- e1 подразумевается isKind или стрелки из них, его менять не надо

subst :: Int -> Expr -> Expr -> Expr
subst j s Ast = Ast -- Ast не трогаем
subst j s Box = Box -- Box не трогаем
subst j s (Idx i) = if (i == j) then s else (Idx i) -- самая важная часть
subst j s (e1 :@: e2) = subst j s e1 :@: subst j s e2 -- нестареющая классика
subst j s (Lmb (EDecl n ed) el) = Lmb (EDecl n (subst j s ed)) (subst (j+1) (shift 1 s) el) -- и получилось то же самое правило -- буду снова на него смотреть как на новые ворота, ничего не меняется же...
subst j s (e1 :-> e2) = subst j s e1 :-> subst j s e2 -- я даже не знаю, есть ли тут другие альтернативы, как и в :@:
subst j s (ForAll n e1 e2) = ForAll n e1 (subst (j+1) (shift 1 s) e2)

infer :: Env -> Expr -> Maybe Expr
infer env t | validEnv env = inferValid env t
            | otherwise    = Nothing
 where
  -- T-axiom: * : #
  inferValid env Ast = Just Box -- звёздочка это квадратик
  inferValid env Box = Nothing -- квадратик -- это вещь в себе
  -- T-var
  inferValid env t@(Idx id) | id < length env = Just $ shift (id + 1) (fromDecl $ env !! id)
  -- T-arrow -- проверяем, что выводится одинаковый сорт, и назначаем его
  inferValid env (a :-> b) = do
    kinda <- inferValid env a
    kindb <- inferValid env b
    True <- Just (kinda == kindb && isKind kinda)
    return kinda
  -- T-ForAll
  inferValid env (ForAll x s b) = do
    Box <- inferValid env s
    Ast <- infer (EDecl x s :env) b
    return Ast
  -- T-App
  inferValid env (m :@: n) = do
    a :-> b <- nf <$> inferValid env m
    a' <- inferValid env n
    True <- Just (nf a == nf a')
    return b
    <|> do
  -- T-TApp
  --inferValid env (m :@: a) = do
    ForAll x s b <- nf <$> inferValid env m
    s' <- inferValid env n
    True <- Just (nf s == nf s')
    return (shift (-1) $subst 0 (shift 1 n) b)
  -- T-Abs, возможно, самое важное правило
  inferValid env (Lmb e@(EDecl x a) m) = do
    b <- infer (e:env) m
    kind <- infer (e:env) (shift 1 a :-> b) -- монада упадёт, если a и b не одного сорта
    True <- Just $ isKind kind -- проверяем, что это действительно сорта
    return (a :-> shift (-1) b)
    <|> do
  -- T-TAbs
  --inferValid env (Lmb e@(EDecl x s) m) = do
    b <- infer (e:env) m
    let tryToInferForAll = ForAll x a b
    Ast <- inferValid env tryToInferForAll -- если получилось получить обычный тип
    return tryToInferForAll -- возвращаем тип forall
  -- остальное
  inferValid env _ = Nothing

infer0 :: Expr -> Maybe Expr
infer0 = infer []

oneStep :: Expr -> Maybe Expr
oneStep (Idx _) = Nothing
oneStep Ast = Nothing
oneStep Box = Nothing
-- ENO - App1
oneStep (a :@: b) | Just res <- oneStep a = Just (res :@: b)
-- ENO - Arr 1
oneStep (a :-> b) | Just res <- oneStep a = Just (res :-> b)
-- ENO - App2
oneStep (a :@: b) | Just res <- oneStep b = Just (a :@: res)
-- ENO - Arr2
oneStep (a :-> b) | Just res <- oneStep b = Just (a :-> res)
-- ENO -- All0
oneStep (ForAll n knd e) | Just r <- oneStep e = Just $ ForAll n knd r
-- ENO - Abs0 + Abs
oneStep (Lmb (EDecl x a) m) | Just r <- oneStep a = Just $ Lmb (EDecl x r) m
                            | Just r <- oneStep m = Just $ Lmb (EDecl x a) r
-- ENO - AppAbs
oneStep ((Lmb _ m) :@: n) = Just $ shift (-1) $ subst 0 (shift 1 n) m
-- ENO - AppForAll
oneStep ((ForAll _ knd expr) :@: typ) | Just knd == infer0 typ = Just $ shift (-1) $ subst 0 (shift 1 typ) expr
oneStep _                 = Nothing

-- нормальная форма (возможна расходимость)
nf = nfDB oneStep
 where
  nfDB :: (Expr -> Maybe Expr) -> Expr -> Expr 
  nfDB f t = maybe t (nfDB f) (f t)

--------------------------------
-- конец вывода типов F omega --
--------------------------------


-- ================================================================= --
-- Следующие типы и термы могут оказаться полезными для тестирования --
-- ================================================================= --

-- Кодирование булевых значений в System F
boolT = ForAll "a" Ast $ Idx 0 :-> Idx 0 :-> Idx 0
fls = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 0
tru = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 1

ifThenElse = lE "a" Ast $ lE "v" boolT $ lE "x" (Idx 1) $ lE "y" (Idx 2) $ Idx 2 :@: Idx 3 :@: Idx 1 :@: Idx 0
notF = lE "v" boolT $ lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 3 :@: Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" Ast $ (Idx 0 :-> Idx 0) :-> Idx 0 :-> Idx 0
natAbs body = lE "a" Ast $ lE "s" (Idx 0 :-> Idx 0) $ lE "z" (Idx 1) body
zero  = natAbs $ Idx 0
one   = natAbs $ Idx 1 :@: Idx 0
two   = natAbs $ Idx 1 :@: (Idx 1 :@: Idx 0)
three = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))
four  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))
five  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))
six   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))
seven = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))
eight = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))
nine  = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0))))))))
ten   = natAbs $ Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: (Idx 1 :@: Idx 0)))))))))

-- Кодирование списков в System F omega
tListFo = lE "sigma" Ast $ ForAll "alpha" Ast $ (Idx 1 :-> Idx 0 :-> Idx 0) :-> Idx 0 :-> Idx 0

nilFo = lE "sigma" Ast
      $ lE "alpha" Ast
      $ lE "c" (Idx 1 :-> Idx 0 :-> Idx 0)
      $ lE "n" (Idx 1)
      $ (Idx 0)

consFo = lE "sigma" Ast
       $ lE "e" (Idx 0)
       $ lE "l" (tListFo :@: Idx 1)
       $ lE "alpha" Ast
       $ lE "c" (Idx 3 :-> Idx 0 :-> Idx 0)
       $ lE "n" (Idx 1)
       $ Idx 1 :@: Idx 4 :@: (Idx 3 :@: Idx 2 :@: Idx 1 :@: Idx 0)

-- тесты validEnv и infer
res1 = infer [EDecl "x" Ast] $ (Idx 0) :-> (Idx 0)
res2 = infer [EDecl "x" Box] $ (Idx 0) :-> (Idx 0)
test1 = res1 == Just Ast
test2 = res2 == Just Box