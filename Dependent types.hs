type Symb = String

infixl 4 :@:
infixr 3 >-> -- теперь просто функция

data Expr = Idx Int
          | Ast
          | Box
          | Expr :@: Expr
          | Lmb Decl Expr
          | Pi Decl Expr    -- расширенный функциональный тип
    deriving (Read,Show,Eq,Ord)

data Decl = EDecl Symb Expr
    deriving (Read,Show,Ord)

instance Eq Decl where
  EDecl _ t1 == EDecl _ t2 = t1 == t2

type Env = [Decl]

lE, pE :: Symb -> Expr -> Expr -> Expr
lE v = Lmb . EDecl v
pE v = Pi  . EDecl v

(>->) :: Expr -> Expr -> Expr
a >-> b = pE "_" a (shift 1 b)
----------------------

-- служебные функции (начало) --
fromDecl :: Decl -> Expr
fromDecl (EDecl _ t) = t

isKind :: Expr -> Bool
isKind Ast = True
isKind Box = True
isKind _   = False
-- служебные функции (конец)  --

-- imported from "System Fomega"
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
   go th ic (Lmb (EDecl n ed) el) = Lmb (EDecl n (go th ic ed)) (go (th+1) ic el)
   go th ic (Pi  (EDecl n ed) el) = Pi  (EDecl n (go th ic ed)) (go (th+1) ic el) -- чем-то отличается от строчки выше?

subst :: Int -> Expr -> Expr -> Expr
subst j s Ast = Ast -- Ast не трогаем
subst j s Box = Box -- Box не трогаем
subst j s (Idx i) = if (i == j) then s else (Idx i)
subst j s (e1 :@: e2) = subst j s e1 :@: subst j s e2
subst j s (Lmb (EDecl n ed) el) = Lmb (EDecl n (subst j s ed)) (subst (j+1) (shift 1 s) el)
subst j s (Pi  (EDecl n ed) el) = Pi  (EDecl n (subst j s ed)) (subst (j+1) (shift 1 s) el)

infer :: Env -> Expr -> Maybe Expr
infer env t | validEnv env = inferValid env t
            | otherwise    = Nothing
 where
  -- T-axiom: * : #
  inferValid env Ast = Just Box -- звёздочка это квадратик
  inferValid env Box = Nothing -- квадратик -- это вещь в себе
  -- T-var
  inferValid env t@(Idx id) | id < length env = Just $ shift (id + 1) (fromDecl $ env !! id)
  -- T-Pi
  inferValid env (Pi  e@(EDecl x a) b) = do
    Ast <- inferValid env a -- чекаем, что аргумент является кайндом *
    kind <- infer (e:env) b
    True <- Just $ isKind kind -- проверяем, что в b пришёл сорт
    return kind -- возвращаем резуьтат
  -- T-App (некоторый гибрид двух alternative из "System Fomega" вышел)
  inferValid env (m :@: n) = do
    (Pi  e@(EDecl x a) b) <- nf <$> inferValid env m
    a' <- inferValid env n
    True <- Just (nf a == nf a')
    return (shift (-1) $ subst 0 (shift 1 n) b)
  -- T-Abs
  inferValid env (Lmb e@(EDecl x a) m) = do
    Ast <- inferValid env a -- чекаем, что аргумент является кайндом *
    b <- infer (e:env) m
    --False <- Just $ isKind b -- проверяем, что это НЕ сорт (надо ли?)
    return (Pi (EDecl x a) b)
  inferValid _   _    = Nothing

infer0 :: Expr -> Maybe Expr
infer0 = infer []

oneStep :: Expr -> Maybe Expr
oneStep (Idx _) = Nothing
oneStep Ast = Nothing
oneStep Box = Nothing
-- ENO - App1
oneStep (a :@: b) | Just res <- oneStep a = Just (res :@: b)
-- ENO - App2
oneStep (a :@: b) | Just res <- oneStep b = Just (a :@: res)
-- ENO -- All0 (был в "System Fomega")
-- oneStep (ForAll n knd e) | Just r <- oneStep e = Just $ ForAll n knd r
-- ENO - Abs0 + Abs
oneStep (Lmb (EDecl x a) m) | Just r <- oneStep a = Just $ Lmb (EDecl x r) m
                            | Just r <- oneStep m = Just $ Lmb (EDecl x a) r
-- ENO - Pi0 (был ENO - Arr1 в "System Fomega")
oneStep (Pi  (EDecl x a) m) | Just res <- oneStep a = Just (Pi  (EDecl x res) m)
-- ENO - Pi  (был ENO - Arr2 в "System Fomega")
oneStep (Pi  (EDecl x a) m) | Just res <- oneStep m = Just (Pi  (EDecl x a) res)
-- ENO - AppAbs
oneStep ((Lmb _ m) :@: n) = Just $ shift (-1) $ subst 0 (shift 1 n) m
oneStep ((Pi  _ m) :@: n) = Just $ shift (-1) $ subst 0 (shift 1 n) m
oneStep _                 = Nothing
--oneStep term = error $ show term
-- ENO - AppForAll (был в "System Fomega"), сейчас не нужен
-- oneStep ((ForAll _ knd expr) :@: typ) | Just knd == infer0 typ = Just $ shift (-1) $ subst 0 (shift 1 typ) expr
-- oneStep _                 = Nothing

-- нормальная форма (возможна расходимость)
nf = nfDB oneStep
 where
  nfDB :: (Expr -> Maybe Expr) -> Expr -> Expr
  nfDB f t = maybe t (nfDB f) (f t)