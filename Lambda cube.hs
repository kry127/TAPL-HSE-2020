import Control.Monad

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

type Rule = (Expr,Expr)

-- лямбда-куб
rulesS,rulesF,rulesO,rulesP,rulesFO,rulesPF,rulesPO,rulesPFO :: [Rule]
rulesS   = [(Ast,Ast)]
rulesF   = (Box,Ast) : rulesS
rulesO   = (Box,Box) : rulesS
rulesP   = (Ast,Box) : rulesS
rulesFO  = (Box,Ast) : rulesO
rulesPF  = (Ast,Box) : rulesF
rulesPO  = (Ast,Box) : rulesO
rulesPFO = (Ast,Box) : rulesFO

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

lambdaCubeSpecs :: [Rule] -> Expr -> Expr -> Bool
lambdaCubeSpecs ((Ast, Ast):_) Ast Ast = True
lambdaCubeSpecs ((Ast, Box):_) Ast Box = True
lambdaCubeSpecs ((Box, Ast):_) Box Ast = True
lambdaCubeSpecs ((Box, Box):_) Box Box = True
lambdaCubeSpecs []             _   _   = False
lambdaCubeSpecs (_:specs)      s1  s2  = lambdaCubeSpecs specs s1 s2

-- служебные функции (конец)  --

-- full check
validEnv :: [Rule] -> Env -> Bool
validEnv spec [] = True -- пустой контекст корректен: \varempty |-
validEnv spec (h:es) = validEnvHead spec h es && validEnv spec es -- Г |- A:s && Г |-

-- only head check
validEnvHead :: [Rule] -> Decl -> Env -> Bool
validEnvHead spec (EDecl x a) es = maybe False isKind (inferValid spec es a)

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


infer :: [Rule] -> Env -> Expr -> Maybe Expr
infer spec env t | validEnv spec env = inferValid spec env t
                 | otherwise         = Nothing

inferValid :: [Rule] -> Env -> Expr -> Maybe Expr
-- T-axiom: * : #
inferValid spec env Ast = Just Box -- звёздочка это квадратик
inferValid spec env Box = Nothing -- квадратик -- это вещь в себе
-- T-var
inferValid spec env t@(Idx id) | id < length env = Just $ shift (id + 1) (fromDecl $ env !! id)
-- T-Pi
inferValid spec env (Pi  e@(EDecl x a) b) = do
  s1 <- inferValid spec env a
  -- s2 <- infer spec (e:env) b -- было прежде
  True <- Just $ validEnvHead spec e env -- проверяем корректность только e отн. контекста!
  s2 <- inferValid spec (e:env) b
  True <- Just $ lambdaCubeSpecs spec s1 s2 -- проверяем, что это допустимая зависимость в лямбда-кубе
  return s2
-- T-App
inferValid spec env (m :@: n) = do
  (Pi  e@(EDecl x a) b) <- nf <$> inferValid spec env m
  a' <- inferValid spec env n
  True <- Just (nf a == nf a')
  return (shift (-1) $ subst 0 (shift 1 n) b)
-- T-Abs
inferValid spec env (Lmb e@(EDecl x a) m) = do
  True <- isKind <$> inferValid spec env a -- синяя проверка
  --b <- infer spec (e:env) m -- было прежде
  True <- Just $ validEnvHead spec e env -- проверяем корректность только e отн. контекста!
  b <- inferValid spec (e:env) m
  let result = Pi (EDecl x a) b
  True <- isKind <$> inferValid spec env result -- обязательно проверяем, что вывелся тип некоторого сорта (Ast или Box)
  return result
inferValid spec env _    = Nothing

infer0 :: [Rule] -> Expr -> Maybe Expr
infer0 = flip infer []

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

-- нормальная форма (возможна расходимость)
nf :: Expr -> Expr
nf = nfDB oneStep
 where
  nfDB :: (Expr -> Maybe Expr) -> Expr -> Expr
  nfDB f t = maybe t (nfDB f) (f t)

-- n шагов редукции
nSteps n t = foldM (flip ($)) t (replicate n oneStep)

-- тесты
res1 = infer0 rulesPFO vecT == Just (Ast >-> natT >-> Ast)
res2 = infer0 rulesPFO vecNatT == Just (natT >-> Ast)
res3 = null $ infer0 rulesPF vecT
res4 = infer0 rulesPF vecNatT == Just (natT >-> Ast)
res5 = infer0 rulesPFO nil /= Just nilT
res6 = (nf <$> infer0 rulesPF nil) == Just nilT
res7 = (nf <$> infer0 rulesPFO cons) == Just consT
res8 = null $ infer0 rulesPF cons
testDefault = [res1, res2, res3, res4, res5, res6, res7, res8]


-- Следующие типы и термы могут оказаться полезными для тестирования
tArr  = Idx 0 >-> Idx 0
tBool = Idx 0 >-> Idx 0 >-> Idx 0
tNat  = tArr >-> tArr
tK    = Idx 1 >-> Idx 0 >-> Idx 1
tKast = Idx 1 >-> Idx 0 >-> Idx 0
-- Комбинатор $I$ (Idx 0 в cIFopen ссылается в никуда, нужен контекст)
cIFopen = lE "x" (Idx 0) $ Idx 0
cIF = lE "a" Ast $ lE "x" (Idx 0) $ Idx 0
-- Комбинаторы $K$ и $K_\ast$
tKF = pE "a" Ast $ pE  "b" Ast tK
cKF = lE "a" Ast $ lE "b" Ast $ lE "x" (Idx 1) $ lE "y" (Idx 1) $ Idx 1
tKastF = pE "a" Ast $ pE "b" Ast tKast
cKastF = lE "a" Ast $ lE "b" Ast $ lE "x" (Idx 1) $ lE "y" (Idx 1) $ Idx 0
-- Комбинатор $C$
tFlip = (Idx 2 >-> Idx 1 >-> Idx 0) >-> Idx 1 >-> Idx 2 >-> Idx 0
tFlipF = pE "a" Ast $ pE "b" Ast $ pE "c" Ast $ tFlip
cFlipF = lE "a" Ast $ lE "b" Ast $ lE "c" Ast $ lE "f" (Idx 2 >-> Idx 1 >-> Idx 0) $ lE "y" (Idx 2) $ lE "x" (Idx 4) $ Idx 2 :@: Idx 0 :@: Idx 1
-- Кодирование булевых значений в System F
boolT = pE "a" Ast $ Idx 0 >-> Idx 0 >-> Idx 0
fls = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 0
tru = lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 1
ifThenElse = lE "a" Ast $ lE "v" boolT $ lE "x" (Idx 1) $ lE "y" (Idx 2) $ Idx 2 :@: Idx 3 :@: Idx 1 :@: Idx 0
notF = lE "v" boolT $ lE "a" Ast $ lE "t" (Idx 0) $ lE "f" (Idx 1) $ Idx 3 :@: Idx 2 :@: Idx 0 :@: Idx 1
-- Кодирование самоприменения в System F (примеры из лекции)
botF = pE "a" Ast (Idx 0)
topF = pE "a" Ast tArr
sa0 = lE "z" botF $ lE "b" Ast $ Idx 1 :@: (Idx 0 >-> Idx 0) :@: (Idx 1 :@: Idx 0)
sa1 = lE "z" topF $ lE "b" Ast $ Idx 1 :@: (Idx 0 >-> Idx 0) :@: (Idx 1 :@: Idx 0)
sa2 = lE "z" topF $ Idx 0 :@: topF :@: Idx 0
-- Кодирование натуральных чисел в System F
natT = pE "a" Ast $ (Idx 0 >-> Idx 0) >-> Idx 0 >-> Idx 0
natAbs body = lE "a" Ast $ lE "s" (Idx 0 >-> Idx 0) $ lE "z" (Idx 1) body
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
isZeroF = lE "m" natT $ Idx 0 :@: boolT :@: lE "x" boolT fls :@: tru
succF = lE "m" natT $ lE "b" Ast $ lE "s" (Idx 0 >-> Idx 0) $ lE "z" (Idx 1) $ Idx 1 :@: (Idx 3 :@: Idx 2 :@: Idx 1 :@: Idx 0)
-- кодирование вектора в Calculus of Construction
vecT = lE "sigma" Ast
     $ lE "m" natT
     $ pE "phi" (natT >-> Ast)
     $ (Idx 0 :@: zero)
        >-> (pE "n" natT $ Idx 3 >-> Idx 1 :@: Idx 0 >-> Idx 1 :@: (succF :@: Idx 0))
        >-> Idx 0 :@: Idx 1
nil = lE "sigma" Ast
    $ lE "phi" (natT >-> Ast)
    $ lE "z" (Idx 0 :@: zero)
    $ lE "c" (pE "n" natT $ Idx 3 >-> Idx 2 :@: Idx 0 >-> Idx 2 :@: (succF :@: Idx 0))
    $ (Idx 1)
nilT = nf
     $ pE "sigma" Ast
     $ vecT :@: Idx 0 :@: zero
cons = lE "sigma" Ast
     $ lE "n" natT
     $ lE "e" (Idx 1)
     $ lE "v" (vecT :@: Idx 2 :@: Idx 1)
     $ lE "phi" (natT >-> Ast)
     $ lE "z" (Idx 0 :@: zero)
     $ lE "c" (pE "n" natT $ Idx 6 >-> Idx 2 :@: Idx 0 >-> Idx 2 :@: (succF :@: Idx 0))
     $ Idx 0 :@: Idx 5 :@: Idx 4 :@: (Idx 3 :@: Idx 2 :@: Idx 1 :@: Idx 0)
consT = nf
      $ pE "sigma" Ast
      $ pE "n" natT
      $ Idx 1
        >-> vecT :@: Idx 1 :@: Idx 0
        >-> vecT :@: Idx 1 :@: (succF :@: Idx 0)
vecNatT = nf $ vecT :@: natT
vec12 = cons
    :@: natT -- тип
    :@: one  -- индекс
    :@: one  -- элемент
    :@: (cons
           :@: natT -- тип
           :@: zero -- индекс
           :@: two  -- элемент
           :@: (nil :@: natT))