import Data.Maybe

type Symb = String 

infixl 4 :@:, :@>
infixr 3 :->
infix 1 ||-

data Type = TIdx Int         -- типовой атом как индекс Де Брауна
          | Type :-> Type    -- стрелочный тип
          | ForAll Symb Type -- полиморфный тип, Symb - справочное имя связываемой переменной
          | Exists Symb Type -- экзистенциальный тип, Symb - справочное имя связываемой переменной
    deriving (Read,Show,Ord)

instance Eq Type where
  TIdx n1     == TIdx n2     = n1 == n2
  (t1 :-> t3) == (t2 :-> t4) = t1 == t2 && t3 == t4
  ForAll _ t1 == ForAll _ t2 = t1 == t2
  Exists _ t1 == Exists _ t2 = t1 == t2
  _           == _           = False

-- Объявление либо переменная, либо тип
data Decl = VDecl Symb Type --  объявление термовой переменной с ее типом, Symb - справочное имя этой переменной (большая лямбда)
          | TDecl Symb      --  объявление типовой переменной, Symb - справочное имя этой переменной (маленькая лямбда)
    deriving (Read,Show,Ord)

instance Eq Decl where
  VDecl _ t1 == VDecl _ t2 = t1 == t2
  TDecl _    == TDecl _    = True
  _          == _          = False

type Env = [Decl]

data Term = Idx Int
          | Term :@: Term
          | Term :@> Type
          | Lmb Decl Term
          | As (Type,Term) Type       -- упаковка типа-свидетеля и терма в экзистенциальный тип
          | Let (Symb,Symb) Term Term -- распаковка пакета, имена типа и терма в паре - справочные
    deriving (Read,Show,Eq,Ord)

lV :: Symb -> Type -> Term -> Term
lV v = Lmb . VDecl v

lT :: Symb -> Term -> Term
lT = Lmb . TDecl
------------------------------------

infixr 9 !!?
(!!?) :: [a] -> Int -> Maybe a
(!!?) [] _ = Nothing
(!!?) (t : _) 0 = Just t
(!!?) (_ : ts) n = (!!?) ts $ n - 1

-- проверка корректности контекста
validEnv :: Env -> Bool
validEnv [] = True -- пустой контекст корректный
validEnv ((TDecl name):ts) = validEnv ts
validEnv ((VDecl name typ):ts) = (ts ||- typ) && validEnv ts

isTDecl :: Decl -> Bool
isTDecl (TDecl _) = True
isTDecl _ = False

-- проверка корректности типа относительно контекста
(||-) :: Env -> Type -> Bool
env ||- (TIdx n) = fromMaybe False $ isTDecl <$> env !!? n
env ||- (t1 :-> t2) = (env ||- t1) && (env ||- t2)
env ||- (ForAll name typ) = ((TDecl name):env) ||- typ
env ||- (Exists name typ) = ((TDecl name):env) ||- typ

-- сдвиг индексов де Брауна у типовых переменных
shiftT :: Int -> Type -> Type
shiftT inc typ = shiftTwithTH 0 inc typ
  --where
shiftTwithTH th inc (TIdx id) | id >= th  = TIdx (id + inc)
                              | otherwise = TIdx id
shiftTwithTH th inc (s :-> t) = (shiftTwithTH th inc s) :-> (shiftTwithTH th inc t)
shiftTwithTH th inc (ForAll n t) = ForAll n $ shiftTwithTH (th + 1) inc t
shiftTwithTH th inc (Exists n t) = Exists n $ shiftTwithTH (th + 1) inc t
   
-- сдвиг индксов де Брауна у термов
shiftV :: Int -> Term -> Term
shiftV inc typ = shiftVwithTH 0 inc typ
  where
   shiftVwithTH th inc (Idx id) | id >= th  = Idx (id + inc)
                                | otherwise = Idx id
   shiftVwithTH th inc (t1 :@: t2) = shiftVwithTH th inc t1 :@: shiftVwithTH th inc t2
   shiftVwithTH th inc (t :@> typ) = shiftVwithTH th inc t :@> (shiftTwithTH th inc typ) -- должны ли мы шифтить тип?
   shiftVwithTH th inc (Lmb (VDecl n typ) term) = Lmb (VDecl n (shiftTwithTH th inc typ)) (shiftVwithTH (th+1) inc term) -- а тут?)
   shiftVwithTH th inc (Lmb decl term) = Lmb decl (shiftVwithTH (th+1) inc term)
   shiftVwithTH th inc (As (sigma, t) tau) = As (shiftTwithTH th inc sigma, shiftVwithTH th inc t) (shiftTwithTH th inc tau)
   shiftVwithTH th inc (Let (s1, s2) t1 t2) = Let (s1, s2) (shiftVwithTH th inc t1) (shiftVwithTH (th+2) inc t2)

-- подстановка sigma вместо tau вместо типовой переменной с номером j
-- Стоит учитывать, что лямбды должны повышать номер: j -> j + 1
substTT :: Int -> Type -> Type -> Type
substTT j sigma (TIdx id) | id == j   = sigma
                          | otherwise = (TIdx id)
substTT j sigma (s :-> t) = (substTT j sigma s) :-> (substTT j sigma t)
substTT j sigma (ForAll n t) = ForAll n (substTT (j + 1) (shiftT 1 sigma) t)
substTT j sigma (Exists n t) = Exists n (substTT (j + 1) (shiftT 1 sigma) t)

-- подстановка терма s в терм вместо индекса j
substVV :: Int -> Term -> Term -> Term
substVV j s (Idx id) | id == j   = s
                     | otherwise = (Idx id)
substVV j s (t1 :@: t2) = substVV j s t1 :@: substVV j s t2
substVV j s (t :@> typ) = substVV j s t :@> typ -- в тип ничего не подставляем! там термов нет
substVV j s (Lmb decl term) = Lmb decl (substVV (j + 1) (shiftV 1 s) term)
substVV j s (As (sigma, t) tau) = As (sigma, substVV j s t) tau -- в тип sigma и tau ничего не подставляем! там термов нет
substVV j s (Let (s1, s2) t1 t2) = Let (s1, s2) (substVV j s t1) (substVV (j + 2) (shiftV 2 s) t2)

-- подстановка типа tau вместо переменной типа с номером i в терме u
substTV :: Int -> Type -> Term -> Term
substTV i tau u@(Idx id) = u
substTV j tau u@(t1 :@: t2) = substTV j tau t1 :@: substTV j tau t2
substTV j tau u@(t :@> typ) = substTV j tau t :@> substTT j tau typ -- обратите внимание, что в тип мы подставляем с помощью substTT
substTV j s (Lmb (VDecl n typ) term) = Lmb (VDecl n (substTT j s typ)) (substTV (j + 1) (shiftT 1 s) term) -- аналогично, и здесь в типе подставляем с помощью substTT
substTV j s (Lmb decl term) = Lmb decl (substTV (j + 1) (shiftT 1 s) term)
substTV j s (As (sigma, t) tau) = As (substTT j s sigma, substTV j s t) (substTT j s tau) -- обратите внимание, что в тип sigma мы подставляем с помощью substTT
substTV j s (Let (s1, s2) t1 t2) = Let (s1, s2) (substTV j s t1) (substTV (j + 2) (shiftT 2 s) t2)


betaRuleV :: Term -> Term -> Term
betaRuleV (Lmb _ t) s = shiftV (-1) $ substVV 0 (shiftV 1 s) t

betaRuleT :: Term -> Type -> Term
betaRuleT (Lmb _ t) s = shiftV (-1) $ substTV 0 (shiftT 1 s) t

betaRulePack :: Term -> Maybe Term
betaRulePack (Let (a,x) (As (tau,nf) sigma) t) = Just $ shiftV (-1) $ substTV 0 (shiftT 1 tau) (shiftV (-1) $ substVV 0 (shiftV 1 nf) t)
_                                              = Nothing

-- алгоритм работал вместо O(n), где n -- число узлов в AST,
-- за O(n*2^h), где h -- высота дерева. Дело в том, что вместо
-- паттерн-матчинга в guard выражении использовалось повторное
-- вычисление выражение, чо приводило к экспоненциальному времени
-- работы алгоритма
oneStep :: Term -> Maybe Term
oneStep (t1 :@: t2) | Just res <- oneStep t1 = Just (res :@: t2)
oneStep (t1 :@> t2) | Just res <- oneStep t1 = Just (res :@> t2)
oneStep (Lmb decl t) = Lmb decl <$> oneStep t
oneStep t@(t1@(Lmb (VDecl _ _) _) :@: t2) = Just $ betaRuleV t1 t2
oneStep t@(t1@(Lmb (TDecl _)   _) :@> t2) = Just $ betaRuleT t1 t2 -- identical body to the upper line
oneStep (t1 :@: t2)  = (t1 :@:) <$> oneStep t2
oneStep (As (sigma,t) tau) | Just res <- oneStep t = Just $ As (sigma,res) tau
oneStep t@(Let (s1,s2) t1 t2) | Just res <- oneStep t1 = Just $ Let (s1, s2) res t2
                              | otherwise = betaRulePack t
oneStep _                       = Nothing -- whnf -- no lambda or val reduction

nfDB :: (Term -> Maybe Term) -> Term -> Term 
nfDB f t = maybe t (nfDB f) (f t)

-- нормальная форма (возможна расходимость)
nf = nfDB oneStep

-- функция выведения типа терма в заданном контексте
-- функция выведения типа терма в заданном контексте
infer :: Env -> Term -> Maybe Type
infer env (Idx id) | id >= length env = Nothing
                   | validEnv env = case env !! id of
                                     (VDecl n t) -> Just (shiftT (id + 1) t)
                                     otherwise   -> Nothing
                   | otherwise      = Nothing
infer env (t1 :@: t2) = case infer env t1 of
                           Just (s :-> t) -> maybe Nothing (\s' -> if s == s' then Just t else Nothing) (infer env t2)
                           _              -> Nothing
infer env (Lmb decl@(VDecl n sigma) ter) | env ||- sigma = (sigma :->) <$> shiftT (-1) <$> infer (decl:env) ter
                                         | otherwise     = Nothing
infer env (ter :@> typ) | env ||- typ = case infer env ter of
                           Just (ForAll n typ') -> Just $ shiftT (-1) (substTT 0 (shiftT 1 typ) typ')
                           _                    -> Nothing
                        | otherwise   = Nothing
infer env (Lmb decl@(TDecl n) t) = (ForAll n) <$> infer (decl:env) t
infer env (As (s,t) trm@(Exists x t')) | (infer env t) == Just (shiftT (-1) $ substTT 0 (shiftT 1 s) t') = Just trm
                                       | otherwise = Nothing
infer env (Let (alpha,x) t1 t2) = do
    Exists alpha sigm <- infer env t1 -- Exists a.sigma
    tau <- infer ((VDecl x sigm):(TDecl alpha):env) t2 -- tau
    let tau' = shiftT (-2) tau
    True <- Just (env ||- tau')
    return tau'

-- дополнительная функция для удобства
infer0 = infer []

-- ========================= --
-- конец реализации System F --
-- ========================= --

--- тесты для экзистенциальных типов
tstP = pF :@> natT :@> (natT :-> natT) :@: two :@: (plus :@: three)

tstPT = ForAll "a" $ (natT :-> (natT :-> natT) :-> TIdx 0) :-> TIdx 0

tstPTEx = Exists "b" $ ForAll "a" $ (TIdx 1 :-> (TIdx 1 :-> natT) :-> TIdx 0) :-> TIdx 0

packedP = (natT,tstP) `As` tstPTEx

test = Let ("gamma","p") packedP testBody where 
  testBody = snd_ :@: fst_
  fst_ = Idx 0 :@> TIdx 1            :@: (cKF    :@> TIdx 1 :@> (TIdx 1 :-> natT))
  snd_ = Idx 0 :@> (TIdx 1 :-> natT) :@: (cKastF :@> TIdx 1 :@> (TIdx 1 :-> natT))
  
test1 = Let ("gamma","p") packedP testBody where 
  testBody = snd_ :@: seven   -- тип seven - это natT, в snd_ ожидается "gamma"
  snd_ = Idx 0 :@> (TIdx 1 :-> natT) :@: (cKastF :@> TIdx 1 :@> (TIdx 1 :-> natT))

test2 = Let ("gamma","p") packedP testBody where 
  testBody = fst_             -- тип "gamma" локален и не может быть доступен извне 
  fst_ = Idx 0 :@> TIdx 1            :@: (cKF    :@> TIdx 1 :@> (TIdx 1 :-> natT))

-- введём термы на числах Чёрча

isZero, suc, plus, mult, power :: Term
isZero = lV "n" natT $ Idx 0 :@> boolT :@: (cKF :@> boolT :@> boolT :@: fls) :@: tru
suc    = lV "n" natT $ natAbs $ (Idx 3 :@> TIdx 2 :@: Idx 1 :@: (Idx 1 :@: Idx 0))
plus   = lV "m" natT $ lV "n" natT $ natAbs $ (Idx 4 :@> TIdx 2 :@: Idx 1 :@: (Idx 3 :@> TIdx 2 :@: Idx 1 :@: Idx 0))
mult   = lV "m" natT $ lV "n" natT $ natAbs $ (Idx 4 :@> TIdx 2 :@: (Idx 3 :@> TIdx 2 :@: Idx 1) :@: Idx 0)
power  = lV "m" natT $ lV "n" natT $ natAbs $ (Idx 3 :@> (TIdx 2 :-> TIdx 2)) :@: (Idx 4 :@> TIdx 2) :@: Idx 1 :@: Idx 0

-- реализуем оператор примитивной рекурсии на числах Чёрча, но нам нужны пары
pF = lT "sigma" $ lT "tau" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ 
       lT "a" $ lV "f" (TIdx 4 :-> TIdx 3 :-> TIdx 0) $ Idx 0 :@: Idx 3 :@: Idx 2
pFT = ForAll "sigma" $ ForAll "tau" $ TIdx 1 :-> TIdx 0 :-> pT
pT = ForAll "a" $ (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 0
fstP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 2 :@: (cKF    :@> TIdx 2 :@> TIdx 1)
sndP = lT "sigma" $ lT "tau" $ lV "p" pT $ Idx 0 :@> TIdx 1 :@: (cKastF :@> TIdx 2 :@> TIdx 1)

-- примитивная рекурсия
--recNat i f ini | i == 0    = ini
--               | otherwise = f (recNat (i-1) ini) (i-1)


-- помним, что tru и fls могут использоваться как ite:
-- if A then B:T else C:T  <===> A :@> T :@: B :@: C

-- сначала определяем recNatPair, который возвращает пару из результата натуральной
-- рекурсии, и последнего вычисленного индекса
recNatPair = lT "iniT" $ lV "i" natT $ lV "f" (TIdx 1 :-> natT :-> TIdx 1) $ lV "ini" (TIdx 2) $
            Idx 2 :@> internalPairType -- тип пары "Pair a natT"
              :@: nextPair
              :@: (pF :@> (TIdx 3) :@> natT :@: Idx 0 :@: zero)
  where
   internalPairType = (ForAll "b" $ (TIdx 4 :-> natT :-> TIdx 0) :-> TIdx 0)
   fst' = fstP :@> (TIdx 4) :@> natT
   snd' = sndP :@> (TIdx 4) :@> natT
   nextPair = (lV "k" (internalPairType) $ pF :@> (TIdx 4) :@> natT
                   :@: (Idx 2 :@: (fst' :@: Idx 0) :@: (snd' :@: Idx 0)) -- первый элемент пары -- f k succ
                   :@: (suc :@: (snd' :@: Idx 0))) -- Второй элемент пары -- suc succ

-- теперь легко определить и саму натуральную рекурсию
recNat = lT "iniT" $ lV "i" natT $ lV "f" (TIdx 1 :-> natT :-> TIdx 1) $ lV "ini" (TIdx 2) $
     fstP :@> (TIdx 3) :@> natT :@: (recNatPair :@> (TIdx 3) :@: Idx 2 :@: Idx 1 :@: Idx 0)

-- в целях оптимизации, это лучше сделать НЕПОСРЕДСТВЕННО
rec = lT "iniT" $ lV "i" natT $ lV "f" (TIdx 1 :-> natT :-> TIdx 1) $ lV "ini" (TIdx 2) $
            fstP :@> (TIdx 3) :@> natT :@:
            (Idx 2 :@> internalPairType -- тип пары "Pair a natT"
              :@: nextPair
              :@: (pF :@> (TIdx 3) :@> natT :@: Idx 0 :@: zero))
  where
   internalPairType = (ForAll "b" $ (TIdx 4 :-> natT :-> TIdx 0) :-> TIdx 0)
   fst' = fstP :@> (TIdx 4) :@> natT
   snd' = sndP :@> (TIdx 4) :@> natT
   nextPair = (lV "k" (internalPairType) $ pF :@> (TIdx 4) :@> natT
                   :@: (Idx 2 :@: (fst' :@: Idx 0) :@: (snd' :@: Idx 0)) -- первый элемент пары -- f k succ
                   :@: (suc :@: (snd' :@: Idx 0))) -- Второй элемент пары -- suc succ
-- её тип:
recT = ForAll "iniT" (natT :-> (TIdx 0 :-> natT :-> TIdx 0) :-> TIdx 0 :-> TIdx 0)

-- теперь можно определить простые функции над числами Чёрча
pre = lV "n" natT $ rec :@> natT :@: Idx 0 :@: preFun :@: preIni
preFun = lV "a" natT $ lV "b" natT $ Idx 0
preIni = zero

fac = lV "n" natT $ rec :@> natT :@: Idx 0 :@: facFun :@: facIni
facFun = lV "a" natT $ lV "b" natT $ mult :@: (Idx 1) :@: (suc :@: Idx 0)
facIni = one

-- тест на тип:
testRecNatPair = (infer0 recNatPair == Just (ForAll "iniT" (natT :-> ((TIdx 0 :-> (natT :-> TIdx 0)) :-> (TIdx 0 :-> ForAll "b" ((TIdx 1 :-> (natT :-> TIdx 0)) :-> TIdx 0))))))


-- типизация
answer11 = lV "f" topT $ (Idx 0 :@> (topT :-> topT)) :@: (Idx 0 :@> topT) :@: Idx 0
answer12 = lV "f" topT $ ((Idx 0 :@> topT) :@: Idx 0) :@> topT :@: Idx 0
answer21 = lV "f" boolT $ (Idx 0 :@> boolT) :@: Idx 0 :@: Idx 0
answer22 = lV "f" boolT $ lT "b" $ (Idx 1 :@> (TIdx 0 :-> TIdx 0 :-> TIdx 0)) :@: (Idx 1 :@> TIdx 0) :@: (Idx 1 :@> TIdx 0)
answer31 = lV "f" botT $ Idx 0 :@> (botT :-> botT :-> botT) :@: Idx 0 :@: Idx 0
answer32 = lV "f" botT $ (Idx 0 :@> (botT :-> botT) :@: Idx 0) :@> (botT :-> botT) :@: Idx 0
answer41 = lV "f" topT $ lT "t" $ Idx 1 :@> ((TIdx 0 :-> TIdx 0) :-> TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> (TIdx 0 :-> TIdx 0)):@: ((Idx 1 :@> (TIdx 0 :-> TIdx 0)) :@: (Idx 1 :@> TIdx 0))
answer42 = lV "f" topT $ (Idx 0 :@> (topT :-> topT)) :@: (Idx 0 :@> topT) :@: ((Idx 0 :@> topT) :@: Idx 0)
answer51 = lV "f" botT $ (Idx 0 :@> (topT :-> boolT :-> botT)) :@: (Idx 0 :@> topT) :@: (Idx 0 :@> (botT :-> boolT) :@: Idx 0)
answer52 = lV "f" botT $ (Idx 0 :@> (botT :-> botT :-> botT)) :@: Idx 0 :@: (Idx 0 :@> (botT :-> botT) :@: Idx 0)
-- почему-то тестовая система считает, что я нарушил порядок аппликации исходных термов -- ей виднее :)
answer53 = lV "f" botT $ (Idx 0 :@> (botT :-> botT)) :@: (lT "a" $ (Idx 1 :@> (TIdx 0 :-> TIdx 0)) :@: ((Idx 1 :@> (topT :-> TIdx 0)) :@: (Idx 1 :@> topT)))
answer61 = lV "f" boolT $ Idx 0 :@> boolT :@: Idx 0 
answer62 = lV "f" boolT $ (Idx 0 :@> (ForAll "t" (TIdx 0 :-> TIdx 0 :-> TIdx 0))) :@: (lT "x" $ (Idx 1 :@> TIdx 0))

--answer7 = lV "s" undefined $ lV "z" undefined $ Idx 1 :@: (Idx 1 :@: Idx 0)
a7pt1 = ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 0)
a7pt2 = ForAll "a" (TIdx 0 :-> TIdx 0)
--answer7 = lV "s" (ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 0)) $ lV "z" (ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 1 :-> TIdx 0)) $ Idx 1 :@> (TIdx 1 :-> (ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 1 :-> TIdx 0))) :@: (Idx 1 :@> (ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 1 :-> TIdx 0)) :@: Idx 0)
--answer7 = lV "s" a7pt1 $ lV "z" a7pt2 $ (Idx 1 :@> (TIdx 0 :-> a7pt2)) :@: ((Idx 1 :@> a7pt2) :@: Idx 0)
answer7 = lV "s" (ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 0)) $ lV "z" (ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 1 :-> TIdx 0)) $ Idx 1

ty7 = ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 0) :-> ForAll "a" (TIdx 0 :-> TIdx 1 :-> TIdx 1 :-> TIdx 0)
testOfAnsw7 = infer [TDecl "beta"] answer7 == Just ty7

--- тесты
botT = ForAll "a" (TIdx 0)
topT = ForAll "a" (TIdx 0 :-> TIdx 0)
-- boolT = ForAll "a" (TIdx 0 :-> TIdx 0 :-> TIdx 0)
-- типовой индекс в типе ссылается на номер объемлющего ForAll
botF = ForAll "a" (TIdx 0)
tArr  = TIdx 0 :-> TIdx 0
topF = ForAll "a" tArr
-- Кодирование самоприменения в System F (примеры из лекции)
sa0 = lV "z" botF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa1 = lV "z" topF $ lT "b" $ Idx 1 :@> (TIdx 0 :-> TIdx 0) :@: (Idx 1 :@> TIdx 0)
sa2 = lV "z" topF $ Idx 0 :@> topF :@: Idx 0

-- Комбинатор $I$ (TIdx 0 в cIFopen ссылается в никуда, нужен контекст)
cIFopen = lV "x" (TIdx 0) $ Idx 0  
cIF = lT "a" $ lV "x" (TIdx 0) $ Idx 0

-- Комбинаторы $K$ и $K_\ast$
tK    = TIdx 1 :-> TIdx 0 :-> TIdx 1
tKF = ForAll "a" $ ForAll "b" tK
cKF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 1
tKast = TIdx 1 :-> TIdx 0 :-> TIdx 0
tKastF = ForAll "a" $ ForAll "b" tKast
cKastF = lT "a" $ lT "b" $ lV "x" (TIdx 1) $ lV "y" (TIdx 1) $ Idx 0

-- Комбинатор $C$ 
tFlip = (TIdx 2 :-> TIdx 1 :-> TIdx 0) :-> TIdx 1 :-> TIdx 2 :-> TIdx 0
tFlipF = ForAll "a" $ ForAll "b" $ ForAll "c" $ tFlip
cFlipF = lT "a" $ lT "b" $ lT "c" $ lV "f" (TIdx 2 :-> TIdx 1 :-> TIdx 0) $ lV "y" (TIdx 2) $ lV "x" (TIdx 4) $ Idx 2 :@: Idx 0 :@: Idx 1

-- Кодирование булевых значений в System F
boolT = ForAll "a" $ TIdx 0 :-> TIdx 0 :-> TIdx 0
fls = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 0
tru = lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 1

ifThenElse = lT "a" $ lV "v" boolT $ lV "x" (TIdx 1) $ lV "y" (TIdx 2) $ Idx 2 :@> TIdx 3 :@: Idx 1 :@: Idx 0
notF = lV "v" boolT $ lT "a" $ lV "t" (TIdx 0) $ lV "f" (TIdx 1) $ Idx 3 :@> TIdx 2 :@: Idx 0 :@: Idx 1

-- Кодирование натуральных чисел в System F
natT = ForAll "a" $ (TIdx 0 :-> TIdx 0) :-> TIdx 0 :-> TIdx 0
natAbs body = lT "a" $ lV "s" (TIdx 0 :-> TIdx 0) $ lV "z" (TIdx 1) body
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


--- test oneStep
(<&>) = flip (<$>)
iteReduced = (oneStep (ifThenElse :@> boolT) <&> (\x->x :@: fls :@: tru :@: cKF)) == (oneStep (ifThenElse :@> boolT :@: fls :@: tru :@: cKF))
