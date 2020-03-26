import Data.List

type Symb = String 

infixr 3 :->

data Type = TVar Symb      -- типовый атом
          | Type :-> Type  -- стрелочный тип
    deriving (Read,Show,Eq,Ord)

type Ctx = [Type] -- контекст

data TNF = Meta   -- метапеременная (пока еще бесструктурная часть схемы)
             Type   -- типизирована
         | TNF    -- структурированная часть схемы
             Ctx    -- абстрактор 
             Int    -- головная переменная как индекс Де Брауна
             [TNF]  -- бёмовы хвостики
    deriving (Read,Show,Eq,Ord) 

uncurry2List :: Type -> (Symb,[Type])
uncurry2List (TVar name) = (name, [])
uncurry2List (t1 :-> t2) = (t1:) <$> uncurry2List t2

uncurry2RevList :: Type -> (Symb,[Type])
uncurry2RevList t = go [] (uncurry2List t)
 where
  go buf (name, x:xs) = go (x:buf) (name, xs)
  go buf (name, []  ) = (name, buf)

-- раскрытие метапеременной в структурированную схему (в контексте)
envelopMeta :: Ctx -> Type -> [TNF]
envelopMeta ctx (TVar name) = do
  -- перебираем все возможные доступные типы из контектса (с номером)
  (i, t) <- zip [0..] ctx
  -- ищем, кто заканчивается на ту же переменную
  ctx' <- [c | let (name', c) = uncurry2List t, name == name']
  return $ TNF [] i (Meta <$> ctx')
envelopMeta ctx t@(a :-> b) = do
  let (alpha, typelist) = uncurry2RevList t
  -- расширяем контекст найденными типами
  (TNF [] idx tails) <- envelopMeta (typelist ++ ctx) (TVar alpha)
  -- добавляем найденные типы к структурному описанию
  return $ TNF typelist idx tails


unMeta :: Ctx -> TNF -> [TNF]
unMeta ctx (Meta t) = envelopMeta ctx t -- для метапеременных применяем субалгоритм раскрытия
unMeta ctx (TNF abs i ts) = do -- для NF-схем делаем рекурсивные вызовы
  -- добавляем абстрактор к текущему контексту и вызываем алгоритм подстановки метапеременных рекурсивно
  ts' <- sequenceA $ (unMeta (abs ++ ctx)) <$> ts -- аппл. функтор, семантика: каждый с каждым
  return $ TNF abs i ts' -- обновляем все возможные Бёмовы хвостики

unMeta0 :: Type -> [TNF]
unMeta0 t = unMeta [] (Meta t)

--- tests
tArr = TVar "a" :-> TVar "a"

tNat = tArr :-> tArr

tBool = TVar "a" :-> TVar "a" :-> TVar "a"

tK = TVar "a" :-> TVar "b" :-> TVar "a"

tKast = TVar "a" :-> TVar "b" :-> TVar "b"

tBiNat = (TVar "a" :-> TVar "a") :-> (TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBiBiNat = (TVar "a" :-> TVar "b") :-> (TVar "b" :-> TVar "a") :-> TVar "a" :-> TVar "a"

tBinTree = (TVar "a" :-> TVar "a" :-> TVar "a") :-> TVar "a" :-> TVar "a"

hw3last1 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "a"

hw3last2 = ((TVar "a" :-> TVar "b") :-> TVar "a") :-> (TVar "a" :-> TVar "a" :-> TVar "b") :-> TVar "b"

t3 = ((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a"

contFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "d")
               :-> (TVar "b" :-> TVar "c") :-> TVar "d"

selFmapT = (TVar "a" :-> TVar "b") :->  ((TVar "a" :-> TVar "c") :-> TVar "a") 
               :-> (TVar "b" :-> TVar "c") :-> TVar "b"

monsterT = (((TVar "a" :-> TVar "a") :-> TVar "a") :-> TVar "a") :-> TVar "a" :-> TVar "a"

fixT = (TVar "a" :-> TVar "a") :-> TVar "a"

peirceT = ((TVar "p" :-> TVar "q") :-> TVar "p") :-> TVar "p"