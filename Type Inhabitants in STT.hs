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

uncurry2RevList  :: Type -> (Symb,[Type])
uncurry2RevList (TVar name) = (name, [])
uncurry2RevList (t1 :-> t2) = (++[t1]) <$> uncurry2RevList t2

-- строит для каждой метапеременной список всех подходящих замен
envolutionSubalg :: Ctx -> TNF -> [TNF]
envolutionSubalg ctx (Meta t) =
    (target, typelist) =  uncurry2RevList t
	

unMeta :: Ctx -> TNF -> [TNF]
unMeta zetas (Meta t) = let
        (target, typelist) = uncurry2RevList t
    in (\x -> TNF zetas x []) <$> go zetas target typelist
  where
    go zetas target (h:t) = do
      id <- elemIndices h zetas
      return $ id: go zetas target t
	
	


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