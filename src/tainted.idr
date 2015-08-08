
module Data.Tainted

--import Classes.Verified

data Tainted a = Clean a | Dirty a


instance Functor Tainted where
  map f (Dirty a) = Dirty (f a)
  map f (Clean a) = Clean (f a)


--instance VerifiedFunctor Tainted where
--  functorIdentity = ?fid
--  functorComposition = ?comp


instance Applicative Tainted where
  pure = Clean
  (Clean f) <*> (Clean c) = Clean (f c)
  (Clean f) <*> (Dirty d) = Dirty (f d)
  (Dirty f) <*> (Clean c) = Dirty (f c) 
  (Dirty f) <*> (Dirty d) = Dirty (f d)


instance Monad Tainted where
  (Dirty x) >>= f = case f x of
                  (Clean y) => Dirty y
                  y => y
  (Clean x) >>= f = f x
