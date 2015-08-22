-- | Tainted Monad Transformer
module Control.Monad.Trans.Tainted

import Data.Tainted

-- | 'TaintedT' is a monad transformer of 'Tainted'
data TaintedT : (Type -> Type) -> Type where
  mkTaintedT : {m : Monad} -> m (Tainted a) -> TaintedT m a


-- | Lift a 'Tainted' into an 'TaintedT'
--hoistTainted : Monad m => Tainted a -> TaintedT m a
--hoistTainted = mkTaintedT . return
