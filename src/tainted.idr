
module Data.Tainted

import Classes.Verified
import Idris.Core.Evaluate

data Tainted a = Clean a | Dirty a

--- Functor Definitions ---

instance Functor Tainted where
  map f (Dirty a) = Dirty (f a)
  map f (Clean a) = Clean (f a)


-- | Verify that Tainted satisfies the Functor laws
instance VerifiedFunctor Tainted where
  functorIdentity (Clean _) = Refl
  functorIdentity (Dirty _) = Refl

  functorComposition (Clean _) g1 g2 = Refl
  functorComposition (Dirty _) g1 g2 = Refl


--- Applicative Definitions ---

instance Applicative Tainted where
  pure = Clean
  (Clean f) <*> (Clean c) = Clean (f c)
  (Clean f) <*> (Dirty d) = Dirty (f d)
  (Dirty f) <*> (Clean c) = Dirty (f c) 
  (Dirty f) <*> (Dirty d) = Dirty (f d)


-- | Verify that Tainted satisfies the Applicative laws
instance VerifiedApplicative Tainted where
   applicativeMap (Clean _) _ = Refl
   applicativeMap (Dirty _) _ = Refl

   applicativeIdentity (Clean _) = Refl
   applicativeIdentity (Dirty _) = Refl
   
   applicativeComposition (Clean x) (Clean g1) (Clean g2) = Refl
   applicativeComposition (Clean x) (Clean g1) (Dirty g2) = Refl
   applicativeComposition (Clean x) (Dirty g1) (Dirty g2) = Refl
   applicativeComposition (Clean x) (Dirty g1) (Clean g2) = Refl
   applicativeComposition (Dirty x) (Dirty g1) (Dirty g2) = Refl
   applicativeComposition (Dirty x) (Dirty g1) (Clean g2) = Refl
   applicativeComposition (Dirty x) (Clean g1) (Dirty g2) = Refl
   applicativeComposition (Dirty x) (Clean g1) (Clean g2) = Refl
   
   applicativeHomomorphism x g = Refl

   applicativeInterchange x (Clean _) = Refl
   applicativeInterchange x (Dirty _) = Refl


--- Monad Definitions ---

instance Monad Tainted where
  (Dirty x) >>= f = case f x of
                  (Clean y) => Dirty y
                  y => y
  (Clean x) >>= f = f x


-- | Verify that Tainted satisfies the Monad laws
instance VerifiedMonad Tainted where
  monadApplicative (Dirty _) (Dirty _) = Refl
  monadApplicative (Dirty _) (Clean _) = Refl
  monadApplicative (Clean _) (Dirty _) = Refl
  monadApplicative (Clean _) (Clean _) = Refl
  
  monadLeftIdentity _ _  = Refl

  monadRightIdentity (Dirty _) = Refl
  monadRightIdentity (Clean _) = Refl

  monadAssociativity (Clean _) f g = Refl 
  monadAssociativity (Dirty x) f g = BelieveMe --TODO this one is pretty difficult

