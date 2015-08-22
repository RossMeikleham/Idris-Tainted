module Data.Tainted

import Control.Algebra.Lattice
import Classes.Verified


data Tainted a = Clean a | Dirty a


instance (Show a) => Show (Tainted a) where
  show (Clean a) = "Clean " ++ (show a)
  show (Dirty a) = "Dirty " ++ (show a)


--- Semigroup Definitions
instance Semigroup a => Semigroup (Tainted a) where
  (Clean a) <+> (Clean b) = Clean (a <+> b)
  (Dirty a) <+> (Dirty b) = Dirty (a <+> b)
  (Clean a) <+> (Dirty b) = Dirty (a <+> b)
  (Dirty a) <+> (Clean b) = Dirty (a <+> b) 


--- Verify that Tainted satisfies the Semigroup laws
instance VerifiedSemigroup a => VerifiedSemigroup (Tainted a) where
 semigroupOpIsAssociative (Clean x) (Clean y) (Clean z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 semigroupOpIsAssociative (Clean x) (Clean y) (Dirty z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 semigroupOpIsAssociative (Clean x) (Dirty y) (Clean z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 semigroupOpIsAssociative (Clean x) (Dirty y) (Dirty z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 semigroupOpIsAssociative (Dirty x) (Clean y) (Clean z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 semigroupOpIsAssociative (Dirty x) (Clean y) (Dirty z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 semigroupOpIsAssociative (Dirty x) (Dirty y) (Clean z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 semigroupOpIsAssociative (Dirty x) (Dirty y) (Dirty z) = rewrite (semigroupOpIsAssociative x y z) in Refl
 

-- Monoid Definitions
instance Monoid a => Monoid (Tainted a) where
  neutral = Clean neutral 

-- Verify that Tainted satisfied the Monoid laws
instance VerifiedMonoid a => VerifiedMonoid (Tainted a) where
  monoidNeutralIsNeutralL (Clean x) = rewrite (monoidNeutralIsNeutralL x) in Refl
  monoidNeutralIsNeutralL (Dirty x) = rewrite (monoidNeutralIsNeutralL x) in Refl
  monoidNeutralIsNeutralR (Clean x) = rewrite (monoidNeutralIsNeutralR x) in Refl
  monoidNeutralIsNeutralR (Dirty x) = rewrite (monoidNeutralIsNeutralR x) in Refl


--Meet-Semilattice Definitions
instance MeetSemilattice a => MeetSemilattice (Tainted a) where
  meet (Clean x) (Clean y) = Clean (meet x y)
  meet (Dirty x) (Dirty y) = Dirty (meet x y)
  meet (Clean x) (Dirty y) = Dirty (meet x y)
  meet (Dirty x) (Clean y) = Dirty (meet x y)


instance VerifiedMeetSemilattice a => VerifiedMeetSemilattice (Tainted a) where
  meetSemilatticeMeetIsAssociative (Clean x) (Clean y) (Clean z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl
  meetSemilatticeMeetIsAssociative (Clean x) (Clean y) (Dirty z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl
  meetSemilatticeMeetIsAssociative (Clean x) (Dirty y) (Clean z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl
  meetSemilatticeMeetIsAssociative (Clean x) (Dirty y) (Dirty z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl
  meetSemilatticeMeetIsAssociative (Dirty x) (Clean y) (Clean z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl
  meetSemilatticeMeetIsAssociative (Dirty x) (Clean y) (Dirty z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl
  meetSemilatticeMeetIsAssociative (Dirty x) (Dirty y) (Clean z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl
  meetSemilatticeMeetIsAssociative (Dirty x) (Dirty y) (Dirty z) = 
    rewrite (meetSemilatticeMeetIsAssociative x y z) in Refl

  meetSemilatticeMeetIsCommutative (Clean x) (Clean y) = 
    rewrite (meetSemilatticeMeetIsCommutative x y) in Refl
  meetSemilatticeMeetIsCommutative (Clean x) (Dirty y) = 
    rewrite (meetSemilatticeMeetIsCommutative x y) in Refl
  meetSemilatticeMeetIsCommutative (Dirty x) (Clean y) = 
    rewrite (meetSemilatticeMeetIsCommutative x y) in Refl
  meetSemilatticeMeetIsCommutative (Dirty x) (Dirty y) = 
    rewrite (meetSemilatticeMeetIsCommutative x y) in Refl

  meetSemilatticeMeetIsIdempotent (Clean x) = rewrite (meetSemilatticeMeetIsIdempotent x) in Refl	 
  meetSemilatticeMeetIsIdempotent (Dirty x) = rewrite (meetSemilatticeMeetIsIdempotent x) in Refl	 
  

-- BoundedMeetSemilattice Definitions
instance BoundedMeetSemilattice a => BoundedMeetSemilattice (Tainted a) where
  top = (Clean top)
 
 
-- Verify that Tainted satisfied the BoundedMeetSemilattice laws
instance VerifiedBoundedMeetSemilattice a => VerifiedBoundedMeetSemilattice (Tainted a) where
  boundedMeetSemilatticeTopIsTop (Clean x) = rewrite (boundedMeetSemilatticeTopIsTop x) in Refl
  boundedMeetSemilatticeTopIsTop (Dirty x) = rewrite (boundedMeetSemilatticeTopIsTop x) in Refl


-- JoinSemilattice Definitions
instance JoinSemilattice a => JoinSemilattice (Tainted a) where
  join (Clean x) (Clean y) = Clean (join x y)
  join (Clean x) (Dirty y) = Clean (join x y)
  join (Dirty x) (Clean y) = Clean (join x y)
  join (Dirty x) (Dirty y) = Dirty (join x y)


-- Verify that Tainted satisfies the JoinSemilattice laws
instance VerifiedJoinSemilattice a => VerifiedJoinSemilattice (Tainted a) where
  joinSemilatticeJoinIsAssociative (Clean x) (Clean y) (Clean z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl
  joinSemilatticeJoinIsAssociative (Clean x) (Clean y) (Dirty z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl
  joinSemilatticeJoinIsAssociative (Clean x) (Dirty y) (Clean z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl
  joinSemilatticeJoinIsAssociative (Clean x) (Dirty y) (Dirty z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl
  joinSemilatticeJoinIsAssociative (Dirty x) (Clean y) (Clean z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl
  joinSemilatticeJoinIsAssociative (Dirty x) (Clean y) (Dirty z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl
  joinSemilatticeJoinIsAssociative (Dirty x) (Dirty y) (Clean z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl
  joinSemilatticeJoinIsAssociative (Dirty x) (Dirty y) (Dirty z) = 
    rewrite (joinSemilatticeJoinIsAssociative x y z) in Refl

  joinSemilatticeJoinIsCommutative (Clean x) (Clean y) = 
    rewrite (joinSemilatticeJoinIsCommutative x y) in Refl
  joinSemilatticeJoinIsCommutative (Clean x) (Dirty y) = 
    rewrite (joinSemilatticeJoinIsCommutative x y) in Refl
  joinSemilatticeJoinIsCommutative (Dirty x) (Clean y) = 
    rewrite (joinSemilatticeJoinIsCommutative x y) in Refl
  joinSemilatticeJoinIsCommutative (Dirty x) (Dirty y) = 
    rewrite (joinSemilatticeJoinIsCommutative x y) in Refl

  joinSemilatticeJoinIsIdempotent (Clean x) = rewrite (joinSemilatticeJoinIsIdempotent x) in Refl	 
  joinSemilatticeJoinIsIdempotent (Dirty x) = rewrite (joinSemilatticeJoinIsIdempotent x) in Refl	 
  

-- BoundedJoinSemilattice Definitions
instance BoundedJoinSemilattice a => BoundedJoinSemilattice (Tainted a) where
  bottom = (Dirty bottom)


-- Verify that Tainted satisfies the BoundedJoinSemilattice laws
instance VerifiedBoundedJoinSemilattice a => VerifiedBoundedJoinSemilattice (Tainted a) where
  boundedJoinSemilatticeBottomIsBottom (Clean x) = 
    rewrite (boundedJoinSemilatticeBottomIsBottom x) in Refl
  boundedJoinSemilatticeBottomIsBottom (Dirty x) = 
    rewrite (boundedJoinSemilatticeBottomIsBottom x) in Refl
  

-- Lattice Definitions, no extra operations over BoundedJoinSemilattice + BoundedMeetSemilattice
instance Lattice a => Lattice (Tainted a)


-- Verify that Tainted satisfies the Lattice laws, need to show Join and Meet absorb one
-- another
instance VerifiedLattice a => VerifiedLattice (Tainted a) where
  latticeMeetAbsorbsJoin (Clean x) (Clean y) = rewrite (latticeMeetAbsorbsJoin x y) in Refl
  latticeMeetAbsorbsJoin (Clean x) (Dirty y) = rewrite (latticeMeetAbsorbsJoin x y) in Refl
  latticeMeetAbsorbsJoin (Dirty x) (Clean y) = rewrite (latticeMeetAbsorbsJoin x y) in Refl
  latticeMeetAbsorbsJoin (Dirty x) (Dirty y) = rewrite (latticeMeetAbsorbsJoin x y) in Refl
  
  latticeJoinAbsorbsMeet (Clean x) (Clean y) = rewrite (latticeJoinAbsorbsMeet x y) in Refl
  latticeJoinAbsorbsMeet (Clean x) (Dirty y) = rewrite (latticeJoinAbsorbsMeet x y) in Refl
  latticeJoinAbsorbsMeet (Dirty x) (Clean y) = rewrite (latticeJoinAbsorbsMeet x y) in Refl
  latticeJoinAbsorbsMeet (Dirty x) (Dirty y) = rewrite (latticeJoinAbsorbsMeet x y) in Refl
   
  
-- Since Tainted has been verified to be an instance of BoundedJoinSemilattice + 
-- BoundedMeetSemilattice + Lattice it follows that Tainted is also an instance of BoundedLattice
instance BoundedLattice a => BoundedLattice (Tainted a)
instance VerifiedBoundedLattice a => VerifiedBoundedLattice (Tainted a)



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
                  (Dirty y) => Dirty y
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
  
  monadAssociativity (Dirty x) f g with (f x) 
    monadAssociativity (Dirty x) f g | Clean y with (g y) 
      monadAssociativity (Dirty x) f g | Clean y | Clean z = Refl 
      monadAssociativity (Dirty x) f g | Clean y | Dirty z = Refl 
    monadAssociativity (Dirty x) f g | Dirty y with (g y) 
      monadAssociativity (Dirty x) f g | Dirty y | Clean z = Refl 
      monadAssociativity (Dirty x) f g | Dirty y | Dirty z = Refl 


--- Tainted Functions ---

-- | Returns 'True' iff its argument is of the form 'Clean _.
isClean : Tainted a -> Bool
isClean (Clean _) = True
isClean _ = False


-- | Returns 'True' iff its argument is of the form Dirty _.  
isDirty : Tainted a -> Bool 
isDirty = not . isClean 


-- | Extract the value contained in a 'Tainted' type
extractTaint : Tainted a -> a
extractTaint (Clean a) = a
extractTaint (Dirty a) = a


-- | Extracts from a list of 'Tainted' all the 'Clean' elements. 
--   All the 'Clean' elements are extracted in order.
cleans : List (Tainted a) -> List a
cleans = map extractTaint . filter isClean 


-- | Extracts from a list of 'Tainted' all the 'Dirty' elements.
--   All the 'Dirty' elements are extracted in order.
dirtys : List (Tainted a) -> List a
dirtys = map extractTaint . filter isDirty


-- | Partitions a list of 'Tainted' into two lists. 
--   All the 'Dirty' elements are extracted, in order, to the first component of the output. 
--   Similarly the 'Clean' elements are extracted to the second component of the output.
partitionTaints : List (Tainted a) -> (List a, List a)
partitionTaints ts = (c, d)
    where c = cleans  ts
          d = dirtys  ts
