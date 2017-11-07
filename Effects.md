Document some of the issues with using algebraic effects.

The biggest problem is that one needs to be a type system wizard.
The error messages are just out of this world.

Interp.hs:286:1: error:
    • Could not deduce (Ord a0)
      from the context: (Ord a,
                         Ord s,
                         Ord b,
                         Ord a3,
                         Ord a4,
                         Ord t,
                         Data.Open.Union.Internal.Member'
                           NonDetEff r (Data.Open.Union.Internal.FindElem NonDetEff r),
                         Data.Open.Union.Internal.Member'
                           (CacheOutState (Map (t, a4, a3) (Set (b, a))))
                           r
                           (Data.Open.Union.Internal.FindElem
                              (CacheOutState (Map (t, a4, a3) (Set (b, a)))) r),
                         Data.Open.Union.Internal.Member'
                           (CacheOutState (Map (t, a4, a3) (Set (b, s))))
                           r
                           (Data.Open.Union.Internal.FindElem
                              (CacheOutState (Map (t, a4, a3) (Set (b, s)))) r),
                         Data.Open.Union.Internal.Member'
                           (StoreState a)
                           r
                           (Data.Open.Union.Internal.FindElem (StoreState a) r),
                         Data.Open.Union.Internal.Member'
                           (StoreState s)
                           r
                           (Data.Open.Union.Internal.FindElem (StoreState s) r),
                         Data.Open.Union.Internal.Member'
                           (StoreState a3)
                           r
                           (Data.Open.Union.Internal.FindElem (StoreState a3) r),
                         Data.Open.Union.Internal.Member'
                           (ReaderCacheIn (Map (t, a4, a3) (Set (b, s))))
                           r
                           (Data.Open.Union.Internal.FindElem
                              (ReaderCacheIn (Map (t, a4, a3) (Set (b, s)))) r),
                         Data.Open.Union.Internal.Member'
                           (Reader a4) r (Data.Open.Union.Internal.FindElem (Reader a4) r))
        bound by the inferred type for ‘evCache’:
                   (Ord a, Ord s, Ord b, Ord a3, Ord a4, Ord t,
                    Data.Open.Union.Internal.Member'
                      NonDetEff r (Data.Open.Union.Internal.FindElem NonDetEff r),
                    Data.Open.Union.Internal.Member'
                      (CacheOutState (Map (t, a4, a3) (Set (b, a))))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (CacheOutState (Map (t, a4, a3) (Set (b, a)))) r),
                    Data.Open.Union.Internal.Member'
                      (CacheOutState (Map (t, a4, a3) (Set (b, s))))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (CacheOutState (Map (t, a4, a3) (Set (b, s)))) r),
                    Data.Open.Union.Internal.Member'
                      (StoreState a)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState a) r),
                    Data.Open.Union.Internal.Member'
                      (StoreState s)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState s) r),
                    Data.Open.Union.Internal.Member'
                      (StoreState a3)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState a3) r),
                    Data.Open.Union.Internal.Member'
                      (ReaderCacheIn (Map (t, a4, a3) (Set (b, s))))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (ReaderCacheIn (Map (t, a4, a3) (Set (b, s)))) r),
                    Data.Open.Union.Internal.Member'
                      (Reader a4) r (Data.Open.Union.Internal.FindElem (Reader a4) r)) =>
                   (t1 -> t -> Eff r b) -> t1 -> t -> Eff r b
        at Interp.hs:(286,1)-(305,14)
      The type variable ‘a0’ is ambiguous
    • In the ambiguity check for the inferred type for ‘evCache’
      To defer the ambiguity check to use sites, enable AllowAmbiguousTypes
      When checking the inferred type
        evCache :: forall a a1 s a2 b (r :: [* -> *]) t t1.
                   (Ord a, Ord s, Ord b, Ord a1, Ord a2, Ord t,
                    Data.Open.Union.Internal.Member'
                      NonDetEff r (Data.Open.Union.Internal.FindElem NonDetEff r),
                    Data.Open.Union.Internal.Member'
                      (CacheOutState (Map (t, a2, a1) (Set (b, a))))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (CacheOutState (Map (t, a2, a1) (Set (b, a)))) r),
                    Data.Open.Union.Internal.Member'
                      (CacheOutState (Map (t, a2, a1) (Set (b, s))))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (CacheOutState (Map (t, a2, a1) (Set (b, s)))) r),
                    Data.Open.Union.Internal.Member'
                      (StoreState a)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState a) r),
                    Data.Open.Union.Internal.Member'
                      (StoreState s)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState s) r),
                    Data.Open.Union.Internal.Member'
                      (StoreState a1)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState a1) r),
                    Data.Open.Union.Internal.Member'
                      (ReaderCacheIn (Map (t, a2, a1) (Set (b, s))))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (ReaderCacheIn (Map (t, a2, a1) (Set (b, s)))) r),
                    Data.Open.Union.Internal.Member'
                      (Reader a2) r (Data.Open.Union.Internal.FindElem (Reader a2) r)) =>
                   (t1 -> t -> Eff r b) -> t1 -> t -> Eff r b

Interp.hs:310:1: error:
    • Could not deduce (Data.Open.Union.Internal.Member'
                          (StoreState s1)
                          r
                          (Data.Open.Union.Internal.FindElem (StoreState s1) r))
      from the context: (Data.Open.Union.Internal.Member'
                           NonDetEff r (Data.Open.Union.Internal.FindElem NonDetEff r),
                         Data.Open.Union.Internal.Member'
                           (StoreState s2)
                           r
                           (Data.Open.Union.Internal.FindElem (StoreState s2) r),
                         Data.Open.Union.Internal.Member'
                           (StoreState s)
                           r
                           (Data.Open.Union.Internal.FindElem (StoreState s) r),
                         Data.Open.Union.Internal.Member'
                           (CacheOutState (Map (t, a2, s) (b, s2)))
                           r
                           (Data.Open.Union.Internal.FindElem
                              (CacheOutState (Map (t, a2, s) (b, s2))) r),
                         Data.Open.Union.Internal.Member'
                           (CacheOutState (Map k a))
                           r
                           (Data.Open.Union.Internal.FindElem (CacheOutState (Map k a)) r),
                         Data.Open.Union.Internal.Member'
                           (ReaderCacheIn (Map (t, a2, s) (b, s2)))
                           r
                           (Data.Open.Union.Internal.FindElem
                              (ReaderCacheIn (Map (t, a2, s) (b, s2))) r),
                         Data.Open.Union.Internal.Member'
                           (Reader a2) r (Data.Open.Union.Internal.FindElem (Reader a2) r),
                         Ord s,
                         Ord a2,
                         Ord t,
                         Eq s2,
                         Eq b)
        bound by the inferred type for ‘fixCache’:
                   (Data.Open.Union.Internal.Member'
                      NonDetEff r (Data.Open.Union.Internal.FindElem NonDetEff r),
                    Data.Open.Union.Internal.Member'
                      (StoreState s2)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState s2) r),
                    Data.Open.Union.Internal.Member'
                      (StoreState s)
                      r
                      (Data.Open.Union.Internal.FindElem (StoreState s) r),
                    Data.Open.Union.Internal.Member'
                      (CacheOutState (Map (t, a2, s) (b, s2)))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (CacheOutState (Map (t, a2, s) (b, s2))) r),
                    Data.Open.Union.Internal.Member'
                      (CacheOutState (Map k a))
                      r
                      (Data.Open.Union.Internal.FindElem (CacheOutState (Map k a)) r),
                    Data.Open.Union.Internal.Member'
                      (ReaderCacheIn (Map (t, a2, s) (b, s2)))
                      r
                      (Data.Open.Union.Internal.FindElem
                         (ReaderCacheIn (Map (t, a2, s) (b, s2))) r),
                    Data.Open.Union.Internal.Member'
                      (Reader a2) r (Data.Open.Union.Internal.FindElem (Reader a2) r),
                    Ord s, Ord a2, Ord t, Eq s2, Eq b) =>
                   (t -> Eff r a3) -> t -> Eff r b
        at Interp.hs:(310,1)-(320,12)
      The type variable ‘s1’ is ambiguous
    • In the ambiguity check for the inferred type for ‘fixCache’
      To defer the ambiguity check to use sites, enable AllowAmbiguousTypes
      When checking the inferred type
        fixCache :: forall k a s s1 a1 b a2 (r :: [* -> *]) t.
                    (Data.Open.Union.Internal.Member'
                       NonDetEff r (Data.Open.Union.Internal.FindElem NonDetEff r),
                     Data.Open.Union.Internal.Member'
                       (StoreState s1)
                       r
                       (Data.Open.Union.Internal.FindElem (StoreState s1) r),
                     Data.Open.Union.Internal.Member'
                       (StoreState s)
                       r
                       (Data.Open.Union.Internal.FindElem (StoreState s) r),
                     Data.Open.Union.Internal.Member'
                       (CacheOutState (Map (t, a1, s) (b, s1)))
                       r
                       (Data.Open.Union.Internal.FindElem
                          (CacheOutState (Map (t, a1, s) (b, s1))) r),
                     Data.Open.Union.Internal.Member'
                       (CacheOutState (Map k a))
                       r
                       (Data.Open.Union.Internal.FindElem (CacheOutState (Map k a)) r),
                     Data.Open.Union.Internal.Member'
                       (ReaderCacheIn (Map (t, a1, s) (b, s1)))
                       r
                       (Data.Open.Union.Internal.FindElem
                          (ReaderCacheIn (Map (t, a1, s) (b, s1))) r),
                     Data.Open.Union.Internal.Member'
                       (Reader a1) r (Data.Open.Union.Internal.FindElem (Reader a1) r),
                     Ord s, Ord a1, Ord t, Eq s1, Eq b) =>
                    (t -> Eff r a2) -> t -> Eff r b
Failed, modules loaded: AbstractionEffects.

One problem seems to be that if effects have any type parameters
(which they always have, like State, Reader and Error) then that
parameter needs to be concrete or otherwise the Member function
cannot match the effect.