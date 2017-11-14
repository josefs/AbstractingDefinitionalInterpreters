Document some of the issues with using algebraic effects.

* The biggest problem is that one needs to be a type system wizard.
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

* One problem seems to be that if effects have any type parameters
  (which they always have, like State, Reader and Error) then that
  parameter needs to be concrete or otherwise the Member function
  cannot match the effect.

* I've been looking for other algebraic effects libraries on Hackage,
  since I have so many problems with the freer library and types. But
  the ones that I've found come up short.

  + https://hackage.haskell.org/package/effect-handlers

    This package doesn't have a non-determinism effect, that I need. It has
    a search effect but it seems too limited.

  + https://hackage.haskell.org/package/ether

    This package is promising because it removes the problems of the
    mtl approach but allowing to easily create new monad transformers
    by tagging. Unfortunately it doesn't provide a non-determinism
    effect.

  + I should check out the work of Tom Schrijvers and see if any of his
    papers provide any solutions to my problems.

  + https://hackage.haskell.org/package/extensible-effects

    This package is likely to have the same problems as effect handlers
    but I should look at it more closely nevertheless.


* Maybe I can make my own effects library which has better typing properties!

  The idea is to not match on the type of effect when selecting effect in
  the run function. That means that if we want multiple state effects, we
  have to create new state effects. So there's a bit of a downside but
  the upside should be that we can have effects which have type parameters
  which we cannot do right now.

  That would mean though that all effects would have to be equipped with
  some form of parameter, in order for the matching/selection mechanism
  to know about the parameter and avoid selecting for it.
  Or perhaps there's another way. When match in state, say, then we let the
  type of the state be different to the occurrence in the matching head. But
  we put a type equality in the premise which forces the states to be the
  same. Something along these lines:

  instance s ~ s' => Member (State s) (State s' ': rest)