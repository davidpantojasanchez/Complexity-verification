
ghost predicate SetCover<T>(universe:set<T>, sets: set<set<T>>, cardinality:nat)
  requires forall s | s in sets :: s <= universe // los sets son subsets del universo
  requires isCover(universe, sets) // existe un subconjunto de sets tal que su union es igual al universo
{
  exists C:set<set<T>> | C <= sets :: isCover(universe, C) && |C| <= cardinality
}

ghost predicate isCover<T>(universe:set<T>, sets:set<set<T>>)
{
  forall e | e in universe :: (exists s | s in sets :: e in s)
}
  