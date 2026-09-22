
ghost predicate HittingSet<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat)
  requires HittingSetValidInstance(universe, sets)
{
  exists s:set<T> | s <= universe :: HittingSetCertificate(universe, sets, cardinality, s)
}

ghost predicate HittingSetValidInstance<T>(universe:set<T>, sets:set<set<T>>)
{
  forall s | s in sets :: s <= universe
}

ghost predicate HittingSetCertificate<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, hittingSet:set<T>)
{
  hittingSet <= universe && HitsAllSets(sets, hittingSet) && |hittingSet| <= cardinality
}

ghost predicate HitsAllSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}
