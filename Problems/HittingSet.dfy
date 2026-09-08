
ghost predicate HittingSet<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat)
  requires HittingSetValidInstance(universe, sets)
{
  exists s:set<T> | s <= universe :: HittingSetCertificate(universe, sets, cardinality, s)
}

ghost predicate HittingSetValidInstance<T>(universe:set<T>, sets:set<set<T>>)
{
  forall s | s in sets :: s <= universe
}

// A size restriction only: membership in the universe is still checked.
ghost predicate HittingSetAdmissibleCertificate<T>(universe:set<T>, hittingSet:set<T>)
{
  |hittingSet| <= |universe|
}

ghost predicate HittingSetCertificate<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, hittingSet:set<T>)
{
  hittingSet <= universe && hitsSets(sets, hittingSet) && |hittingSet| <= cardinality
}

ghost predicate hitsSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}
