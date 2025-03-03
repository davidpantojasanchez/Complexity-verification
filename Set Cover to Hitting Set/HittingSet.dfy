// DEFINICION DEL PROBLEMA HITTING SET

ghost predicate HittingSet<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat)
  requires forall s | s in sets :: s <= universe // los sets son subsets del universo
{
  exists s:set<T> :: hitsSets(sets, s) && |s| <= cardinality && s <= universe
}

ghost predicate hitsSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}
