include "../Foundations/CollectionLaws.dfy"
include "SetSystem.dfy"

type HittingSetModel<T> = SetSystemModel<T>


ghost predicate HittingSet<T>(instance:HittingSetModel<T>)
  requires HittingSetValidInstance(instance)
{
  exists s:set<T> | s <= instance.universe :: HittingSetCertificate(instance, s)
}

ghost predicate HittingSetValidInstance<T>(instance:HittingSetModel<T>)
{
  SetSystemMembersWithinUniverse(instance.universe, instance.sets)
}

ghost predicate HittingSetCertificate<T>(instance:HittingSetModel<T>, hittingSet:set<T>)
{
  hittingSet <= instance.universe && HitsAllSets(instance.sets, hittingSet) && |hittingSet| <= instance.k
}

ghost predicate HitsAllSets<T>(sets:set<set<T>>, s:set<T>)
{
  forall s1 | s1 in sets :: s * s1 != {}
}

lemma hitting_set_certificate_cardinality_bound<T>(instance:HittingSetModel<T>, hittingSet:set<T>)
  requires HittingSetCertificate(instance, hittingSet)
  ensures |hittingSet| <= |instance.universe|
{
  subset_cardinality_bound_set(hittingSet, instance.universe);
}
