include "HittingSet.dfy"
include "../Lemmas/NativeCollectionLemmas.dfy"

lemma hitting_set_certificate_size_bound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, hittingSet:set<T>)
  requires HittingSetCertificate(universe, sets, cardinality, hittingSet)
  ensures |hittingSet| <= |universe|
{
  subset_cardinality_bound(hittingSet, universe);
}
