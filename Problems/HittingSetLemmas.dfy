include "HittingSet.dfy"
include "../Lemmas/ArithmeticLemmas.dfy"

lemma HittingSetCertificateSizeBound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, hittingSet:set<T>)
  requires HittingSetCertificate(universe, sets, cardinality, hittingSet)
  ensures |hittingSet| <= |universe|
{
  SubsetCardinalityBound(hittingSet, universe);
}
