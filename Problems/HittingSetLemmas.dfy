include "HittingSet.dfy"
include "../Foundations/Collections.dfy"

lemma hitting_set_certificate_volume_bound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, hittingSet:set<T>)
  requires HittingSetCertificate(universe, sets, cardinality, hittingSet)
  ensures |hittingSet| <= |universe|
{
  subset_cardinality_bound_set(hittingSet, universe);
}

lemma hitting_set_singleton_cardinality_setset<T>(sets:set<set<T>>)
  ensures |set member | member in sets :: {member}| == |sets|
  decreases |sets|
{
  if sets != {} {
    var member :| member in sets;
    var remaining := sets-{member};
    hitting_set_singleton_cardinality_setset(remaining);
    assert (set item | item in sets :: {item}) == (set item | item in remaining :: {item})+{{member}};
    assert {member} !in (set item | item in remaining :: {item});
  }
}
