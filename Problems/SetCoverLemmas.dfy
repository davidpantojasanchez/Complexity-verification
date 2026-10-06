include "SetCover.dfy"
include "../Lemmas/ArithmeticLemmas.dfy"

lemma SetCoverCertificateSizeBound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, cover:set<set<T>>)
  requires SetCoverValidInstance(universe, sets)
  requires SetCoverCertificate(universe, sets, cardinality, cover)
  ensures |cover| <= |sets|
  ensures forall s | s in cover :: |s| <= |universe|
{
  SubsetCardinalityBound(cover, sets);
  forall s | s in cover ensures |s| <= |universe| {
    SubsetCardinalityBound(s, universe);
  }
}
