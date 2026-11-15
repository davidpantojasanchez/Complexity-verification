include "SetCover.dfy"
include "SetSystemRepresentation.dfy"
include "../Foundations/Collections.dfy"

lemma set_cover_certificate_volume_bound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, cover:set<set<T>>)
  requires SetCoverValidInstance(universe, sets)
  requires SetCoverCertificate(universe, sets, cardinality, cover)
  ensures |cover| <= |sets|
  ensures forall s | s in cover :: |s| <= |universe|
{
  subset_cardinality_bound_set(cover, sets);
  forall s | s in cover ensures |s| <= |universe| {
    subset_cardinality_bound_set(s, universe);
  }
}
