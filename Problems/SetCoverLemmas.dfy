include "SetCover.dfy"
include "../Lemmas/NativeCollectionLemmas.dfy"

lemma set_cover_certificate_size_bound<T>(universe:set<T>, sets:set<set<T>>, cardinality:nat, cover:set<set<T>>)
  requires SetCoverValidInstance(universe, sets)
  requires SetCoverCertificate(universe, sets, cardinality, cover)
  ensures |cover| <= |sets|
  ensures forall s | s in cover :: |s| <= |universe|
{
  subset_cardinality_bound(cover, sets);
  forall s | s in cover ensures |s| <= |universe| {
    subset_cardinality_bound(s, universe);
  }
}


// Structural description bound: one family marker, one marker per member,
// and an upper bound on the number of atomic element occurrences.
ghost function PolynomialSetCoverCertificateSize(n:nat):nat
{ 1 + n + n*n }
