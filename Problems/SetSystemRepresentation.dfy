include "../Foundations/CollectionSizes.dfy"

// Exact native sizes shared by Set Cover and Hitting Set. A compound label is
// weighted by its own representation size; no auxiliary trait universe occurs.

ghost function SetSystemInstanceSize<T>(universe:set<T>, sets:set<set<T>>, k:nat, weight:T -> nat):nat
{ 1+Size_set(universe, weight)+Size_set(sets, member => Size_set(member, weight))+NatBits(k) }

ghost function SetCoverCertificateSize<T>(certificate:set<set<T>>, weight:T -> nat):nat
{ Size_set(certificate, member => Size_set(member, weight)) }

ghost function HittingSetCertificateSize<T>(certificate:set<T>, weight:T -> nat):nat
{ Size_set(certificate, weight) }

ghost function SetCoverInputSize<T>(universe:set<T>, sets:set<set<T>>, k:nat, certificate:set<set<T>>, weight:T -> nat):nat
{ SetSystemInstanceSize(universe, sets, k, weight)+SetCoverCertificateSize(certificate, weight) }

ghost function HittingSetInputSize<T>(universe:set<T>, sets:set<set<T>>, k:nat, certificate:set<T>, weight:T -> nat):nat
{ SetSystemInstanceSize(universe, sets, k, weight)+HittingSetCertificateSize(certificate, weight) }

lemma set_system_dimensions_size_bound(universe:set<int>, sets:set<set<int>>, k:nat)
  ensures |universe|+|sets|+2+NatBits(k)+MaxBits_setint(universe) <=
    3*(SetSystemInstanceSize(universe, sets, k, IntBits)+1)
{
  size_properties_set(universe, IntBits);
  size_properties_setsetint(sets);
  size_extensional_set(sets, Size_setint, member => Size_set(member, IntBits));
}
