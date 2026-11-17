include "SetSystem.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Foundations/RepresentationBounds.dfy"
include "../Collections/Set.dfy"

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

// Instrumented Set Cover and Hitting Set instances.
datatype SetSystemInstance<T(==)> = SetSystemInstance(universe:Set<T>, sets:SetSet<T>, k:nat)
{
  ghost function Model():SetSystemModel<T>
  { SetSystemModel(universe.Model(), sets.Model(), k) }
}

// Instrumented Set Cover instance with set-valued labels.
datatype SetCoverSetInstance<T(==)> = SetCoverSetInstance(universe:SetSet<T>, sets:SetSetSet<T>, k:nat)
{
  ghost function Model():SetSystemModel<set<T>>
  { SetSystemModel(universe.Model(), sets.Model(), k) }
}

// Bound the model components of a Set Cover or Hitting Set instance.
ghost function {:opaque} SetSystemInstanceSizeBound<T>(instance:SetSystemInstance<T>, weight:T -> nat):(size:nat)
  ensures instance.universe.SizeBound(weight) <= size
  ensures instance.sets.SizeBound(weight) <= size && NatBits(instance.k) <= size
  ensures SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight) <= size
{
  var U, S := instance.universe, instance.sets;
  representation_bound_set(U.Model(), weight);
  representation_bound_setset(S.Model(), weight);
  1+U.SizeBound(weight)+S.SizeBound(weight)+NatBits(instance.k)
}

// Count the entire supplied certificate, including labels outside the instance.
ghost function {:opaque} SetCoverInputSizeBound<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat):(size:nat)
  ensures SetSystemInstanceSizeBound(instance, weight) <= size && certificate.SizeBound(weight) <= size
  ensures SetCoverInputSize(instance.universe.Model(), instance.sets.Model(), instance.k, certificate.Model(), weight) <= size
{
  representation_bound_setset(certificate.Model(), weight);
  SetSystemInstanceSizeBound(instance, weight)+certificate.SizeBound(weight)
}
