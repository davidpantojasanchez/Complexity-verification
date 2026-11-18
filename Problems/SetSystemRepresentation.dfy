include "SetSystem.dfy"
include "../Collections/Set.dfy"

// Instrumented Set Cover and Hitting Set instances.
datatype SetSystemInstance<T(==)> = SetSystemInstance(universe:Set<T>, sets:SetSet<T>, k:nat)
{
  ghost function Model():SetSystemModel<T>
  { SetSystemModel(universe.Model(), sets.Model(), k) }

  ghost function Size(weight:T -> nat):nat
  { 1+universe.Size(weight)+sets.Size(weight)+NatBits(k) }

  ghost function {:opaque} SizeBound(weight:T -> nat):(size:nat)
    ensures universe.SizeBound(weight) <= size
    ensures sets.SizeBound(weight) <= size && NatBits(k) <= size
    ensures Size(weight) <= size
  { 1+universe.SizeBound(weight)+sets.SizeBound(weight)+NatBits(k) }
}

// Instrumented Set Cover instance with set-valued labels.
datatype SetCoverSetInstance<T(==)> = SetCoverSetInstance(universe:SetSet<T>, sets:SetSetSet<T>, k:nat)
{
  ghost function Model():SetSystemModel<set<T>>
  { SetSystemModel(universe.Model(), sets.Model(), k) }

  ghost function Size(weight:T -> nat):nat
  { 1+universe.Size(weight)+sets.Size(weight)+NatBits(k) }

  ghost function {:opaque} SizeBound(weight:T -> nat):(size:nat)
    ensures universe.SizeBound(weight) <= size
    ensures sets.SizeBound(weight) <= size && NatBits(k) <= size
    ensures Size(weight) <= size
  { 1+universe.SizeBound(weight)+sets.SizeBound(weight)+NatBits(k) }
}

ghost function SetCoverInputSize<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat):nat
{ instance.Size(weight)+certificate.Size(weight) }

// Count the entire supplied certificate, including labels outside the instance.
ghost function {:opaque} SetCoverInputSizeBound<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat):(size:nat)
  ensures instance.SizeBound(weight) <= size && certificate.SizeBound(weight) <= size
  ensures SetCoverInputSize(instance, certificate, weight) <= size
{
  instance.SizeBound(weight)+certificate.SizeBound(weight)
}
