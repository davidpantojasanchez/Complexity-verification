/*
Abstract interfaces for immutable sets and nested sets.

Every operation has a base cost of 1. Operations whose cost also depends on the
size of the data add that variable cost to the base cost. The cost_* functions
are the single source of truth for these formulas.

Concrete implementations are defined in ConcreteSet.dfy.
*/
ghost function cost_Pick(element_size_bound:nat):nat { element_size_bound + 1 }
ghost function cost_Empty():nat { 1 }
ghost function cost_nElements():nat { 1 }
ghost function cost_Contains(size_bound:nat):nat { size_bound + 1 }
ghost function cost_Add(size_bound:nat):nat { size_bound + 1 }
ghost function cost_Remove(size_bound:nat):nat { size_bound + 1 }
ghost function cost_Copy(size_bound:nat):nat { size_bound + 1 }
ghost function cost_New():nat { 1 }


trait Set<T(==)> {
  // Compilable representation view. Intended for concrete implementations only.
  function Repr():set<T>
  // Model used for verification. Separated from Repr because making it opaque is very useful
  ghost function {:opaque} Model():set<T> { Repr() }
  // Upper bound of the model. Used for adding simpler computational costs on changing models
  ghost function Universe():set<T>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|)
  }

  ghost function UBSize0():nat { Cardinality() }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + cost_Pick(0)

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_Empty()

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + cost_Contains(UBSize0())

  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures counter_out == counter_in + cost_Add(UBSize0())

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_Remove(UBSize0())

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + cost_Copy(UBSize0())
}


trait SetSet<T(==)> {
  // Compilable representation view. Intended for concrete implementations only.
  function Repr():set<set<T>>
  ghost function {:opaque} Model():set<set<T>> { Repr() }
  ghost function Universe():set<set<T>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|) &&
    (forall s | s in Universe() :: UBSize1() >= |s|)
  }

  ghost function UBSize1():nat
  ghost function UBSize0():nat { Cardinality() * UBSize1() }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e.Valid()
    ensures e.UBSize0() <= UBSize1()
    ensures e.Model() in Model()
    ensures counter_out == counter_in + cost_Pick(UBSize1())

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_Empty()

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()

  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + cost_Contains(UBSize0())

  method Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.UBSize0() <= UBSize1() then R.UBSize1() == UBSize1()
            else R.UBSize1() == e.UBSize0()
    ensures (R.UBSize1() == UBSize1()) || (R.UBSize1() == e.UBSize0())
    ensures counter_out == counter_in + cost_Add(UBSize0())

  method Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.UBSize1() <= UBSize1()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_Remove(UBSize0())

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.UBSize1() == UBSize1()
    ensures counter_out == counter_in + cost_Copy(UBSize0())
}


trait SetSetSet<T(==)> {
  // Compilable representation view. Intended for concrete implementations only.
  function Repr():set<set<set<T>>>
  ghost function {:opaque} Model():set<set<set<T>>> { Repr() }
  ghost function Universe():set<set<set<T>>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= |Universe()|) &&
    (forall s | s in Universe() :: forall s' | s' in s :: UBSize1() >= |s|*|s'|) &&
    (forall s | s in Universe() :: forall s' | s' in s :: UBSize2() >= |s'|)
  }

  ghost function UBSize1():nat
  ghost function UBSize2():nat
  ghost function UBSize0():nat { Cardinality()*UBSize1() }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e.Valid()
    ensures e.UBSize0() <= UBSize1()
    ensures e.UBSize1() <= UBSize2()
    ensures e.Model() in Model()
    ensures counter_out == counter_in + cost_Pick(UBSize1())

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_Empty()

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()

  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + cost_Contains(UBSize0())

  method Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires e.Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.UBSize0() <= UBSize1() then R.UBSize1() == UBSize1()
            else R.UBSize1() == e.UBSize0()
    ensures if e.UBSize1() <= UBSize2() then R.UBSize2() == UBSize2()
            else R.UBSize2() == e.UBSize1()
    ensures ((R.UBSize1() == UBSize1()) || (R.UBSize1() == e.UBSize0())) &&
            ((R.UBSize2() == UBSize2()) || (R.UBSize2() == e.UBSize1()))
    ensures counter_out == counter_in + cost_Add(UBSize0())

  method Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.UBSize1() <= UBSize1()
    ensures R.UBSize2() <= UBSize2()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_Remove(UBSize0())

  method Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.UBSize1() == UBSize1()
    ensures R.UBSize2() == UBSize2()
    ensures counter_out == counter_in + cost_Copy(UBSize0())
}


ghost predicate init_Set(S:Set)
{
  S.Valid() && S.Model() == S.Universe()
}

ghost predicate init_SetSet(S:SetSet)
{
  S.Valid() && S.Model() == S.Universe()
}

ghost predicate init_SetSetSet(S:SetSetSet)
{
  S.Valid() && S.Model() == S.Universe()
}

ghost predicate in_universe_Set(S:Set, U:Set)
{
  S.Valid() && U.Valid() && S.Universe() <= U.Model()
}

ghost predicate in_universe_SetSet(S:SetSet, U:SetSet)
{
  S.Valid() && U.Valid() &&
  S.Universe() <= U.Model() &&
  S.UBSize1() <= U.UBSize1()
}

ghost predicate in_universe_SetSetSet(S:SetSetSet, U:SetSetSet)
{
  S.Valid() && U.Valid() &&
  S.Universe() <= U.Model() &&
  S.UBSize1() <= U.UBSize1() &&
  S.UBSize2() <= U.UBSize2()
}
