/*
Abstract interfaces for immutable sets and nested sets.

Every operation has a base cost of 1. Exact operation costs depend on the current
model. Their Universe variants provide stable upper bounds for external
verification. The cost_* functions are the single source of truth for these
formulas.

Concrete implementations are defined in ConcreteSet.dfy.
*/
lemma nat_multiply_right_mono(a:nat, b:nat, factor:nat)
  requires a <= b
  ensures a * factor <= b * factor
{}


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
    (Cardinality() <= UBCardinality())
  }

  ghost function Size0():nat { Cardinality() }
  ghost function UBSize0():nat { UBCardinality() }
  ghost function UBCardinality():nat { |Universe()| }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + cost_SetPick(this)

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_SetEmpty(this)

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_SetNElements(this)

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + cost_SetContains(this)
    ensures counter_out <= counter_in + cost_SetContainsUniverse(this)

  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures counter_out == counter_in + cost_SetAdd(this)
    ensures counter_out <= counter_in + cost_SetAddUniverse(this)

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_SetRemove(this)
    ensures counter_out <= counter_in + cost_SetRemoveUniverse(this)

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + cost_SetCopy(this)
    ensures counter_out <= counter_in + cost_SetCopyUniverse(this)
}


trait SetSet<T(==)> {
  // Compilable representation view. Intended for concrete implementations only.
  function Repr():set<set<T>>
  ghost function {:opaque} Model():set<set<T>> { Repr() }
  ghost function Universe():set<set<T>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= UBCardinality()) &&
    (forall s | s in Universe() :: UBSize1() >= |s|)
  }

  ghost function UBSize1():nat
  ghost function Size0():nat { Cardinality() * UBSize1() }
  ghost function UBSize0():nat { UBCardinality() * UBSize1() }
  ghost function UBCardinality():nat { |Universe()| }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e.Valid()
    ensures e.Size0() <= UBSize1()
    ensures e.UBSize0() <= UBSize1()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + cost_SetSetPick(this, e)
    ensures counter_out <= counter_in + cost_SetSetPickUniverse(this)

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_SetSetEmpty(this)

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_SetSetNElements(this)

  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + cost_SetSetContains(this)
    ensures counter_out <= counter_in + cost_SetSetContainsUniverse(this)

  method Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.Size0() <= UBSize1() then R.UBSize1() == UBSize1()
            else R.UBSize1() == e.Size0()
    ensures (R.UBSize1() == UBSize1()) || (R.UBSize1() == e.Size0())
    ensures counter_out == counter_in + cost_SetSetAdd(this)
    ensures counter_out <= counter_in + cost_SetSetAddUniverse(this)

  method Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.UBSize1() <= UBSize1()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_SetSetRemove(this)
    ensures counter_out <= counter_in + cost_SetSetRemoveUniverse(this)

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.UBSize1() == UBSize1()
    ensures counter_out == counter_in + cost_SetSetCopy(this)
    ensures counter_out <= counter_in + cost_SetSetCopyUniverse(this)
}


trait SetSetSet<T(==)> {
  // Compilable representation view. Intended for concrete implementations only.
  function Repr():set<set<set<T>>>
  ghost function {:opaque} Model():set<set<set<T>>> { Repr() }
  ghost function Universe():set<set<set<T>>>

  ghost function Valid():bool
  {
    (Model() <= Universe()) &&
    (Cardinality() <= UBCardinality()) &&
    (forall s | s in Universe() :: forall s' | s' in s :: UBSize1() >= |s|*|s'|) &&
    (forall s | s in Universe() :: forall s' | s' in s :: UBSize2() >= |s'|)
  }

  ghost function UBSize1():nat
  ghost function UBSize2():nat
  ghost function Size0():nat { Cardinality()*UBSize1() }
  ghost function UBSize0():nat { UBCardinality()*UBSize1() }
  ghost function UBCardinality():nat { |Universe()| }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires Model() != {}
    ensures e.Valid()
    ensures e.Size0() <= UBSize1()
    ensures e.UBSize0() <= UBSize1()
    ensures e.UBSize1() <= UBSize2()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + cost_SetSetSetPick(this, e)
    ensures counter_out <= counter_in + cost_SetSetSetPickUniverse(this)

  method Empty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + cost_SetSetSetEmpty(this)

  method nElements(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_SetSetSetNElements(this)

  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + cost_SetSetSetContains(this)
    ensures counter_out <= counter_in + cost_SetSetSetContainsUniverse(this)

  method Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires e.Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.Size0() <= UBSize1() then R.UBSize1() == UBSize1()
            else R.UBSize1() == e.Size0()
    ensures if e.UBSize1() <= UBSize2() then R.UBSize2() == UBSize2()
            else R.UBSize2() == e.UBSize1()
    ensures ((R.UBSize1() == UBSize1()) || (R.UBSize1() == e.Size0())) &&
            ((R.UBSize2() == UBSize2()) || (R.UBSize2() == e.UBSize1()))
    ensures counter_out == counter_in + cost_SetSetSetAdd(this)
    ensures counter_out <= counter_in + cost_SetSetSetAddUniverse(this)

  method Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Universe() == Universe()
    ensures R.UBSize1() <= UBSize1()
    ensures R.UBSize2() <= UBSize2()
    ensures R.Model() == Model() - {e.Model()}
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures counter_out == counter_in + cost_SetSetSetRemove(this)
    ensures counter_out <= counter_in + cost_SetSetSetRemoveUniverse(this)

  method Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures R.UBSize1() == UBSize1()
    ensures R.UBSize2() == UBSize2()
    ensures counter_out == counter_in + cost_SetSetSetCopy(this)
    ensures counter_out <= counter_in + cost_SetSetSetCopyUniverse(this)
}


lemma SetModelSizeBound<T>(S:Set<T>)
  requires S.Valid()
  ensures S.Size0() <= S.UBSize0()
{}

lemma SetSetModelSizeBound<T>(S:SetSet<T>)
  requires S.Valid()
  ensures S.Size0() <= S.UBSize0()
{
  nat_multiply_right_mono(S.Cardinality(), S.UBCardinality(), S.UBSize1());
}

lemma SetSetSetModelSizeBound<T>(S:SetSetSet<T>)
  requires S.Valid()
  ensures S.Size0() <= S.UBSize0()
{
  nat_multiply_right_mono(S.Cardinality(), S.UBCardinality(), S.UBSize1());
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


ghost function cost_SetPick<T>(S:Set<T>):nat { 1 }
ghost function cost_SetEmpty<T>(S:Set<T>):nat { 1 }
ghost function cost_SetNElements<T>(S:Set<T>):nat { 1 }
ghost function cost_SetContains<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function cost_SetContainsUniverse<T>(S:Set<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetAdd<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function cost_SetAddUniverse<T>(S:Set<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetRemove<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function cost_SetRemoveUniverse<T>(S:Set<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetCopy<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function cost_SetCopyUniverse<T>(S:Set<T>):nat { S.UBSize0() + 1 }
ghost function cost_NewSet():nat { 1 }

ghost function cost_SetSetPick<T>(S:SetSet<T>, e:Set<T>):nat { e.Size0() + 1 }
ghost function cost_SetSetPickUniverse<T>(S:SetSet<T>):nat { S.UBSize1() + 1 }
ghost function cost_SetSetEmpty<T>(S:SetSet<T>):nat { 1 }
ghost function cost_SetSetNElements<T>(S:SetSet<T>):nat { 1 }
ghost function cost_SetSetContains<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetContainsUniverse<T>(S:SetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetSetAdd<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetAddUniverse<T>(S:SetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetSetRemove<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetRemoveUniverse<T>(S:SetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetSetCopy<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetCopyUniverse<T>(S:SetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_NewSetSet():nat { 1 }

ghost function cost_SetSetSetPick<T>(S:SetSetSet<T>, e:SetSet<T>):nat
{ e.Size0() + 1 }
ghost function cost_SetSetSetPickUniverse<T>(S:SetSetSet<T>):nat
{ S.UBSize1() + 1 }
ghost function cost_SetSetSetEmpty<T>(S:SetSetSet<T>):nat { 1 }
ghost function cost_SetSetSetNElements<T>(S:SetSetSet<T>):nat { 1 }
ghost function cost_SetSetSetContains<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetSetContainsUniverse<T>(S:SetSetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetSetSetAdd<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetSetAddUniverse<T>(S:SetSetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetSetSetRemove<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetSetRemoveUniverse<T>(S:SetSetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_SetSetSetCopy<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function cost_SetSetSetCopyUniverse<T>(S:SetSetSet<T>):nat { S.UBSize0() + 1 }
ghost function cost_NewSetSetSet():nat { 1 }
