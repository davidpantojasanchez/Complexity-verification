/*
Abstract interfaces for immutable sets and nested sets.

Every operation has a base cost of 1. Exact operation costs depend on the current
model. Their Universe variants provide stable upper bounds for external
verification. The cost_* functions are the single source of truth for these
formulas.

Concrete implementations are defined in ConcreteSet.dfy.
*/
trait Set<T(==)> {
  // Compilable representation view. Intended for concrete implementations only.
  function Repr():set<T>
  // Opaque boundary keeps the compiled representation out of client proofs.
  ghost function {:opaque} Model():set<T> { Repr() }
  // Upper bound of the model. Used for adding simpler computational costs on changing models
  ghost function Universe():set<T>

  ghost predicate Valid()
  {
    (Model() <= Universe()) &&
    (Cardinality() <= UCardinality())
  }

  ghost function Size0():nat { Cardinality() }
  ghost function USize0():nat { UCardinality() }
  ghost function UCardinality():nat { |Universe()| }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:T, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e in Model()
    ensures e in Universe()
    ensures counter_out == counter_in + CostPick_Set(this)

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty_Set(this)

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_Set(this)

  method Equal(other:Set<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual_Set(this, other)
    ensures counter_out <= counter_in + UCostEqual_Set(this, other)

  method Contains(e:T, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e in Model())
    ensures counter_out == counter_in + CostContains_Set(this)
    ensures counter_out <= counter_in + UCostContains_Set(this)

  method Add(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures R.Universe() == Universe() + {e}
    ensures R.Model() == Model() + {e}
    ensures counter_out == counter_in + CostAdd_Set(this)
    ensures counter_out <= counter_in + UCostAdd_Set(this)

  method Remove(e:T, ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e}
    ensures counter_out == counter_in + CostRemove_Set(this)
    ensures counter_out <= counter_in + UCostRemove_Set(this)

  method Copy(ghost counter_in:nat) returns (R:Set<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_Set(this)
    ensures counter_out <= counter_in + UCostCopy_Set(this)
}


trait SetSet<T(==)> {
  function Repr():set<set<T>>
  ghost function {:opaque} Model():set<set<T>> { Repr() }
  ghost function Universe():set<set<T>>

  ghost predicate Valid()
  {
    (Model() <= Universe()) &&
    (Cardinality() <= UCardinality()) &&
    (forall s | s in Universe() :: USize1() >= |s|)
  }

  ghost function Size1():nat { MaxCardinality_set(Model()) }
  // Keep universe maxima out of client cost proofs; use the size-bound lemmas.
  ghost function {:opaque} USize1():nat { MaxCardinality_set(Universe()) }
  ghost function Size0():nat { Cardinality() * Size1() }
  ghost function USize0():nat { UCardinality() * USize1() }
  ghost function UCardinality():nat { |Universe()| }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:Set<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Size0() <= USize1()
    ensures e.USize0() <= USize1()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + CostPick_SetSet(this, e)
    ensures counter_out <= counter_in + UCostPick_SetSet(this)

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty_SetSet(this)

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_SetSet(this)

  // Compare family contents, charging for both operands.
  method Equal(other:SetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual_SetSet(this, other)
    ensures counter_out <= counter_in + UCostEqual_SetSet(this, other)

  method Contains(e:Set<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains_SetSet(this)
    ensures counter_out <= counter_in + UCostContains_SetSet(this)

  method Add(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.Size0() <= USize1() then R.USize1() == USize1()
            else R.USize1() == e.Size0()
    ensures (R.USize1() == USize1()) || (R.USize1() == e.Size0())
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures counter_out == counter_in + CostAdd_SetSet(this)
    ensures counter_out <= counter_in + UCostAdd_SetSet(this)

  method Remove(e:Set<T>, ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() <= USize1()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures counter_out == counter_in + CostRemove_SetSet(this)
    ensures counter_out <= counter_in + UCostRemove_SetSet(this)

  method Copy(ghost counter_in:nat) returns (R:SetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() == Size1()
    ensures R.USize1() <= USize1()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_SetSet(this)
    ensures counter_out <= counter_in + UCostCopy_SetSet(this)
}


trait SetSetSet<T(==)> {
  function Repr():set<set<set<T>>>
  ghost function {:opaque} Model():set<set<set<T>>> { Repr() }
  ghost function Universe():set<set<set<T>>>

  ghost predicate Valid()
  {
    (Model() <= Universe()) &&
    (Cardinality() <= UCardinality()) &&
    (forall s | s in Universe() :: forall s' | s' in s :: USize1() >= |s|*|s'|) &&
    (forall s | s in Universe() :: forall s' | s' in s :: USize2() >= |s'|)
  }

  ghost function Size1():nat { MaxSize_setset(Model()) }
  ghost function Size2():nat { MaxMemberCardinality_setset(Model()) }
  // Keep universe maxima out of client cost proofs; use the size-bound lemmas.
  ghost function {:opaque} USize1():nat { MaxSize_setset(Universe()) }
  ghost function {:opaque} USize2():nat { MaxMemberCardinality_setset(Universe()) }
  ghost function Size0():nat { Cardinality()*Size1() }
  ghost function USize0():nat { UCardinality()*USize1() }
  ghost function UCardinality():nat { |Universe()| }
  ghost function Cardinality():(c:nat)
    ensures 0 <= c
  { |Model()| }

  method Pick(ghost counter_in:nat) returns (e:SetSet<T>, ghost counter_out:nat)
    requires Model() != {}
    requires Valid()
    ensures e.Valid()
    ensures e.Size0() <= USize1()
    ensures e.USize0() <= USize1()
    ensures e.USize1() <= USize2()
    ensures e.Model() in Model()
    ensures e.Universe() == e.Model()
    ensures counter_out == counter_in + CostPick_SetSetSet(this, e)
    ensures counter_out <= counter_in + UCostPick_SetSetSet(this)

  method IsEmpty(ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (Model() == {})
    ensures counter_out == counter_in + CostIsEmpty_SetSetSet(this)

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_SetSetSet(this)

  // Compare nested-family contents, charging for both operands.
  method Equal(other:SetSetSet<T>, ghost counter_in:nat) returns (equal:bool, ghost counter_out:nat)
    requires Valid() && other.Valid()
    ensures equal == (Model() == other.Model())
    ensures counter_out == counter_in + CostEqual_SetSetSet(this, other)
    ensures counter_out <= counter_in + UCostEqual_SetSetSet(this, other)

  method Contains(e:SetSet<T>, ghost counter_in:nat) returns (b:bool, ghost counter_out:nat)
    requires Valid()
    ensures b == (e.Model() in Model())
    ensures counter_out == counter_in + CostContains_SetSetSet(this)
    ensures counter_out <= counter_in + UCostContains_SetSetSet(this)

  method Add(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    requires e.Valid()
    ensures R.Valid()
    ensures if e.Model() in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() + 1
    ensures if e.Size0() <= USize1() then R.USize1() == USize1()
            else R.USize1() == e.Size0()
    ensures if e.Size1() <= USize2() then R.USize2() == USize2()
            else R.USize2() == e.Size1()
    ensures ((R.USize1() == USize1()) || (R.USize1() == e.Size0())) &&
            ((R.USize2() == USize2()) || (R.USize2() == e.Size1()))
    ensures R.Universe() == Universe() + {e.Model()}
    ensures R.Model() == Model() + {e.Model()}
    ensures counter_out == counter_in + CostAdd_SetSetSet(this)
    ensures counter_out <= counter_in + UCostAdd_SetSetSet(this)

  method Remove(e:SetSet<T>, ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() <= USize1()
    ensures R.USize2() <= USize2()
    ensures if e.Model() !in Model() then R.Cardinality() == Cardinality()
            else R.Cardinality() == Cardinality() - 1
    ensures R.Universe() == Universe()
    ensures R.Model() == Model() - {e.Model()}
    ensures counter_out == counter_in + CostRemove_SetSetSet(this)
    ensures counter_out <= counter_in + UCostRemove_SetSetSet(this)

  method Copy(ghost counter_in:nat) returns (R:SetSetSet<T>, ghost counter_out:nat)
    requires Valid()
    ensures R.Valid()
    ensures R.USize1() == Size1()
    ensures R.USize2() == Size2()
    ensures R.USize1() <= USize1()
    ensures R.USize2() <= USize2()
    ensures R.Model() == Model()
    ensures R.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_SetSetSet(this)
    ensures counter_out <= counter_in + UCostCopy_SetSetSet(this)
}


// Maximum member cardinality; the empty family has size zero.
ghost function {:opaque} MaxCardinality_set<K>(sets:set<set<K>>):(size:nat)
  ensures sets == {} ==> size == 0
  decreases |sets|
{
  if sets == {} then 0 else
    var s :| s in sets;
    var rest := MaxCardinality_set(sets - {s});
    if |s| > rest then |s| else rest
}

ghost function {:opaque} MaxSize_setset<K>(sets:set<set<set<K>>>):(size:nat)
  ensures sets == {} ==> size == 0
  decreases |sets|
{
  if sets == {} then 0 else
    var s :| s in sets;
    var current := |s| * MaxCardinality_set(s);
    var rest := MaxSize_setset(sets - {s});
    if current > rest then current else rest
}

ghost function {:opaque} MaxMemberCardinality_setset<K>(sets:set<set<set<K>>>):(size:nat)
  ensures sets == {} ==> size == 0
  decreases |sets|
{
  if sets == {} then 0 else
    var s :| s in sets;
    var current := MaxCardinality_set(s);
    var rest := MaxMemberCardinality_setset(sets - {s});
    if current > rest then current else rest
}

ghost predicate Init_Set(S:Set)
{
  S.Valid() && S.Model() == S.Universe()
}

ghost predicate Init_SetSet(S:SetSet)
{
  S.Valid() && S.Model() == S.Universe()
}

ghost predicate Init_SetSetSet(S:SetSetSet)
{
  S.Valid() && S.Model() == S.Universe()
}

ghost predicate InUniverse_Set(S:Set, U:Set)
{
  S.Valid() && U.Valid() && S.Universe() <= U.Model()
}

ghost predicate InUniverse_SetSet(S:SetSet, U:SetSet)
{
  S.Valid() && U.Valid() &&
  S.Universe() <= U.Model() &&
  S.USize1() <= U.USize1()
}

ghost predicate InUniverse_SetSetSet(S:SetSetSet, U:SetSetSet)
{
  S.Valid() && U.Valid() &&
  S.Universe() <= U.Model() &&
  S.USize1() <= U.USize1() &&
  S.USize2() <= U.USize2()
}


ghost function CostPick_Set<T>(S:Set<T>):nat { 1 }
ghost function CostIsEmpty_Set<T>(S:Set<T>):nat { 1 }
ghost function CostCount_Set<T>(S:Set<T>):nat { 1 }
ghost function CostEqual_Set<T>(left:Set<T>, right:Set<T>):nat { left.Size0() + right.Size0() + 1 }
ghost function UCostEqual_Set<T>(left:Set<T>, right:Set<T>):nat { left.USize0() + right.USize0() + 1 }
ghost function CostContains_Set<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function UCostContains_Set<T>(S:Set<T>):nat { S.USize0() + 1 }
ghost function CostAdd_Set<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function UCostAdd_Set<T>(S:Set<T>):nat { S.USize0() + 1 }
ghost function CostRemove_Set<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function UCostRemove_Set<T>(S:Set<T>):nat { S.USize0() + 1 }
ghost function CostCopy_Set<T>(S:Set<T>):nat { S.Size0() + 1 }
ghost function UCostCopy_Set<T>(S:Set<T>):nat { S.USize0() + 1 }
ghost function CostNew_Set():nat { 1 }

ghost function CostPick_SetSet<T>(S:SetSet<T>, e:Set<T>):nat { e.Size0() + 1 }
ghost function UCostPick_SetSet<T>(S:SetSet<T>):nat { S.USize1() + 1 }
ghost function CostIsEmpty_SetSet<T>(S:SetSet<T>):nat { 1 }
ghost function CostCount_SetSet<T>(S:SetSet<T>):nat { 1 }
ghost function CostEqual_SetSet<T>(left:SetSet<T>, right:SetSet<T>):nat { left.Size0() + right.Size0() + 1 }
ghost function UCostEqual_SetSet<T>(left:SetSet<T>, right:SetSet<T>):nat { left.USize0() + right.USize0() + 1 }
ghost function CostContains_SetSet<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function UCostContains_SetSet<T>(S:SetSet<T>):nat { S.USize0() + 1 }
ghost function CostAdd_SetSet<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function UCostAdd_SetSet<T>(S:SetSet<T>):nat { S.USize0() + 1 }
ghost function CostRemove_SetSet<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function UCostRemove_SetSet<T>(S:SetSet<T>):nat { S.USize0() + 1 }
ghost function CostCopy_SetSet<T>(S:SetSet<T>):nat { S.Size0() + 1 }
ghost function UCostCopy_SetSet<T>(S:SetSet<T>):nat { S.USize0() + 1 }
ghost function CostNew_SetSet():nat { 1 }

ghost function CostPick_SetSetSet<T>(S:SetSetSet<T>, e:SetSet<T>):nat { e.Size0() + 1 }
ghost function UCostPick_SetSetSet<T>(S:SetSetSet<T>):nat { S.USize1() + 1 }
ghost function CostIsEmpty_SetSetSet<T>(S:SetSetSet<T>):nat { 1 }
ghost function CostCount_SetSetSet<T>(S:SetSetSet<T>):nat { 1 }
ghost function CostEqual_SetSetSet<T>(left:SetSetSet<T>, right:SetSetSet<T>):nat { left.Size0() + right.Size0() + 1 }
ghost function UCostEqual_SetSetSet<T>(left:SetSetSet<T>, right:SetSetSet<T>):nat { left.USize0() + right.USize0() + 1 }
ghost function CostContains_SetSetSet<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function UCostContains_SetSetSet<T>(S:SetSetSet<T>):nat { S.USize0() + 1 }
ghost function CostAdd_SetSetSet<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function UCostAdd_SetSetSet<T>(S:SetSetSet<T>):nat { S.USize0() + 1 }
ghost function CostRemove_SetSetSet<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function UCostRemove_SetSetSet<T>(S:SetSetSet<T>):nat { S.USize0() + 1 }
ghost function CostCopy_SetSetSet<T>(S:SetSetSet<T>):nat { S.Size0() + 1 }
ghost function UCostCopy_SetSetSet<T>(S:SetSetSet<T>):nat { S.USize0() + 1 }
ghost function CostNew_SetSetSet():nat { 1 }
