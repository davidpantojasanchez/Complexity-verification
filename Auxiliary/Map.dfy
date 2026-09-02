include "Set.dfy"

/*
Abstract interfaces for immutable maps and maps whose keys are maps.

Map models are finite partial functions.  Universe fixes both the keys that may
occur and their associated values; Insert extends that universe when necessary.
For Map_Map_T, UBSize_Keys is a stable bound on the size of every map-valued key.

Concrete implementations and all New_* factories belong in ConcreteMap.dfy.
*/

ghost function cost_Get(size_bound:nat):nat { size_bound + 1 }
ghost function cost_Insert(size_bound:nat):nat { size_bound + 1 }


trait Map<T0(==), T1(==)> {
  ghost function Model():map<T0, T1>
  ghost function Universe():map<T0, T1>

  ghost function Keys():set<T0> { Model().Keys }
  ghost function Values():set<T1> { Model().Values }

  ghost function Valid():bool
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= |Universe()|
  }

  ghost function UBSize():nat { Cardinality() }

  ghost function Cardinality():(cardinality:nat)
    ensures 0 <= cardinality
  { |Model()| }

  method Get(key:T0, ghost counter_in:nat) returns (value:T1, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + cost_Get(UBSize())

  method Insert(key:T0, value:T1, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures if key in Keys()
            then result.Cardinality() == Cardinality()
            else result.Cardinality() == Cardinality() + 1
    ensures counter_out == counter_in + cost_Insert(UBSize())

  method Remove(key:T0, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model() - {key}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key}
    ensures if key in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures counter_out == counter_in + cost_Remove(UBSize())

  method PickKey(ghost counter_in:nat) returns (key:T0, ghost counter_out:nat)
    requires Valid()
    requires Model() != map[]
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + cost_Pick(0)

  method nPairs(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()

  method ContainsKey(key:T0, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + cost_Contains(UBSize())

  method Empty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + cost_Empty()

  method Copy(ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + cost_Copy(UBSize())
}


// Maps whose keys are maps
trait Map_Map_T<T0(==), T1(==), T2(==)> {
  ghost function Model():map<map<T0, T1>, T2>
  ghost function Universe():map<map<T0, T1>, T2>

  ghost function Keys():set<map<T0, T1>> { Model().Keys }
  ghost function Values():set<T2> { Model().Values }

  ghost function Valid():bool
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= |Universe()| &&
    (forall key | key in Universe().Keys :: |key| <= UBSize_Keys())
  }

  ghost function UBSize():nat { Cardinality() * UBSize_Keys() }
  ghost function UBSize_Keys():nat

  ghost function Cardinality():(cardinality:nat)
    ensures 0 <= cardinality
  { |Model()| }

  method Get(key:Map<T0, T1>, ghost counter_in:nat) returns (value:T2, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_Get(UBSize())

  method Insert(key:Map<T0, T1>, value:T2, ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    requires key.Valid()
    ensures result.Valid()
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.Keys() == Keys() + {key.Model()}
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality()
            else result.Cardinality() == Cardinality() + 1
    ensures if key.UBSize() <= UBSize_Keys()
            then result.UBSize_Keys() == UBSize_Keys()
            else result.UBSize_Keys() == key.UBSize()
    ensures result.UBSize_Keys() == UBSize_Keys() ||
            result.UBSize_Keys() == key.UBSize()
    ensures counter_out == counter_in + cost_Insert(UBSize())

  method Remove(key:Map<T0, T1>, ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures result.UBSize_Keys() <= UBSize_Keys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures counter_out == counter_in + cost_Remove(UBSize())

  method PickKey(ghost counter_in:nat) returns (key:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    requires Model() != map[]
    ensures key.Valid()
    ensures key.Model() in Model().Keys
    ensures key.UBSize() <= UBSize_Keys()
    ensures counter_out == counter_in + cost_Pick(UBSize_Keys())

  method nPairs(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_nElements()

  method ContainsKey(key:Map<T0, T1>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + cost_Contains(UBSize())

  method Empty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + cost_Empty()

  method Copy(ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures result.UBSize_Keys() == UBSize_Keys()
    ensures counter_out == counter_in + cost_Copy(UBSize())
}


ghost predicate init_Map(M:Map)
{
  M.Valid() && M.Model() == M.Universe()
}

ghost predicate init_Map_Map_T(M:Map_Map_T)
{
  M.Valid() && M.Model() == M.Universe()
}

ghost predicate in_universe_Map(M:Map, U:Map)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  (forall key | key in M.Universe().Keys ::
    M.Universe()[key] == U.Model()[key])
}

ghost predicate in_universe_Map_Map_T(M:Map_Map_T, U:Map_Map_T)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  M.UBSize_Keys() <= U.UBSize_Keys() &&
  (forall key | key in M.Universe().Keys ::
    M.Universe()[key] == U.Model()[key])
}
