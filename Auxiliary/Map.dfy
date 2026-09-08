/*
Abstract interfaces for immutable maps and maps whose keys are maps.

Map models are finite partial functions.  Universe fixes both the keys that may
occur and their associated values; Insert extends that universe when necessary.
For Map_Map_T, UBSize_Keys is a stable bound on the size of every map-valued key.

Concrete implementations and all New_* factories belong in ConcreteMap.dfy.
*/

trait Map<T0(==), T1(==)> {
  function Repr():map<T0, T1>
  ghost function {:opaque} Model():map<T0, T1> { Repr() }
  ghost function Universe():map<T0, T1>

  ghost function Keys():set<T0> { Model().Keys }
  ghost function Values():set<T1> { Model().Values }

  ghost function Valid():bool
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UBCardinality()
  }

  ghost function Size():nat { Cardinality() }
  ghost function UBSize():nat { UBCardinality() }
  ghost function UBCardinality():nat { |Universe()| }

  ghost function Cardinality():(cardinality:nat)
    ensures 0 <= cardinality
  { |Model()| }

  method Get(key:T0, ghost counter_in:nat) returns (value:T1, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + cost_MapGet(this)
    ensures counter_out <= counter_in + cost_MapGetUniverse(this)

  method Insert(key:T0, value:T1, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures if key in Keys()
            then result.Cardinality() == Cardinality()
            else result.Cardinality() == Cardinality() + 1
    ensures counter_out == counter_in + cost_MapInsert(this)
    ensures counter_out <= counter_in + cost_MapInsertUniverse(this)

  method Remove(key:T0, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model() - {key}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key}
    ensures if key in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures counter_out == counter_in + cost_MapRemove(this)
    ensures counter_out <= counter_in + cost_MapRemoveUniverse(this)

  method PickKey(ghost counter_in:nat) returns (key:T0, ghost counter_out:nat)
    requires Valid()
    requires Model() != map[]
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + cost_MapPickKey(this)

  method nPairs(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_MapNPairs(this)

  method ContainsKey(key:T0, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + cost_MapContainsKey(this)
    ensures counter_out <= counter_in + cost_MapContainsKeyUniverse(this)

  method Empty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + cost_MapEmpty(this)

  method Copy(ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + cost_MapCopy(this)
    ensures counter_out <= counter_in + cost_MapCopyUniverse(this)
}


// Maps whose keys are maps
trait Map_Map_T<T0(==), T1(==), T2(==)> {
  function Repr():map<map<T0, T1>, T2>
  ghost function {:opaque} Model():map<map<T0, T1>, T2> { Repr() }
  ghost function Universe():map<map<T0, T1>, T2>

  ghost function Keys():set<map<T0, T1>> { Model().Keys }
  ghost function Values():set<T2> { Model().Values }

  ghost function Valid():bool
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UBCardinality() &&
    (forall key | key in Universe().Keys :: |key| <= UBSize_Keys())
  }

  ghost function Size():nat { Cardinality() * UBSize_Keys() }
  ghost function UBSize():nat { UBCardinality() * UBSize_Keys() }
  ghost function UBSize_Keys():nat
  ghost function UBCardinality():nat { |Universe()| }

  ghost function Cardinality():(cardinality:nat)
    ensures 0 <= cardinality
  { |Model()| }

  method Get(key:Map<T0, T1>, ghost counter_in:nat) returns (value:T2, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_MapMapTGet(this)
    ensures counter_out <= counter_in + cost_MapMapTGetUniverse(this)

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
    ensures if key.Size() <= UBSize_Keys()
            then result.UBSize_Keys() == UBSize_Keys()
            else result.UBSize_Keys() == key.Size()
    ensures result.UBSize_Keys() == UBSize_Keys() ||
            result.UBSize_Keys() == key.Size()
    ensures counter_out == counter_in + cost_MapMapTInsert(this)
    ensures counter_out <= counter_in + cost_MapMapTInsertUniverse(this)

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
    ensures counter_out == counter_in + cost_MapMapTRemove(this)
    ensures counter_out <= counter_in + cost_MapMapTRemoveUniverse(this)

  method PickKey(ghost counter_in:nat) returns (key:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    requires Model() != map[]
    ensures key.Valid()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures key.Size() <= UBSize_Keys()
    ensures key.UBSize() <= UBSize_Keys()
    ensures counter_out == counter_in + cost_MapMapTPickKey(this, key)
    ensures counter_out <= counter_in + cost_MapMapTPickKeyUniverse(this)

  method nPairs(ghost counter_in:nat) returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_MapMapTNPairs(this)

  method ContainsKey(key:Map<T0, T1>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + cost_MapMapTContainsKey(this)
    ensures counter_out <= counter_in + cost_MapMapTContainsKeyUniverse(this)

  method Empty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + cost_MapMapTEmpty(this)

  method Copy(ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures result.UBSize_Keys() == UBSize_Keys()
    ensures counter_out == counter_in + cost_MapMapTCopy(this)
    ensures counter_out <= counter_in + cost_MapMapTCopyUniverse(this)
}


lemma MapModelSizeBound<K, V>(M:Map<K, V>)
  requires M.Valid()
  ensures M.Size() <= M.UBSize()
{}

lemma MapMapTModelSizeBound<K, V, R>(M:Map_Map_T<K, V, R>)
  requires M.Valid()
  ensures M.Size() <= M.UBSize()
{
  map_nat_multiply_right_mono(M.Cardinality(), M.UBCardinality(), M.UBSize_Keys());
}

lemma map_nat_multiply_right_mono(a:nat, b:nat, factor:nat)
  requires a <= b
  ensures a * factor <= b * factor
{}


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


ghost function cost_MapGet<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function cost_MapGetUniverse<K, V>(M:Map<K, V>):nat { M.UBSize() + 1 }
ghost function cost_MapInsert<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function cost_MapInsertUniverse<K, V>(M:Map<K, V>):nat { M.UBSize() + 1 }
ghost function cost_MapRemove<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function cost_MapRemoveUniverse<K, V>(M:Map<K, V>):nat { M.UBSize() + 1 }
ghost function cost_MapPickKey<K, V>(M:Map<K, V>):nat { 1 }
ghost function cost_MapNPairs<K, V>(M:Map<K, V>):nat { 1 }
ghost function cost_MapContainsKey<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function cost_MapContainsKeyUniverse<K, V>(M:Map<K, V>):nat { M.UBSize() + 1 }
ghost function cost_MapEmpty<K, V>(M:Map<K, V>):nat { 1 }
ghost function cost_MapCopy<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function cost_MapCopyUniverse<K, V>(M:Map<K, V>):nat { M.UBSize() + 1 }
ghost function cost_NewMap():nat { 1 }

ghost function cost_MapMapTGet<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function cost_MapMapTGetUniverse<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.UBSize() + 1 }
ghost function cost_MapMapTInsert<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function cost_MapMapTInsertUniverse<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.UBSize() + 1 }
ghost function cost_MapMapTRemove<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function cost_MapMapTRemoveUniverse<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.UBSize() + 1 }
ghost function cost_MapMapTPickKey<K, V, R>(M:Map_Map_T<K, V, R>, key:Map<K, V>):nat
{ key.Size() + 1 }
ghost function cost_MapMapTPickKeyUniverse<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.UBSize_Keys() + 1 }
ghost function cost_MapMapTNPairs<K, V, R>(M:Map_Map_T<K, V, R>):nat { 1 }
ghost function cost_MapMapTContainsKey<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.Size() + 1 }
ghost function cost_MapMapTContainsKeyUniverse<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.UBSize() + 1 }
ghost function cost_MapMapTEmpty<K, V, R>(M:Map_Map_T<K, V, R>):nat { 1 }
ghost function cost_MapMapTCopy<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function cost_MapMapTCopyUniverse<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.UBSize() + 1 }
ghost function cost_NewMapMapT():nat { 1 }
