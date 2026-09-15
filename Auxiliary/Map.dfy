include "Set.dfy"

/*
Abstract interfaces for immutable maps

Concrete implementations are defined in ConcreteMap.dfy.
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
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures counter_out == counter_in + cost_MapInsert(this)
    ensures counter_out <= counter_in + cost_MapInsertUniverse(this)

  method Remove(key:T0, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures if key in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key}
    ensures counter_out == counter_in + cost_MapRemove(this)
    ensures counter_out <= counter_in + cost_MapRemoveUniverse(this)

  method PickKey(ghost counter_in:nat) returns (key:T0, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + cost_MapPickKey(this)

  method nPairs(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
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
// Maximum key cardinality; the empty family has size zero.
ghost function {:opaque} MaxMapCardinality<K, V>(maps:set<map<K, V>>):(size:nat)
  ensures maps == {} ==> size == 0
  decreases |maps|
{
  if maps == {} then 0 else
    var m :| m in maps;
    var rest := MaxMapCardinality(maps - {m});
    if |m| > rest then |m| else rest
}

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

  ghost function Size_Keys():nat { MaxMapCardinality(Model().Keys) }
  ghost function Size():nat { Cardinality() * Size_Keys() }
  ghost function UBSize():nat { UBCardinality() * UBSize_Keys() }
  ghost function {:opaque} UBSize_Keys():nat { MaxMapCardinality(Universe().Keys) }
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
    ensures result.Cardinality() <= Cardinality() + 1
    ensures if key.Size() <= UBSize_Keys()
            then result.UBSize_Keys() == UBSize_Keys()
            else result.UBSize_Keys() == key.Size()
    ensures result.UBSize_Keys() == UBSize_Keys() ||
            result.UBSize_Keys() == key.Size()
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.Keys() == Keys() + {key.Model()}
    ensures counter_out == counter_in + cost_MapMapTInsert(this)
    ensures counter_out <= counter_in + cost_MapMapTInsertUniverse(this)

  method Remove(key:Map<T0, T1>, ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UBSize_Keys() <= UBSize_Keys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + cost_MapMapTRemove(this)
    ensures counter_out <= counter_in + cost_MapMapTRemoveUniverse(this)

  method PickKey(ghost counter_in:nat) returns (key:Map<T0, T1>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= UBSize_Keys()
    ensures key.UBSize() <= UBSize_Keys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + cost_MapMapTPickKey(this, key)
    ensures counter_out <= counter_in + cost_MapMapTPickKeyUniverse(this)

  method nPairs(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
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
    ensures result.UBSize_Keys() == Size_Keys()
    ensures result.UBSize_Keys() <= UBSize_Keys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + cost_MapMapTCopy(this)
    ensures counter_out <= counter_in + cost_MapMapTCopyUniverse(this)
}


// Maps whose keys are sets
trait Map_Set_T<K(==), V(==)> {
  function Repr():map<set<K>, V>
  ghost function {:opaque} Model():map<set<K>, V> { Repr() }
  ghost function Universe():map<set<K>, V>
  ghost function Cardinality():nat { |Model()| }
  ghost function UBCardinality():nat { |Universe()| }
  ghost function UBSize_Keys():nat
  ghost function Size():nat { Cardinality() * UBSize_Keys() }
  ghost function UBSize():nat { UBCardinality() * UBSize_Keys() }
  ghost predicate {:opaque} Valid() {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UBCardinality() &&
    (forall key | key in Universe().Keys :: |key| <= UBSize_Keys())
  }

  method Get(key:Set<K>, ghost counter_in:nat) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_MapSetTGet(this)
    ensures counter_out <= counter_in + cost_MapSetTGetUniverse(this)

  method ContainsKey(key:Set<K>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + cost_MapSetTContainsKey(this)
    ensures counter_out <= counter_in + cost_MapSetTContainsKeyUniverse(this)

  method Insert(key:Set<K>, value:V, ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UBSize_Keys() == (if key.Size0() <= UBSize_Keys() then UBSize_Keys() else key.Size0())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + cost_MapSetTInsert(this)
    ensures counter_out <= counter_in + cost_MapSetTInsertUniverse(this)

}


// Maps whose keys are maps whose keys are sets
trait Map_MapSet_T<K(==), V(==), R(==)> {
  function Repr():map<map<set<K>, V>, R>
  ghost function {:opaque} Model():map<map<set<K>, V>, R> { Repr() }
  ghost function Universe():map<map<set<K>, V>, R>
  ghost function Cardinality():nat { |Model()| }
  ghost function UBCardinality():nat { |Universe()| }
  ghost function UBSize_Keys():nat
  ghost function UBSize_Keys_Keys():nat
  ghost function Size():nat { Cardinality() * UBSize_Keys() * UBSize_Keys_Keys() }
  ghost function UBSize():nat { UBCardinality() * UBSize_Keys() * UBSize_Keys_Keys() }
  ghost predicate {:opaque} Valid() {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UBCardinality() &&
    (forall key | key in Universe().Keys :: |key| <= UBSize_Keys()) &&
    (forall key | key in Universe().Keys :: forall question | question in key.Keys ::
      |question| <= UBSize_Keys_Keys())
  }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_MapMapSetTGet(this)
    ensures counter_out <= counter_in + cost_MapMapSetTGetUniverse(this)

  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + cost_MapMapSetTContainsKey(this)
    ensures counter_out <= counter_in + cost_MapMapSetTContainsKeyUniverse(this)

  method Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UBSize_Keys() == (if key.Cardinality() <= UBSize_Keys() then UBSize_Keys() else key.Cardinality())
    ensures result.UBSize_Keys_Keys() == (if key.UBSize_Keys() <= UBSize_Keys_Keys() then UBSize_Keys_Keys() else key.UBSize_Keys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + cost_MapMapSetTInsert(this)
    ensures counter_out <= counter_in + cost_MapMapSetTInsertUniverse(this)

}


ghost predicate init_Map(M:Map)
{
  M.Valid() && M.Model() == M.Universe()
}

ghost predicate init_Map_Map_T(M:Map_Map_T)
{
  M.Valid() && M.Model() == M.Universe()
}

ghost predicate init_Map_Set_T(M:Map_Set_T)
{
  M.Valid() && M.Model() == M.Universe()
}

ghost predicate init_Map_MapSet_T(M:Map_MapSet_T)
{
  M.Valid() && M.Model() == M.Universe()
}


ghost predicate in_universe_Map(M:Map, U:Map)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
}

ghost predicate in_universe_Map_Map_T(M:Map_Map_T, U:Map_Map_T)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  M.UBSize_Keys() <= U.UBSize_Keys() &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
}

ghost predicate in_universe_Map_Set_T(M:Map_Set_T, U:Map_Set_T)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  M.UBSize_Keys() <= U.UBSize_Keys() &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
}

ghost predicate in_universe_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  M.UBSize_Keys() <= U.UBSize_Keys() &&
  M.UBSize_Keys_Keys() <= U.UBSize_Keys_Keys() &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
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


ghost function cost_MapSetTGet<K, V>(M:Map_Set_T<K, V>):nat { M.Size() + 1 }
ghost function cost_MapSetTGetUniverse<K, V>(M:Map_Set_T<K, V>):nat { M.UBSize() + 1 }

ghost function cost_MapSetTContainsKey<K, V>(M:Map_Set_T<K, V>):nat { M.Size() + 1 }
ghost function cost_MapSetTContainsKeyUniverse<K, V>(M:Map_Set_T<K, V>):nat { M.UBSize() + 1 }

ghost function cost_MapSetTInsert<K, V>(M:Map_Set_T<K, V>):nat { M.Size() + 1 }
ghost function cost_MapSetTInsertUniverse<K, V>(M:Map_Set_T<K, V>):nat { M.UBSize() + 1 }

ghost function cost_NewMapSetT():nat { 1 }


ghost function cost_MapMapSetTGet<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.Size() + 1 }
ghost function cost_MapMapSetTGetUniverse<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.UBSize() + 1 }

ghost function cost_MapMapSetTContainsKey<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.Size() + 1 }
ghost function cost_MapMapSetTContainsKeyUniverse<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.UBSize() + 1 }

ghost function cost_MapMapSetTInsert<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.Size() + 1 }
ghost function cost_MapMapSetTInsertUniverse<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.UBSize() + 1 }

ghost function cost_NewMapMapSetT():nat { 1 }
