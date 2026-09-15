include "Map.dfy"
include "Lemmas.dfy"


class ConcreteMap<K(==), V(==)> extends Map<K, V> {
  const entries:map<K, V>
  ghost const universe:map<K, V>

  constructor(entries_in:map<K, V>, ghost universe_in:map<K, V>)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in entries_in.Keys ::
      entries_in[key] == universe_in[key]
    ensures Valid()
    ensures Model() == entries_in
    ensures Universe() == universe_in
  {
    entries := entries_in;
    universe := universe_in;
    reveal Model();
    if_smaller_then_less_cardinality(entries_in.Keys, universe_in.Keys);
  }

  function Repr():map<K, V> { entries }
  ghost function Universe():map<K, V> { universe }

  method Get(key:K, ghost counter_in:nat)
      returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + cost_MapGet(this)
    ensures counter_out <= counter_in + cost_MapGetUniverse(this)
  {
    reveal Model();
    MapModelSizeBound(this);
    value := entries[key];
    counter_out := counter_in + cost_MapGet(this);
  }

  method Insert(key:K, value:V, ghost counter_in:nat)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures counter_out == counter_in + cost_MapInsert(this)
    ensures counter_out <= counter_in + cost_MapInsertUniverse(this)
  {
    reveal Model();
    MapModelSizeBound(this);
    reveal Valid();
    result := new ConcreteMap(entries[key := value], universe[key := value]);
    counter_out := counter_in + cost_MapInsert(this);
  }

  method Remove(key:K, ghost counter_in:nat)
      returns (result:Map<K, V>, ghost counter_out:nat)
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
  {
    reveal Model();
    MapModelSizeBound(this);
    reveal Valid();
    result := new ConcreteMap(entries - {key}, universe);
    counter_out := counter_in + cost_MapRemove(this);
  }

  method PickKey(ghost counter_in:nat)
      returns (key:K, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + cost_MapPickKey(this)
  {
    reveal Model();
    reveal Valid();
    key :| key in entries.Keys;
    counter_out := counter_in + cost_MapPickKey(this);
  }

  method nPairs(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_MapNPairs(this)
  {
    reveal Model();
    size := |entries|;
    counter_out := counter_in + cost_MapNPairs(this);
  }

  method ContainsKey(key:K, ghost counter_in:nat)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + cost_MapContainsKey(this)
    ensures counter_out <= counter_in + cost_MapContainsKeyUniverse(this)
  {
    reveal Model();
    MapModelSizeBound(this);
    contains := key in entries;
    counter_out := counter_in + cost_MapContainsKey(this);
  }

  method Empty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + cost_MapEmpty(this)
  {
    reveal Model();
    empty := entries == map[];
    counter_out := counter_in + cost_MapEmpty(this);
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + cost_MapCopy(this)
    ensures counter_out <= counter_in + cost_MapCopyUniverse(this)
  {
    reveal Model();
    MapModelSizeBound(this);
    result := new ConcreteMap(entries, entries);
    counter_out := counter_in + cost_MapCopy(this);
  }
}


class ConcreteMapMapT<K(==), V(==), R(==)> extends Map_Map_T<K, V, R> {
  const entries:map<map<K, V>, R>
  ghost const universe:map<map<K, V>, R>

  constructor(entries_in:map<map<K, V>, R>, ghost universe_in:map<map<K, V>, R>)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in entries_in.Keys ::
      entries_in[key] == universe_in[key]
    ensures Valid()
    ensures Model() == entries_in
    ensures Universe() == universe_in
  {
    entries := entries_in;
    universe := universe_in;
    reveal Model();
    reveal UBSize_Keys();
    if_smaller_then_less_cardinality(entries_in.Keys, universe_in.Keys);
    MaxMapCardinalityProperties(universe_in.Keys);
  }

  function Repr():map<map<K, V>, R> { entries }
  ghost function Universe():map<map<K, V>, R> { universe }

  method Get(key:Map<K, V>, ghost counter_in:nat)
      returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_MapMapTGet(this)
    ensures counter_out <= counter_in + cost_MapMapTGetUniverse(this)
  {
    reveal Model();
    reveal UBSize_Keys();
    MapMapTModelSizeBound(this);
    reveal key.Model();
    var concrete_key := key.Repr();
    value := entries[concrete_key];
    counter_out := counter_in + cost_MapMapTGet(this);
  }

  method Insert(key:Map<K, V>, value:R, ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
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
  {
    reveal Model();
    reveal UBSize_Keys();
    MapMapTModelSizeBound(this);
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.Repr();
    assert key.Size() == |concrete_key|;
    assert (universe[concrete_key := value]).Keys == universe.Keys + {concrete_key};
    MaxMapCardinalityInsert(universe.Keys, concrete_key);
    result := new ConcreteMapMapT(
      entries[concrete_key := value],
      universe[concrete_key := value]);
    reveal result.UBSize_Keys();
    counter_out := counter_in + cost_MapMapTInsert(this);
  }

  method Remove(key:Map<K, V>, ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
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
  {
    reveal Model();
    reveal UBSize_Keys();
    MapMapTModelSizeBound(this);
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.Repr();
    result := new ConcreteMapMapT(entries - {concrete_key}, universe);
    reveal result.UBSize_Keys();
    counter_out := counter_in + cost_MapMapTRemove(this);
  }

  method PickKey(ghost counter_in:nat)
      returns (key:Map<K, V>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= UBSize_Keys()
    ensures key.UBSize() <= UBSize_Keys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + cost_MapMapTPickKey(this, key)
    ensures counter_out <= counter_in + cost_MapMapTPickKeyUniverse(this)
  {
    reveal Model();
    reveal UBSize_Keys();
    reveal Valid();
    var chosen:map<K, V> :| chosen in entries.Keys;
    MaxMapCardinalityMember(universe.Keys, chosen);
    key := new ConcreteMap(chosen, chosen);
    counter_out := counter_in + cost_MapMapTPickKey(this, key);
  }

  method nPairs(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_MapMapTNPairs(this)
  {
    reveal Model();
    reveal UBSize_Keys();
    size := |entries|;
    counter_out := counter_in + cost_MapMapTNPairs(this);
  }

  method ContainsKey(key:Map<K, V>, ghost counter_in:nat)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + cost_MapMapTContainsKey(this)
    ensures counter_out <= counter_in + cost_MapMapTContainsKeyUniverse(this)
  {
    reveal Model();
    reveal UBSize_Keys();
    MapMapTModelSizeBound(this);
    reveal key.Model();
    var concrete_key := key.Repr();
    contains := concrete_key in entries;
    counter_out := counter_in + cost_MapMapTContainsKey(this);
  }

  method Empty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + cost_MapMapTEmpty(this)
  {
    reveal Model();
    reveal UBSize_Keys();
    empty := entries == map[];
    counter_out := counter_in + cost_MapMapTEmpty(this);
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UBSize_Keys() == Size_Keys()
    ensures result.UBSize_Keys() <= UBSize_Keys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + cost_MapMapTCopy(this)
    ensures counter_out <= counter_in + cost_MapMapTCopyUniverse(this)
  {
    reveal Model();
    reveal UBSize_Keys();
    MapMapTModelSizeBound(this);
    reveal Valid();
    result := new ConcreteMapMapT(entries, entries);
    reveal result.UBSize_Keys();
    counter_out := counter_in + cost_MapMapTCopy(this);
  }
}


method New_Map<K(==), V(==)>(ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures counter_out == counter_in + cost_NewMap()
{
  result := new ConcreteMap(map[], map[]);
  counter_out := counter_in + cost_NewMap();
}

method New_Map_params<K(==), V(==)>(ghost universe:map<K, V>, ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures counter_out == counter_in + cost_NewMap()
{
  result := new ConcreteMap(map[], universe);
  counter_out := counter_in + cost_NewMap();
}

method New_Map_Map_T<K(==), V(==), R(==)>(ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  ensures result.UBSize_Keys() == 0
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures counter_out == counter_in + cost_NewMapMapT()
{
  result := new ConcreteMapMapT(map[], map[]);
  reveal result.UBSize_Keys();
  counter_out := counter_in + cost_NewMapMapT();
}

method New_Map_Map_T_params<K(==), V(==), R(==)>(ghost universe:map<map<K, V>, R>, ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures counter_out == counter_in + cost_NewMapMapT()
{
  result := new ConcreteMapMapT(map[], universe);
  counter_out := counter_in + cost_NewMapMapT();
}


class ConcreteMapSetT<K(==), V(==)> extends Map_Set_T<K, V> {
  const entries:map<set<K>, V>
  ghost const universe:map<set<K>, V>
  ghost const ub_size_keys:nat

  constructor(entries_in:map<set<K>, V>, ghost universe_in:map<set<K>, V>, ghost ub_size_keys_in:nat)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in universe_in.Keys :: |key| <= ub_size_keys_in
    requires forall key | key in entries_in.Keys :: entries_in[key] == universe_in[key]
    ensures Valid()
    ensures UBSize_Keys() == ub_size_keys_in
    ensures Model() == entries_in && Universe() == universe_in
  {
    entries := entries_in;
    universe := universe_in;
    ub_size_keys := ub_size_keys_in;
    reveal Model(), Valid();
    if_smaller_then_less_cardinality(entries_in.Keys, universe_in.Keys);
  }

  function Repr():map<set<K>, V> { entries }
  ghost function Universe():map<set<K>, V> { universe }
  ghost function UBSize_Keys():nat { ub_size_keys }

  method Get(key:Set<K>, ghost counter_in:nat) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_MapSetTGet(this)
    ensures counter_out <= counter_in + cost_MapSetTGetUniverse(this)
  {
    reveal Model(), key.Model();
    MapSetTModelSizeBound(this);
    value := entries[key.Repr()];
    counter_out := counter_in + cost_MapSetTGet(this);
  }

  method ContainsKey(key:Set<K>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + cost_MapSetTContainsKey(this)
    ensures counter_out <= counter_in + cost_MapSetTContainsKeyUniverse(this)
  {
    reveal Model(), key.Model();
    MapSetTModelSizeBound(this);
    contains := key.Repr() in entries;
    counter_out := counter_in + cost_MapSetTContainsKey(this);
  }

  method Insert(key:Set<K>, value:V, ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UBSize_Keys() == (if key.Size0() <= UBSize_Keys() then UBSize_Keys() else key.Size0())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + cost_MapSetTInsert(this)
    ensures counter_out <= counter_in + cost_MapSetTInsertUniverse(this)
  {
    reveal Model(), key.Model();
    MapSetTModelSizeBound(this);
    reveal Valid(), key.Valid();
    var concrete_key := key.Repr();
    ghost var bound := if key.Size0() <= UBSize_Keys() then UBSize_Keys() else key.Size0();
    result := new ConcreteMapSetT(entries[concrete_key := value], universe[concrete_key := value], bound);
    counter_out := counter_in + cost_MapSetTInsert(this);
  }

}

method New_Map_Set_T<K(==), V(==)>(ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
  ensures init_Map_Set_T(result)
  ensures result.UBSize_Keys() == 0
  ensures result.Model() == map[] && result.Universe() == map[]
  ensures counter_out == counter_in + cost_NewMapSetT()
{
  result := new ConcreteMapSetT(map[], map[], 0);
  counter_out := counter_in + cost_NewMapSetT();
}

class ConcreteMapMapSetT<K(==), V(==), R(==)> extends Map_MapSet_T<K, V, R> {
  const entries:map<map<set<K>, V>, R>
  ghost const universe:map<map<set<K>, V>, R>
  ghost const ub_size_keys:nat
  ghost const ub_size_keys_keys:nat

  constructor(entries_in:map<map<set<K>, V>, R>, ghost universe_in:map<map<set<K>, V>, R>, ghost ub_size_keys_in:nat, ghost ub_size_keys_keys_in:nat)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in universe_in.Keys :: |key| <= ub_size_keys_in
    requires forall key | key in universe_in.Keys :: forall question | question in key.Keys ::
      |question| <= ub_size_keys_keys_in
    requires forall key | key in entries_in.Keys :: entries_in[key] == universe_in[key]
    ensures Valid()
    ensures UBSize_Keys() == ub_size_keys_in
    ensures UBSize_Keys_Keys() == ub_size_keys_keys_in
    ensures Model() == entries_in && Universe() == universe_in
  {
    entries := entries_in;
    universe := universe_in;
    ub_size_keys := ub_size_keys_in;
    ub_size_keys_keys := ub_size_keys_keys_in;
    reveal Model(), Valid();
    if_smaller_then_less_cardinality(entries_in.Keys, universe_in.Keys);
  }

  function Repr():map<map<set<K>, V>, R> { entries }
  ghost function Universe():map<map<set<K>, V>, R> { universe }
  ghost function UBSize_Keys():nat { ub_size_keys }
  ghost function UBSize_Keys_Keys():nat { ub_size_keys_keys }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_MapMapSetTGet(this)
    ensures counter_out <= counter_in + cost_MapMapSetTGetUniverse(this)
  {
    reveal Model(), key.Model();
    MapMapSetTModelSizeBound(this);
    value := entries[key.Repr()];
    counter_out := counter_in + cost_MapMapSetTGet(this);
  }

  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + cost_MapMapSetTContainsKey(this)
    ensures counter_out <= counter_in + cost_MapMapSetTContainsKeyUniverse(this)
  {
    reveal Model(), key.Model();
    MapMapSetTModelSizeBound(this);
    contains := key.Repr() in entries;
    counter_out := counter_in + cost_MapMapSetTContainsKey(this);
  }

  method {:isolate_assertions} Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UBSize_Keys() == (if key.Cardinality() <= UBSize_Keys() then UBSize_Keys() else key.Cardinality())
    ensures result.UBSize_Keys_Keys() == (if key.UBSize_Keys() <= UBSize_Keys_Keys() then UBSize_Keys_Keys() else key.UBSize_Keys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + cost_MapMapSetTInsert(this)
    ensures counter_out <= counter_in + cost_MapMapSetTInsertUniverse(this)
  {
    reveal Model(), key.Model();
    MapMapSetTModelSizeBound(this);
    reveal Valid(), key.Valid();
    var concrete_key := key.Repr();
    ghost var bound := if key.Cardinality() <= UBSize_Keys() then UBSize_Keys() else key.Cardinality();
    ghost var nestedBound := if key.UBSize_Keys() <= UBSize_Keys_Keys() then UBSize_Keys_Keys() else key.UBSize_Keys();
    forall candidate | candidate in universe[concrete_key := value].Keys
      ensures |candidate| <= bound
      ensures forall question | question in candidate.Keys :: |question| <= nestedBound
    {
      if candidate == concrete_key {
        assert key.Model().Keys <= key.Universe().Keys;
      } else {
        assert candidate in universe.Keys;
      }
    }
    var updatedEntries := entries[concrete_key := value];
    ghost var updatedUniverse := universe[concrete_key := value];
    ghost var agreedEntries, agreedUniverse := MapUpdatePreservesUniverse(entries, universe, concrete_key, value);
    result := new ConcreteMapMapSetT(updatedEntries, updatedUniverse, bound, nestedBound);
    counter_out := counter_in + cost_MapMapSetTInsert(this);
  }

}

method New_Map_MapSet_T<K(==), V(==), R(==)>(ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
  ensures init_Map_MapSet_T(result)
  ensures result.UBSize_Keys() == 0
  ensures result.UBSize_Keys_Keys() == 0
  ensures result.Model() == map[] && result.Universe() == map[]
  ensures counter_out == counter_in + cost_NewMapMapSetT()
{
  result := new ConcreteMapMapSetT(map[], map[], 0, 0);
  counter_out := counter_in + cost_NewMapMapSetT();
}
