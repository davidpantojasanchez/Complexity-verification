include "Map.dfy"
include "Lemmas.dfy"


class ConcreteMap<K(==), V(==)> extends Map<K, V> {
  const entries:map<K, V>
  ghost const universe:map<K, V>

  constructor(entries_in:map<K, V>, ghost universe_in:map<K, V>)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in entries_in.Keys ::
      entries_in[key] == universe_in[key]
    ensures Model() == entries_in
    ensures Universe() == universe_in
    ensures Valid()
  {
    entries := entries_in;
    universe := universe_in;
    reveal Model();
    set_subset_cardinality(entries_in.Keys, universe_in.Keys);
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
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures if key in Keys()
            then result.Cardinality() == Cardinality()
            else result.Cardinality() == Cardinality() + 1
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
    ensures result.Model() == Model() - {key}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key}
    ensures if key in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
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
    requires Valid()
    requires Model() != map[]
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
      returns (size:int, ghost counter_out:nat)
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
  ghost const ub_size_keys:nat

  constructor(entries_in:map<map<K, V>, R>,
              ghost universe_in:map<map<K, V>, R>,
              ghost ub_size_keys_in:nat)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in entries_in.Keys ::
      entries_in[key] == universe_in[key]
    requires forall key | key in universe_in.Keys ::
      |key| <= ub_size_keys_in
    ensures Model() == entries_in
    ensures Universe() == universe_in
    ensures UBSize_Keys() == ub_size_keys_in
    ensures Valid()
  {
    entries := entries_in;
    universe := universe_in;
    ub_size_keys := ub_size_keys_in;
    reveal Model();
    set_subset_cardinality(entries_in.Keys, universe_in.Keys);
  }

  function Repr():map<map<K, V>, R> { entries }
  ghost function Universe():map<map<K, V>, R> { universe }
  ghost function UBSize_Keys():nat { ub_size_keys }

  method Get(key:Map<K, V>, ghost counter_in:nat)
      returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + cost_MapMapTGet(this)
    ensures counter_out <= counter_in + cost_MapMapTGetUniverse(this)
  {
    reveal Model();
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
  {
    reveal Model();
    MapMapTModelSizeBound(this);
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.Repr();
    ghost var new_ub_size_keys :=
      if key.Size() <= UBSize_Keys() then UBSize_Keys() else key.Size();
    result := new ConcreteMapMapT(
      entries[concrete_key := value],
      universe[concrete_key := value],
      new_ub_size_keys);
    counter_out := counter_in + cost_MapMapTInsert(this);
  }

  method Remove(key:Map<K, V>, ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
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
  {
    reveal Model();
    MapMapTModelSizeBound(this);
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.Repr();
    result := new ConcreteMapMapT(entries - {concrete_key}, universe, UBSize_Keys());
    counter_out := counter_in + cost_MapMapTRemove(this);
  }

  method PickKey(ghost counter_in:nat)
      returns (key:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    requires Model() != map[]
    ensures key.Valid()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures key.Size() <= UBSize_Keys()
    ensures key.UBSize() <= UBSize_Keys()
    ensures counter_out == counter_in + cost_MapMapTPickKey(this, key)
    ensures counter_out <= counter_in + cost_MapMapTPickKeyUniverse(this)
  {
    reveal Model();
    reveal Valid();
    var chosen:map<K, V> :| chosen in entries.Keys;
    key := new ConcreteMap(chosen, chosen);
    counter_out := counter_in + cost_MapMapTPickKey(this, key);
  }

  method nPairs(ghost counter_in:nat)
      returns (size:int, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + cost_MapMapTNPairs(this)
  {
    reveal Model();
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
    empty := entries == map[];
    counter_out := counter_in + cost_MapMapTEmpty(this);
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures result.UBSize_Keys() == UBSize_Keys()
    ensures counter_out == counter_in + cost_MapMapTCopy(this)
    ensures counter_out <= counter_in + cost_MapMapTCopyUniverse(this)
  {
    reveal Model();
    MapMapTModelSizeBound(this);
    reveal Valid();
    result := new ConcreteMapMapT(entries, entries, UBSize_Keys());
    counter_out := counter_in + cost_MapMapTCopy(this);
  }
}


method New_Map<K(==), V(==)>(ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures result.Valid()
  ensures counter_out == counter_in + cost_NewMap()
{
  result := new ConcreteMap(map[], map[]);
  counter_out := counter_in + cost_NewMap();
}

method New_Map_params<K(==), V(==)>(ghost universe:map<K, V>,
                                    ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures result.Valid()
  ensures counter_out == counter_in + cost_NewMap()
{
  result := new ConcreteMap(map[], universe);
  counter_out := counter_in + cost_NewMap();
}

method New_Map_Map_T<K(==), V(==), R(==)>(ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures result.UBSize_Keys() == 0
  ensures result.Valid()
  ensures counter_out == counter_in + cost_NewMapMapT()
{
  result := new ConcreteMapMapT(map[], map[], 0);
  counter_out := counter_in + cost_NewMapMapT();
}

method New_Map_Map_T_params<K(==), V(==), R(==)>(
    ghost universe:map<map<K, V>, R>, ghost ub_size_keys:nat,
    ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  requires forall key | key in universe.Keys :: |key| <= ub_size_keys
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures result.UBSize_Keys() == ub_size_keys
  ensures result.Valid()
  ensures counter_out == counter_in + cost_NewMapMapT()
{
  result := new ConcreteMapMapT(map[], universe, ub_size_keys);
  counter_out := counter_in + cost_NewMapMapT();
}


method MapSmokeTest() returns (ok:bool)
  ensures ok
{
  ghost var counter:nat := 0;
  var map0:Map<int, int>;
  map0, counter := New_Map(counter);
  var map1:Map<int, int>;
  map1, counter := map0.Insert(1, 10, counter);
  var value:int;
  value, counter := map1.Get(1, counter);
  assert value == 10;
  var contains:bool;
  contains, counter := map1.ContainsKey(1, counter);
  assert contains;
  var map2:Map<int, int>;
  map2, counter := map1.Copy(counter);
  map2, counter := map2.Remove(1, counter);
  var empty:bool;
  empty, counter := map2.Empty(counter);
  ok := value == 10 && contains && empty;
}


method MapMapTSmokeTest() returns (ok:bool)
  ensures ok
{
  ghost var counter:nat := 0;
  var key0:Map<int, bool>;
  key0, counter := New_Map(counter);
  var key1:Map<int, bool>;
  key1, counter := key0.Insert(1, true, counter);

  var outer0:Map_Map_T<int, bool, int>;
  outer0, counter := New_Map_Map_T(counter);
  var outer1:Map_Map_T<int, bool, int>;
  outer1, counter := outer0.Insert(key1, 7, counter);

  var equivalent_key:Map<int, bool>;
  equivalent_key, counter := key1.Copy(counter);
  var value:int;
  value, counter := outer1.Get(equivalent_key, counter);
  assert value == 7;

  var picked:Map<int, bool>;
  picked, counter := outer1.PickKey(counter);
  assert picked.Model() == key1.Model();

  var outer2:Map_Map_T<int, bool, int>;
  outer2, counter := outer1.Remove(equivalent_key, counter);
  var empty:bool;
  empty, counter := outer2.Empty(counter);
  ok := value == 7 && empty;
}
