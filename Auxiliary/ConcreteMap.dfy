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
    SubsetCardinalityBound(entries_in.Keys, universe_in.Keys);
  }

  function Repr():map<K, V> { entries }
  ghost function Universe():map<K, V> { universe }

  method Get(key:K, ghost counter_in:nat)
      returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + CostGet_Map(this)
    ensures counter_out <= counter_in + UCostGet_Map(this)
  {
    reveal Model();
    ModelSizeBound_Map(this);
    value := entries[key];
    counter_out := counter_in + CostGet_Map(this);
  }

  method Insert(key:K, value:V, ghost counter_in:nat)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures counter_out == counter_in + CostInsert_Map(this)
    ensures counter_out <= counter_in + UCostInsert_Map(this)
  {
    reveal Model();
    ModelSizeBound_Map(this);
    reveal Valid();
    result := new ConcreteMap(entries[key := value], universe[key := value]);
    counter_out := counter_in + CostInsert_Map(this);
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
    ensures counter_out == counter_in + CostRemove_Map(this)
    ensures counter_out <= counter_in + UCostRemove_Map(this)
  {
    reveal Model();
    ModelSizeBound_Map(this);
    reveal Valid();
    result := new ConcreteMap(entries - {key}, universe);
    counter_out := counter_in + CostRemove_Map(this);
  }

  method PickKey(ghost counter_in:nat)
      returns (key:K, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + CostPickKey_Map(this)
  {
    reveal Model();
    reveal Valid();
    key :| key in entries.Keys;
    counter_out := counter_in + CostPickKey_Map(this);
  }

  method Count(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_Map(this)
  {
    reveal Model();
    size := |entries|;
    counter_out := counter_in + CostCount_Map(this);
  }

  method ContainsKey(key:K, ghost counter_in:nat)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map(this)
  {
    reveal Model();
    ModelSizeBound_Map(this);
    contains := key in entries;
    counter_out := counter_in + CostContainsKey_Map(this);
  }

  method IsEmpty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty_Map(this)
  {
    reveal Model();
    empty := entries == map[];
    counter_out := counter_in + CostIsEmpty_Map(this);
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_Map(this)
    ensures counter_out <= counter_in + UCostCopy_Map(this)
  {
    reveal Model();
    ModelSizeBound_Map(this);
    result := new ConcreteMap(entries, entries);
    counter_out := counter_in + CostCopy_Map(this);
  }
}


class ConcreteMap_Map_T<K(==), V(==), R(==)> extends Map_Map_T<K, V, R> {
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
    reveal USize_Keys();
    SubsetCardinalityBound(entries_in.Keys, universe_in.Keys);
    MaxCardinalityProperties_map(universe_in.Keys);
  }

  function Repr():map<map<K, V>, R> { entries }
  ghost function Universe():map<map<K, V>, R> { universe }

  method Get(key:Map<K, V>, ghost counter_in:nat)
      returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostGet_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    ModelSizeBound_Map_Map_T(this);
    reveal key.Model();
    var concrete_key := key.Repr();
    value := entries[concrete_key];
    counter_out := counter_in + CostGet_Map_Map_T(this);
  }

  method Insert(key:Map<K, V>, value:R, ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    requires key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures if key.Size() <= USize_Keys()
            then result.USize_Keys() == USize_Keys()
            else result.USize_Keys() == key.Size()
    ensures result.USize_Keys() == USize_Keys() ||
            result.USize_Keys() == key.Size()
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.Keys() == Keys() + {key.Model()}
    ensures counter_out == counter_in + CostInsert_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostInsert_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    ModelSizeBound_Map_Map_T(this);
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.Repr();
    result := new ConcreteMap_Map_T(
      entries[concrete_key := value],
      universe[concrete_key := value]);
    InsertUniverseMeasures_Map_Map_T(this, result, key, value);
    counter_out := counter_in + CostInsert_Map_Map_T(this);
  }

  method Remove(key:Map<K, V>, ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.USize_Keys() <= USize_Keys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + CostRemove_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostRemove_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    ModelSizeBound_Map_Map_T(this);
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.Repr();
    result := new ConcreteMap_Map_T(entries - {concrete_key}, universe);
    reveal result.USize_Keys();
    counter_out := counter_in + CostRemove_Map_Map_T(this);
  }

  method PickKey(ghost counter_in:nat)
      returns (key:Map<K, V>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= USize_Keys()
    ensures key.USize() <= USize_Keys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + CostPickKey_Map_Map_T(this, key)
    ensures counter_out <= counter_in + UCostPickKey_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    reveal Valid();
    var chosen:map<K, V> :| chosen in entries.Keys;
    MaxCardinalityMember_map(universe.Keys, chosen);
    key := new ConcreteMap(chosen, chosen);
    counter_out := counter_in + CostPickKey_Map_Map_T(this, key);
  }

  method Count(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    size := |entries|;
    counter_out := counter_in + CostCount_Map_Map_T(this);
  }

  method ContainsKey(key:Map<K, V>, ghost counter_in:nat)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    ModelSizeBound_Map_Map_T(this);
    reveal key.Model();
    var concrete_key := key.Repr();
    contains := concrete_key in entries;
    counter_out := counter_in + CostContainsKey_Map_Map_T(this);
  }

  method IsEmpty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    empty := entries == map[];
    counter_out := counter_in + CostIsEmpty_Map_Map_T(this);
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.USize_Keys() == Size_Keys()
    ensures result.USize_Keys() <= USize_Keys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostCopy_Map_Map_T(this)
  {
    reveal Model();
    reveal USize_Keys();
    ModelSizeBound_Map_Map_T(this);
    reveal Valid();
    result := new ConcreteMap_Map_T(entries, entries);
    reveal result.USize_Keys();
    counter_out := counter_in + CostCopy_Map_Map_T(this);
  }
}


method New_Map<K(==), V(==)>(ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_Map()
{
  result := new ConcreteMap(map[], map[]);
  counter_out := counter_in + CostNew_Map();
}

method NewWithUniverse_Map<K(==), V(==)>(ghost universe:map<K, V>, ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures counter_out == counter_in + CostNew_Map()
{
  result := new ConcreteMap(map[], universe);
  counter_out := counter_in + CostNew_Map();
}

method New_Map_Map_T<K(==), V(==), R(==)>(ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  ensures result.USize_Keys() == 0
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_Map_Map_T()
{
  result := new ConcreteMap_Map_T(map[], map[]);
  reveal result.USize_Keys();
  counter_out := counter_in + CostNew_Map_Map_T();
}

method NewWithUniverse_Map_Map_T<K(==), V(==), R(==)>(ghost universe:map<map<K, V>, R>, ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures counter_out == counter_in + CostNew_Map_Map_T()
{
  result := new ConcreteMap_Map_T(map[], universe);
  counter_out := counter_in + CostNew_Map_Map_T();
}


class ConcreteMap_Set_T<K(==), V(==)> extends Map_Set_T<K, V> {
  const entries:map<set<K>, V>
  ghost const universe:map<set<K>, V>

  constructor(entries_in:map<set<K>, V>, ghost universe_in:map<set<K>, V>)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in entries_in.Keys :: entries_in[key] == universe_in[key]
    ensures Valid()
    ensures Model() == entries_in && Universe() == universe_in
  {
    entries := entries_in;
    universe := universe_in;
    reveal Model(), Valid(), USize_Keys();
    SubsetCardinalityBound(entries_in.Keys, universe_in.Keys);
    MaxCardinalityProperties_set(universe_in.Keys);
  }

  function Repr():map<set<K>, V> { entries }
  ghost function Universe():map<set<K>, V> { universe }

  method Get(key:Set<K>, ghost counter_in:nat) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet_Map_Set_T(this)
    ensures counter_out <= counter_in + UCostGet_Map_Set_T(this)
  {
    reveal Model(), key.Model();
    ModelSizeBound_Map_Set_T(this);
    value := entries[key.Repr()];
    counter_out := counter_in + CostGet_Map_Set_T(this);
  }

  method ContainsKey(key:Set<K>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map_Set_T(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map_Set_T(this)
  {
    reveal Model(), key.Model();
    ModelSizeBound_Map_Set_T(this);
    contains := key.Repr() in entries;
    counter_out := counter_in + CostContainsKey_Map_Set_T(this);
  }

  method Insert(key:Set<K>, value:V, ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.USize_Keys() == (if key.Size0() <= USize_Keys() then USize_Keys() else key.Size0())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert_Map_Set_T(this)
    ensures counter_out <= counter_in + UCostInsert_Map_Set_T(this)
  {
    reveal Model(), key.Model();
    ModelSizeBound_Map_Set_T(this);
    reveal Valid(), key.Valid();
    var concrete_key := key.Repr();
    result := new ConcreteMap_Set_T(entries[concrete_key := value], universe[concrete_key := value]);
    InsertUniverseMeasures_Map_Set_T(this, result, key, value);
    counter_out := counter_in + CostInsert_Map_Set_T(this);
  }

}

method New_Map_Set_T<K(==), V(==)>(ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
  ensures Init_Map_Set_T(result)
  ensures result.USize_Keys() == 0
  ensures result.Model() == map[] && result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_Map_Set_T()
{
  result := new ConcreteMap_Set_T(map[], map[]);
  reveal result.USize_Keys();
  counter_out := counter_in + CostNew_Map_Set_T();
}

class ConcreteMap_MapSet_T<K(==), V(==), R(==)> extends Map_MapSet_T<K, V, R> {
  const entries:map<map<set<K>, V>, R>
  ghost const universe:map<map<set<K>, V>, R>

  constructor(entries_in:map<map<set<K>, V>, R>, ghost universe_in:map<map<set<K>, V>, R>)
    requires entries_in.Keys <= universe_in.Keys
    requires forall key | key in entries_in.Keys :: entries_in[key] == universe_in[key]
    ensures Valid()
    ensures Model() == entries_in && Universe() == universe_in
  {
    entries := entries_in;
    universe := universe_in;
    reveal Model(), Valid(), USize_Keys(), USize_Keys_Keys();
    SubsetCardinalityBound(entries_in.Keys, universe_in.Keys);
    MaxCardinalityProperties_map(universe_in.Keys);
    MaxSetKeyCardinalityProperties_map_set_t(universe_in.Keys);
  }

  function Repr():map<map<set<K>, V>, R> { entries }
  ghost function Universe():map<map<set<K>, V>, R> { universe }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet_Map_MapSet_T(this)
    ensures counter_out <= counter_in + UCostGet_Map_MapSet_T(this)
  {
    reveal Model(), key.Model();
    ModelSizeBound_Map_MapSet_T(this);
    value := entries[key.Repr()];
    counter_out := counter_in + CostGet_Map_MapSet_T(this);
  }

  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map_MapSet_T(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map_MapSet_T(this)
  {
    reveal Model(), key.Model();
    ModelSizeBound_Map_MapSet_T(this);
    contains := key.Repr() in entries;
    counter_out := counter_in + CostContainsKey_Map_MapSet_T(this);
  }

  method {:isolate_assertions} Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.USize_Keys() == (if key.Cardinality() <= USize_Keys() then USize_Keys() else key.Cardinality())
    ensures result.USize_Keys_Keys() == (if key.Size_Keys() <= USize_Keys_Keys() then USize_Keys_Keys() else key.Size_Keys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert_Map_MapSet_T(this)
    ensures counter_out <= counter_in + UCostInsert_Map_MapSet_T(this)
  {
    reveal Model(), key.Model();
    ModelSizeBound_Map_MapSet_T(this);
    var concrete_key := key.Repr();
    var updatedEntries := entries[concrete_key := value];
    ghost var updatedUniverse := universe[concrete_key := value];
    UpdateAgreement_Map_MapSet_T(this, concrete_key, value);
    result := new ConcreteMap_MapSet_T(updatedEntries, updatedUniverse);
    assert result.Universe() == Universe()[key.Model() := value];
    InsertUniverseMeasures_Map_MapSet_T(this, result, key, value);
    counter_out := counter_in + CostInsert_Map_MapSet_T(this);
  }

}

method New_Map_MapSet_T<K(==), V(==), R(==)>(ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
  ensures Init_Map_MapSet_T(result)
  ensures result.USize_Keys() == 0
  ensures result.USize_Keys_Keys() == 0
  ensures result.Model() == map[] && result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_Map_MapSet_T()
{
  result := new ConcreteMap_MapSet_T(map[], map[]);
  reveal result.USize_Keys(), result.USize_Keys_Keys();
  counter_out := counter_in + CostNew_Map_MapSet_T();
}
