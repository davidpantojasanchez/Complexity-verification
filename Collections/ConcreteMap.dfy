include "Map.dfy"
include "ConcreteSet.dfy"
include "../Lemmas/Lemmas.dfy"


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

  function ExecutableModel():map<K, V> { entries }
  ghost function Universe():map<K, V> { universe }

  method Get(key:K, ghost counter_in:nat)
      returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()
  {
    reveal Model();
    value := entries[key];
    counter_out := counter_in + CostGet();
  }

  method Insert(key:K, value:V, ghost counter_in:nat)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures counter_out == counter_in + CostInsert()
    ensures counter_out <= counter_in + UCostInsert()
  {
    reveal Model();
    reveal Valid();
    result := new ConcreteMap(entries[key := value], universe[key := value]);
    counter_out := counter_in + CostInsert();
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
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()
  {
    reveal Model();
    reveal Valid();
    result := new ConcreteMap(entries - {key}, universe);
    counter_out := counter_in + CostRemove();
  }

  method PickKey(ghost counter_in:nat)
      returns (key:K, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + CostPickKey()
  {
    reveal Model();
    reveal Valid();
    key :| key in entries.Keys;
    counter_out := counter_in + CostPickKey();
  }

  method Count(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  {
    reveal Model();
    size := |entries|;
    counter_out := counter_in + CostCount();
  }

  method ContainsKey(key:K, ghost counter_in:nat)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()
  {
    reveal Model();
    contains := key in entries;
    counter_out := counter_in + CostContainsKey();
  }

  method IsEmpty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()
  {
    reveal Model();
    empty := entries == map[];
    counter_out := counter_in + CostIsEmpty();
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()
  {
    reveal Model();
    result := new ConcreteMap(entries, entries);
    counter_out := counter_in + CostCopy();
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
    SubsetCardinalityBound(entries_in.Keys, universe_in.Keys);
    reveal UCardinalityKeys();
    MaxByMonotonic(entries_in.Keys, universe_in.Keys, item => |item|);
    MultiplicationPreservesOrder(|entries_in|, MaxCardinality_map(entries_in.Keys), |universe_in|, MaxCardinality_map(universe_in.Keys));
  }

  function ExecutableModel():map<map<K, V>, R> { entries }
  ghost function Universe():map<map<K, V>, R> { universe }

  method Get(key:Map<K, V>, ghost counter_in:nat)
      returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    value := entries[concrete_key];
    counter_out := counter_in + CostGet();
  }

  method Insert(key:Map<K, V>, value:R, ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    requires key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures if key.Size() <= UCardinalityKeys()
            then result.UCardinalityKeys() == UCardinalityKeys()
            else result.UCardinalityKeys() == key.Size()
    ensures result.UCardinalityKeys() == UCardinalityKeys() ||
            result.UCardinalityKeys() == key.Size()
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.Keys() == Keys() + {key.Model()}
    ensures counter_out == counter_in + CostInsert()
    ensures counter_out <= counter_in + UCostInsert()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Map_T(
      entries[concrete_key := value],
      universe[concrete_key := value]);
    InsertUniverseMeasures_Map_Map_T(this, result, key, value);
    counter_out := counter_in + CostInsert();
  }

  method Remove(key:Map<K, V>, ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Map_T(entries - {concrete_key}, universe);
    reveal result.UCardinalityKeys();
    counter_out := counter_in + CostRemove();
  }

  method PickKey(ghost counter_in:nat)
      returns (key:Map<K, V>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= UCardinalityKeys()
    ensures key.USize() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + CostPickKey(key)
    ensures counter_out <= counter_in + UCostPickKey()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    var chosen:map<K, V> :| chosen in entries.Keys;
    MaxByMember(universe.Keys, chosen, item => |item|);
    key := new ConcreteMap(chosen, chosen);
    counter_out := counter_in + CostPickKey(key);
  }

  method Count(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  {
    reveal Model();
    reveal UCardinalityKeys();
    size := |entries|;
    counter_out := counter_in + CostCount();
  }

  method ContainsKey(key:Map<K, V>, ghost counter_in:nat)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    contains := concrete_key in entries;
    counter_out := counter_in + CostContainsKey();
  }

  method IsEmpty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()
  {
    reveal Model();
    reveal UCardinalityKeys();
    empty := entries == map[];
    counter_out := counter_in + CostIsEmpty();
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    result := new ConcreteMap_Map_T(entries, entries);
    reveal result.UCardinalityKeys();
    counter_out := counter_in + CostCopy();
  }
}


method New_Map<K(==), V(==)>(ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_MapFamily()
{
  result := new ConcreteMap(map[], map[]);
  counter_out := counter_in + CostNew_MapFamily();
}

method NewWithUniverse_Map<K(==), V(==)>(ghost universe:map<K, V>, ghost counter_in:nat)
    returns (result:Map<K, V>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures counter_out == counter_in + CostNew_MapFamily()
{
  result := new ConcreteMap(map[], universe);
  counter_out := counter_in + CostNew_MapFamily();
}

method New_Map_Map_T<K(==), V(==), R(==)>(ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  ensures result.UCardinalityKeys() == 0
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_MapFamily()
{
  result := new ConcreteMap_Map_T(map[], map[]);
  reveal result.UCardinalityKeys();
  counter_out := counter_in + CostNew_MapFamily();
}

method NewWithUniverse_Map_Map_T<K(==), V(==), R(==)>(ghost universe:map<map<K, V>, R>, ghost counter_in:nat)
    returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
  ensures result.Valid()
  ensures result.Model() == map[]
  ensures result.Universe() == universe
  ensures counter_out == counter_in + CostNew_MapFamily()
{
  result := new ConcreteMap_Map_T(map[], universe);
  counter_out := counter_in + CostNew_MapFamily();
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
    reveal Model();
    SubsetCardinalityBound(entries_in.Keys, universe_in.Keys);
    reveal UCardinalityKeys();
    MaxByMonotonic(entries_in.Keys, universe_in.Keys, item => |item|);
    MultiplicationPreservesOrder(|entries_in|, MaxCardinality_set(entries_in.Keys), |universe_in|, MaxCardinality_set(universe_in.Keys));
  }

  function ExecutableModel():map<set<K>, V> { entries }
  ghost function Universe():map<set<K>, V> { universe }

  method Get(key:Set<K>, ghost counter_in:nat) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()
  {
    reveal Model(), key.Model();
    value := entries[key.ExecutableModel()];
    counter_out := counter_in + CostGet();
  }

  method ContainsKey(key:Set<K>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()
  {
    reveal Model(), key.Model();
    contains := key.ExecutableModel() in entries;
    counter_out := counter_in + CostContainsKey();
  }

  method Insert(key:Set<K>, value:V, ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Size() <= UCardinalityKeys() then UCardinalityKeys() else key.Size())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert()
    ensures counter_out <= counter_in + UCostInsert()
  {
    reveal Model(), key.Model();
    reveal Valid(), key.Valid();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Set_T(entries[concrete_key := value], universe[concrete_key := value]);
    InsertUniverseMeasures_Map_Set_T(this, result, key, value);
    counter_out := counter_in + CostInsert();
  }

  method Remove(key:Set<K>, ghost counter_in:nat)
      returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Set_T(entries - {concrete_key}, universe);
    reveal result.UCardinalityKeys();
    counter_out := counter_in + CostRemove();
  }

  method PickKey(ghost counter_in:nat)
      returns (key:Set<K>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= UCardinalityKeys()
    ensures key.USize() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + CostPickKey(key)
    ensures counter_out <= counter_in + UCostPickKey()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    var chosen:set<K> :| chosen in entries.Keys;
    MaxByMember(universe.Keys, chosen, item => |item|);
    key := new ConcreteSet(chosen, chosen);
    counter_out := counter_in + CostPickKey(key);
  }

  method Count(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  {
    reveal Model();
    reveal UCardinalityKeys();
    size := |entries|;
    counter_out := counter_in + CostCount();
  }

  method IsEmpty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()
  {
    reveal Model();
    reveal UCardinalityKeys();
    empty := entries == map[];
    counter_out := counter_in + CostIsEmpty();
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    result := new ConcreteMap_Set_T(entries, entries);
    reveal result.UCardinalityKeys();
    counter_out := counter_in + CostCopy();
  }

}

method New_Map_Set_T<K(==), V(==)>(ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
  ensures Init_Map_Set_T(result)
  ensures result.UCardinalityKeys() == 0
  ensures result.Model() == map[] && result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_MapFamily()
{
  result := new ConcreteMap_Set_T(map[], map[]);
  reveal result.UCardinalityKeys();
  counter_out := counter_in + CostNew_MapFamily();
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
    reveal Model();
    SubsetCardinalityBound(entries_in.Keys, universe_in.Keys);
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    MaxByMonotonic(entries_in.Keys, universe_in.Keys, item => |item|);
    MaxByMonotonic(entries_in.Keys, universe_in.Keys, SetKeyCardinality);
    MultiplicationPreservesOrder(MaxCardinality_map(entries_in.Keys), MaxSetKeyCardinality_map_set_t(entries_in.Keys), MaxCardinality_map(universe_in.Keys), MaxSetKeyCardinality_map_set_t(universe_in.Keys));
    MultiplicationPreservesOrder(|entries_in|, MaxCardinality_map(entries_in.Keys) * MaxSetKeyCardinality_map_set_t(entries_in.Keys), |universe_in|, MaxCardinality_map(universe_in.Keys) * MaxSetKeyCardinality_map_set_t(universe_in.Keys));
  }

  function ExecutableModel():map<map<set<K>, V>, R> { entries }
  ghost function Universe():map<map<set<K>, V>, R> { universe }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()
  {
    reveal Model(), key.Model();
    value := entries[key.ExecutableModel()];
    counter_out := counter_in + CostGet();
  }

  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()
  {
    reveal Model(), key.Model();
    contains := key.ExecutableModel() in entries;
    counter_out := counter_in + CostContainsKey();
  }

  method {:isolate_assertions} Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.UCardinalityKeysKeys() == (if key.CardinalityKeys() <= UCardinalityKeysKeys() then UCardinalityKeysKeys() else key.CardinalityKeys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert()
    ensures counter_out <= counter_in + UCostInsert()
  {
    reveal Model(), key.Model();
    var concrete_key := key.ExecutableModel();
    var updatedEntries := entries[concrete_key := value];
    ghost var updatedUniverse := universe[concrete_key := value];
    UpdateAgreement_Map_MapSet_T(this, concrete_key, value);
    result := new ConcreteMap_MapSet_T(updatedEntries, updatedUniverse);
    assert result.Universe() == Universe()[key.Model() := value];
    InsertUniverseMeasures_Map_MapSet_T(this, result, key, value);
    counter_out := counter_in + CostInsert();
  }

  method Remove(key:Map_Set_T<K, V>, ghost counter_in:nat)
      returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.UCardinalityKeysKeys() <= UCardinalityKeysKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + CostRemove()
    ensures counter_out <= counter_in + UCostRemove()
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_MapSet_T(entries - {concrete_key}, universe);
    reveal result.UCardinalityKeys(), result.UCardinalityKeysKeys();
    counter_out := counter_in + CostRemove();
  }

  method PickKey(ghost counter_in:nat)
      returns (key:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Cardinality() <= UCardinalityKeys()
    ensures key.UCardinality() <= UCardinalityKeys()
    ensures key.CardinalityKeys() <= UCardinalityKeysKeys()
    ensures key.UCardinalityKeys() <= UCardinalityKeysKeys()
    ensures key.Size() <= USizeKeys()
    ensures key.USize() <= USizeKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + CostPickKey(key)
    ensures counter_out <= counter_in + UCostPickKey()
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    reveal Valid();
    var chosen:map<set<K>, V> :| chosen in entries.Keys;
    MaxByMember(universe.Keys, chosen, item => |item|);
    MaxSetKeyCardinalityMember_map_set_t(universe.Keys, chosen);
    key := new ConcreteMap_Set_T(chosen, chosen);
    reveal key.UCardinalityKeys();
    MultiplicationPreservesOrder(key.Cardinality(), key.CardinalityKeys(), UCardinalityKeys(), UCardinalityKeysKeys());
    counter_out := counter_in + CostPickKey(key);
  }

  method Count(ghost counter_in:nat)
      returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    size := |entries|;
    counter_out := counter_in + CostCount();
  }

  method IsEmpty(ghost counter_in:nat)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    empty := entries == map[];
    counter_out := counter_in + CostIsEmpty();
  }

  method Copy(ghost counter_in:nat)
      returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeysKeys() == CardinalityKeysKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.UCardinalityKeysKeys() <= UCardinalityKeysKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    reveal Valid();
    result := new ConcreteMap_MapSet_T(entries, entries);
    reveal result.UCardinalityKeys(), result.UCardinalityKeysKeys();
    counter_out := counter_in + CostCopy();
  }

}

method New_Map_MapSet_T<K(==), V(==), R(==)>(ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
  ensures Init_Map_MapSet_T(result)
  ensures result.UCardinalityKeys() == 0
  ensures result.UCardinalityKeysKeys() == 0
  ensures result.Model() == map[] && result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_MapFamily()
{
  result := new ConcreteMap_MapSet_T(map[], map[]);
  reveal result.UCardinalityKeys(), result.UCardinalityKeysKeys();
  counter_out := counter_in + CostNew_MapFamily();
}
