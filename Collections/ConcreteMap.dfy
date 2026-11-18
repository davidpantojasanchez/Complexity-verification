include "Map.dfy"
include "ConcreteSet.dfy"
include "CollectionUpdates.dfy"


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
    subset_cardinality_bound_set(entries_in.Keys, universe_in.Keys);
  }

  function ExecutableModel():map<K, V> { entries }
  ghost function Universe():map<K, V> { universe }

  method Get(key:K, ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context)
    ensures context.valueWeight(value) <= SizeBound(context.keyWeight, context.valueWeight)
  {
    reveal Model();
    value := entries[key];
    representation_member_map(Model(), context.keyWeight, context.valueWeight, key);
    counter_out := counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context);
  }

  method Insert(key:K, value:V, ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key) + context.valueWeight(value), context)
    ensures result.ULeafBits(context.keyWeight, context.valueWeight) <= MaxLeafWeight(ULeafBits(context.keyWeight, context.valueWeight),
        MaxLeafWeight(context.keyWeight(key), context.valueWeight(value)))
  {
    reveal Model();
    reveal Valid();
    result := new ConcreteMap(entries[key := value], universe[key := value]);
    max_leaf_bits_insert_map(Universe(), context.keyWeight, context.valueWeight, key, value);
    counter_out := counter_in + Cost(TraversalWork(),
      context.keyWeight(key) + context.valueWeight(value), context);
  }

  method Remove(key:K, ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures if key in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key}
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context)
    ensures result.SizeBound(context.keyWeight, context.valueWeight) <= SizeBound(context.keyWeight, context.valueWeight)
    ensures result.USizeBound(context.keyWeight, context.valueWeight) == USizeBound(context.keyWeight, context.valueWeight)
  {
    reveal Model();
    reveal Valid();
    result := new ConcreteMap(entries - {key}, universe);
    representation_submap_map(result.Model(), Model(), context.keyWeight, context.valueWeight);
    counter_out := counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context);
  }

  method PickKey(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (key:K, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + Cost(1, 0, context)
    ensures context.keyWeight(key) <= SizeBound(context.keyWeight, context.valueWeight)
    ensures context.keyWeight(key) <= LeafBits(context.keyWeight, context.valueWeight)
  {
    reveal Model();
    reveal Valid();
    key :| key in entries.Keys;
    representation_member_map(Model(), context.keyWeight, context.valueWeight, key);
    counter_out := counter_in + Cost(1, 0, context);
  }

  method Count(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    cardinality := |entries|;
    counter_out := counter_in + Cost(1, 0, context);
  }

  method ContainsKey(key:K, ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context)
  {
    reveal Model();
    contains := key in entries;
    counter_out := counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context);
  }

  method IsEmpty(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    empty := entries == map[];
    counter_out := counter_in + Cost(1, 0, context);
  }

  method Copy(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (result:Map<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)
    ensures result.SizeBound(context.keyWeight, context.valueWeight) == SizeBound(context.keyWeight, context.valueWeight) && result.USizeBound(context.keyWeight,
        context.valueWeight) == SizeBound(context.keyWeight, context.valueWeight)
  {
    reveal Model();
    result := new ConcreteMap(entries, entries);
    counter_out := counter_in + Cost(TraversalWork(), 0, context);
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
    subset_cardinality_bound_set(entries_in.Keys, universe_in.Keys);
    reveal UCardinalityKeys();
    max_by_monotonic(entries_in.Keys, universe_in.Keys, item => |item|);
    nonnegative_product_monotonic(|entries_in|, 1 + MaxCardinality_map(entries_in.Keys), |universe_in|, 1 + MaxCardinality_map(universe_in.Keys));
  }

  function ExecutableModel():map<map<K, V>, R> { entries }
  ghost function Universe():map<map<K, V>, R> { universe }

  method Get(key:Map<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context)
    ensures context.valueWeight(value) <= SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    value := entries[concrete_key];
    representation_member_map_map_t(Model(), context.keyWeight, context.innerValueWeight, context.valueWeight, key.Model());
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context);
  }

  method Insert(key:Map<K, V>, value:R, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.Keys() == Keys() + {key.Model()}
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight) + context.valueWeight(value), context)
    ensures result.ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <=
          MaxLeafWeight(ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight),
            MaxLeafWeight(key.LeafBits(context.keyWeight, context.innerValueWeight), context.valueWeight(value)))
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Map_T(
      entries[concrete_key := value],
      universe[concrete_key := value]);
    insert_universe_measures_map_map_t(this, result, key, value);
    max_leaf_bits_insert_map(Universe(), child => MaxLeafBits_map(child, context.keyWeight, context.innerValueWeight),
        context.valueWeight, key.Model(), value);
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight) + context.valueWeight(value), context);
  }

  method Remove(key:Map<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == UCardinalityKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context)
    ensures result.SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) <= SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures result.USizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) == USizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Map_T(entries - {concrete_key}, universe);
    assert result.Keys() == Keys() - {key.Model()};
    assert result.Cardinality() == |result.Keys()| && Cardinality() == |Keys()|;
    assert if key.Model() in Keys() then |Keys() - {key.Model()}| == |Keys()| - 1
      else Keys() - {key.Model()} == Keys();
    reveal result.UCardinalityKeys();
    representation_submap_map_map_t(result.Model(), Model(), context.keyWeight, context.innerValueWeight, context.valueWeight);
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context);
  }

  method PickKey(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (key:Map<K, V>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.VolumeBound() <= UCardinalityKeys()
    ensures key.UVolumeBound() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + Cost(key.TraversalWork(), 0, context)
    ensures key.USizeBound(context.keyWeight, context.innerValueWeight) == key.SizeBound(context.keyWeight, context.innerValueWeight)
    ensures key.SizeBound(context.keyWeight, context.innerValueWeight) <= SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures key.ULeafBits(context.keyWeight, context.innerValueWeight) <= LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    var chosen:map<K, V> :| chosen in entries.Keys;
    max_by_member(universe.Keys, chosen, item => |item|);
    key := new ConcreteMap(chosen, chosen);
    representation_member_map_map_t(Model(), context.keyWeight, context.innerValueWeight, context.valueWeight, key.Model());
    counter_out := counter_in + Cost(key.TraversalWork(), 0, context);
  }

  method Count(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    reveal UCardinalityKeys();
    cardinality := |entries|;
    counter_out := counter_in + Cost(1, 0, context);
  }

  method ContainsKey(key:Map<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    contains := concrete_key in entries;
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context);
  }

  method IsEmpty(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    reveal UCardinalityKeys();
    empty := entries == map[];
    counter_out := counter_in + Cost(1, 0, context);
  }

  method Copy(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (result:Map_Map_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)
    ensures result.SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) == SizeBound(context.keyWeight, context.innerValueWeight,
        context.valueWeight) && result.USizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) == SizeBound(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    result := new ConcreteMap_Map_T(entries, entries);
    reveal result.UCardinalityKeys();
    counter_out := counter_in + Cost(TraversalWork(), 0, context);
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
    subset_cardinality_bound_set(entries_in.Keys, universe_in.Keys);
    reveal UCardinalityKeys();
    max_by_monotonic(entries_in.Keys, universe_in.Keys, item => |item|);
    nonnegative_product_monotonic(|entries_in|, 1 + MaxCardinality_set(entries_in.Keys), |universe_in|, 1 + MaxCardinality_set(universe_in.Keys));
  }

  function ExecutableModel():map<set<K>, V> { entries }
  ghost function Universe():map<set<K>, V> { universe }

  method Get(key:Set<K>, ghost counter_in:nat, ghost context:MapContext<K,V>) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight), context)
    ensures context.valueWeight(value) <= SizeBound(context.keyWeight, context.valueWeight)
  {
    reveal Model(), key.Model();
    value := entries[key.ExecutableModel()];
    representation_member_map_set_t(Model(), context.keyWeight, context.valueWeight, key.Model());
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight), context);
  }

  method ContainsKey(key:Set<K>, ghost counter_in:nat, ghost context:MapContext<K,V>) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight), context)
  {
    reveal Model(), key.Model();
    contains := key.ExecutableModel() in entries;
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight), context);
  }

  method Insert(key:Set<K>, value:V, ghost counter_in:nat, ghost context:MapContext<K,V>) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight) + context.valueWeight(value), context)
    ensures result.ULeafBits(context.keyWeight, context.valueWeight) <= MaxLeafWeight(ULeafBits(context.keyWeight, context.valueWeight),
        MaxLeafWeight(key.LeafBits(context.keyWeight), context.valueWeight(value)))
  {
    reveal Model(), key.Model();
    reveal Valid();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Set_T(entries[concrete_key := value], universe[concrete_key := value]);
    insert_universe_measures_map_set_t(this, result, key, value);
    max_leaf_bits_insert_map(Universe(), child => MaxLeafBits_set(child, context.keyWeight), context.valueWeight, key.Model(), value);
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight) + context.valueWeight(value), context);
  }

  method Remove(key:Set<K>, ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == UCardinalityKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight), context)
    ensures result.SizeBound(context.keyWeight, context.valueWeight) <= SizeBound(context.keyWeight, context.valueWeight)
    ensures result.USizeBound(context.keyWeight, context.valueWeight) == USizeBound(context.keyWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_Set_T(entries - {concrete_key}, universe);
    reveal result.UCardinalityKeys();
    representation_submap_map_set_t(result.Model(), Model(), context.keyWeight, context.valueWeight);
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight), context);
  }

  method PickKey(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (key:Set<K>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.VolumeBound() <= UCardinalityKeys()
    ensures key.UVolumeBound() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + Cost(key.TraversalWork(), 0, context)
    ensures key.USizeBound(context.keyWeight) == key.SizeBound(context.keyWeight)
    ensures key.SizeBound(context.keyWeight) <= SizeBound(context.keyWeight, context.valueWeight)
    ensures key.ULeafBits(context.keyWeight) <= LeafBits(context.keyWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    var chosen:set<K> :| chosen in entries.Keys;
    max_by_member(universe.Keys, chosen, item => |item|);
    key := new ConcreteSet(chosen, chosen);
    representation_member_map_set_t(Model(), context.keyWeight, context.valueWeight, key.Model());
    counter_out := counter_in + Cost(key.TraversalWork(), 0, context);
  }

  method Count(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    reveal UCardinalityKeys();
    cardinality := |entries|;
    counter_out := counter_in + Cost(1, 0, context);
  }

  method IsEmpty(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    reveal UCardinalityKeys();
    empty := entries == map[];
    counter_out := counter_in + Cost(1, 0, context);
  }

  method Copy(ghost counter_in:nat, ghost context:MapContext<K,V>)
      returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)
    ensures result.SizeBound(context.keyWeight, context.valueWeight) == SizeBound(context.keyWeight, context.valueWeight) && result.USizeBound(context.keyWeight,
        context.valueWeight) == SizeBound(context.keyWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys();
    reveal Valid();
    result := new ConcreteMap_Set_T(entries, entries);
    reveal result.UCardinalityKeys();
    counter_out := counter_in + Cost(TraversalWork(), 0, context);
  }

}

method New_Map_Set_T<K(==), V(==)>(ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
  ensures result.Init()
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
    subset_cardinality_bound_set(entries_in.Keys, universe_in.Keys);
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    max_by_monotonic(entries_in.Keys, universe_in.Keys, item => |item|);
    max_by_monotonic(entries_in.Keys, universe_in.Keys, KeyCardinality_map_set_t);
    nonnegative_product_monotonic(MaxCardinality_map(entries_in.Keys), 1 + MaxSetKeyCardinality_map_set_t(entries_in.Keys),
        MaxCardinality_map(universe_in.Keys), 1 + MaxSetKeyCardinality_map_set_t(universe_in.Keys));
    nonnegative_product_monotonic(|entries_in|, 1 + MaxCardinality_map(entries_in.Keys) * (1 + MaxSetKeyCardinality_map_set_t(entries_in.Keys)),
        |universe_in|, 1 + MaxCardinality_map(universe_in.Keys) * (1 + MaxSetKeyCardinality_map_set_t(universe_in.Keys)));
  }

  function ExecutableModel():map<map<set<K>, V>, R> { entries }
  ghost function Universe():map<map<set<K>, V>, R> { universe }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context)
    ensures context.valueWeight(value) <= SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
  {
    reveal Model(), key.Model();
    value := entries[key.ExecutableModel()];
    representation_member_map_mapset_t(Model(), context.keyWeight, context.innerValueWeight, context.valueWeight, key.Model());
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context);
  }

  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context)
  {
    contains := key.ExecutableModel() in entries;
    assert contains == (key.Model() in Model().Keys) by {
      reveal Model(), key.Model();
    }
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context);
  }

  method Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.UCardinalityKeysKeys() == (if key.CardinalityKeys() <= UCardinalityKeysKeys() then UCardinalityKeysKeys() else key.CardinalityKeys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight) + context.valueWeight(value), context)
    ensures result.ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <=
          MaxLeafWeight(ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight),
            MaxLeafWeight(key.LeafBits(context.keyWeight, context.innerValueWeight), context.valueWeight(value)))
  {
    reveal Model(), key.Model();
    var concrete_key := key.ExecutableModel();
    var updatedEntries := entries[concrete_key := value];
    ghost var updatedUniverse := universe[concrete_key := value];
    update_agreement_map(Model(), Universe(), concrete_key, value);
    result := new ConcreteMap_MapSet_T(updatedEntries, updatedUniverse);
    assert result.Model() == Model()[key.Model() := value] by {
      assert result.Model() == updatedEntries;
    }
    assert result.Universe() == Universe()[key.Model() := value];
    insert_universe_measures_map_map_set_t(this, result, key, value);
    max_leaf_bits_insert_map(Universe(), child => MaxLeafBits_map_set_t(child, context.keyWeight,
        context.innerValueWeight), context.valueWeight, key.Model(), value);
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight) + context.valueWeight(value), context);
  }

  method Remove(key:Map_Set_T<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == UCardinalityKeys()
    ensures result.UCardinalityKeysKeys() == UCardinalityKeysKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context)
    ensures result.SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) <= SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures result.USizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) == USizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    reveal Valid();
    reveal key.Model();
    var concrete_key := key.ExecutableModel();
    result := new ConcreteMap_MapSet_T(entries - {concrete_key}, universe);
    reveal result.UCardinalityKeys(), result.UCardinalityKeysKeys();
    representation_submap_map_mapset_t(result.Model(), Model(), context.keyWeight, context.innerValueWeight, context.valueWeight);
    counter_out := counter_in + Cost(TraversalWork(),
      key.SizeBound(context.keyWeight, context.innerValueWeight), context);
  }

  method PickKey(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (key:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Cardinality() <= UCardinalityKeys()
    ensures key.UCardinality() <= UCardinalityKeys()
    ensures key.CardinalityKeys() <= UCardinalityKeysKeys()
    ensures key.UCardinalityKeys() <= UCardinalityKeysKeys()
    ensures key.VolumeBound() <= UVolumeBoundKeys()
    ensures key.UVolumeBound() <= UVolumeBoundKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + Cost(key.TraversalWork(), 0, context)
    ensures key.USizeBound(context.keyWeight, context.innerValueWeight) == key.SizeBound(context.keyWeight, context.innerValueWeight)
    ensures key.SizeBound(context.keyWeight, context.innerValueWeight) <= SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures key.ULeafBits(context.keyWeight, context.innerValueWeight) <= LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    reveal Valid();
    var chosen:map<set<K>, V> :| chosen in entries.Keys;
    max_by_member(universe.Keys, chosen, item => |item|);
    max_set_key_cardinality_member_map_set_t(universe.Keys, chosen);
    key := new ConcreteMap_Set_T(chosen, chosen);
    reveal key.UCardinalityKeys();
    nonnegative_product_monotonic(key.Cardinality(), 1 + key.CardinalityKeys(), UCardinalityKeys(), 1 + UCardinalityKeysKeys());
    representation_member_map_mapset_t(Model(), context.keyWeight, context.innerValueWeight, context.valueWeight, key.Model());
    counter_out := counter_in + Cost(key.TraversalWork(), 0, context);
  }

  method Count(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    cardinality := |entries|;
    counter_out := counter_in + Cost(1, 0, context);
  }

  method IsEmpty(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    empty := entries == map[];
    counter_out := counter_in + Cost(1, 0, context);
  }

  method Copy(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeysKeys() == CardinalityKeysKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.UCardinalityKeysKeys() <= UCardinalityKeysKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)
    ensures result.SizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) == SizeBound(context.keyWeight, context.innerValueWeight,
        context.valueWeight) && result.USizeBound(context.keyWeight, context.innerValueWeight, context.valueWeight) == SizeBound(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
  {
    reveal Model();
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    reveal Valid();
    result := new ConcreteMap_MapSet_T(entries, entries);
    reveal result.UCardinalityKeys(), result.UCardinalityKeysKeys();
    assert result.UCardinalityKeys() == MaxCardinality_map(entries.Keys);
    counter_out := counter_in + Cost(TraversalWork(), 0, context);
  }

}

method New_Map_MapSet_T<K(==), V(==), R(==)>(ghost counter_in:nat)
    returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
  ensures result.Init()
  ensures result.UCardinalityKeys() == 0
  ensures result.UCardinalityKeysKeys() == 0
  ensures result.Model() == map[] && result.Universe() == map[]
  ensures counter_out == counter_in + CostNew_MapFamily()
{
  result := new ConcreteMap_MapSet_T(map[], map[]);
  reveal result.UCardinalityKeys(), result.UCardinalityKeysKeys();
  counter_out := counter_in + CostNew_MapFamily();
}
