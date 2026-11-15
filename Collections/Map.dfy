include "../Foundations/Collections.dfy"
include "Set.dfy"
/*
Traits for immutable maps
Concrete implementations are defined in ConcreteMap.dfy.
*/

// Shared structural model, universe relation and work for all map shapes.
trait MapFamily<K, V> {
  ghost function Model():map<K, V>
  ghost function Universe():map<K, V>

  ghost predicate Valid()
    ensures Valid() ==> Model().Keys <= Universe().Keys
    ensures Valid() ==> (forall key | key in Model().Keys :: Model()[key] == Universe()[key])

  ghost function Cardinality():nat { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  
  ghost function Volume():nat
  ghost function UVolume():nat

  ghost function Keys():set<K> { Model().Keys }
  ghost function Values():set<V> { Model().Values }

  ghost predicate Init() {
    Valid() && Model() == Universe()
  }

  ghost predicate UniverseWithin(reference:MapFamily<K, V>) {
    Valid() && reference.Valid() && Universe().Keys <= reference.Model().Keys &&
    (forall key | key in Universe().Keys :: Universe()[key] == reference.Model()[key])
  }

  ghost function TraversalWork():nat { Volume() + 1 }

  lemma universe_within_transitive(middle:MapFamily<K, V>, reference:MapFamily<K, V>)
    requires UniverseWithin(middle)
    requires middle.UniverseWithin(reference)
    ensures UniverseWithin(reference)
  {}
}


trait Map<T0(==), T1(==)> extends MapFamily<T0, T1> {
  function ExecutableModel():map<T0, T1>
  ghost function {:opaque} Model():map<T0, T1> { ExecutableModel() }
  ghost function Universe():map<T0, T1>

  ghost predicate Valid()
    ensures Valid() ==> Model().Keys <= Universe().Keys
    ensures Valid() ==> (forall key | key in Model().Keys :: Model()[key] == Universe()[key])
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality() &&
    Volume() <= UVolume()
  }

  ghost function Volume():nat { Cardinality() }
  ghost function UVolume():nat { UCardinality() }

  ghost function Size(keyWeight:T0 -> nat, valueWeight:T1 -> nat):(size:nat)
    ensures size == StructuralSize(Volume(), LeafBits(keyWeight, valueWeight))
    ensures Volume() <= size && LeafBits(keyWeight, valueWeight) <= size
    ensures Cardinality() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USize(keyWeight, valueWeight)
  {
    representation_submap_map(Model(), Universe(), keyWeight, valueWeight, Valid());
    RepresentationSize_map(Model(), keyWeight, valueWeight)
  }

  ghost function USize(keyWeight:T0 -> nat, valueWeight:T1 -> nat):(size:nat)
    ensures size == StructuralSize(UVolume(), ULeafBits(keyWeight, valueWeight))
    ensures UVolume() <= size && ULeafBits(keyWeight, valueWeight) <= size
    ensures UCardinality() <= size
    ensures 1 <= size
  {
    RepresentationSize_map(Universe(), keyWeight, valueWeight)
  }

  ghost function LeafBits(keyWeight:T0 -> nat, valueWeight:T1 -> nat):(bits:nat)
    ensures 1 <= bits
    ensures Valid() ==> bits <= ULeafBits(keyWeight, valueWeight)
  {
    representation_submap_map(Model(), Universe(), keyWeight, valueWeight, Valid());
    MaxLeafBits_map(Model(), keyWeight, valueWeight)
  }
  ghost function ULeafBits(keyWeight:T0 -> nat, valueWeight:T1 -> nat):(bits:nat)
    ensures 1 <= bits
  { MaxLeafBits_map(Universe(), keyWeight, valueWeight) }

  ghost function Cost(work:nat, operandSize:nat, context:MapContext<T0,T1>):(cost:nat)
    ensures
      (work <= context.bound+1 && Size(context.keyWeight, context.valueWeight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := Size(context.keyWeight, context.valueWeight);
    collection_step_bound(work, size, operandSize, context.bound);
    CostRepresentation(work, size, operandSize)
  }

  method Get(key:T0, ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (value:T1, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures context.valueWeight(value) <= Size(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context)


  method Insert(key:T0, value:T1, ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures result.ULeafBits(context.keyWeight, context.valueWeight) <= MaxLeafWeight(ULeafBits(context.keyWeight, context.valueWeight),
        MaxLeafWeight(context.keyWeight(key), context.valueWeight(value)))
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key) + context.valueWeight(value), context)


  method Remove(key:T0, ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures if key in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key}
    ensures result.Size(context.keyWeight, context.valueWeight) <= Size(context.keyWeight, context.valueWeight)
    ensures result.USize(context.keyWeight, context.valueWeight) == USize(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context)


  method PickKey(ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (key:T0, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures context.keyWeight(key) <= Size(context.keyWeight, context.valueWeight)
    ensures context.keyWeight(key) <= LeafBits(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Count(ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)

  method ContainsKey(key:T0, ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      context.keyWeight(key), context)

  method IsEmpty(ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Copy(ghost counter_in:nat, ghost context:MapContext<T0,T1>) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures result.Size(context.keyWeight, context.valueWeight) == Size(context.keyWeight, context.valueWeight) && result.USize(context.keyWeight,
        context.valueWeight) == Size(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)

  // Complexity bounds

  lemma u_leaf_bits_bound(bits:nat, keyWeight:T0 -> nat, valueWeight:T1 -> nat)
    requires 1 <= bits
    requires forall item | item in Universe() :: keyWeight(item) <= bits && valueWeight(Universe()[item]) <= bits
    ensures ULeafBits(keyWeight, valueWeight) <= bits
  {
    max_leaf_bits_bound_map(Universe(), keyWeight, valueWeight, bits);
  }

  lemma u_size_bound(volume:nat, bits:nat, keyWeight:T0 -> nat, valueWeight:T1 -> nat)
    requires UVolume() <= volume && ULeafBits(keyWeight, valueWeight) <= bits && 1 <= bits
    ensures USize(keyWeight, valueWeight) <= StructuralSize(volume, bits)
  {
    structural_size_monotonic(UVolume(), ULeafBits(keyWeight, valueWeight), volume, bits);
  }

  lemma universe_within_bound(U:Map<T0, T1>, context:MapContext<T0,T1>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Volume() <= UVolume() <= U.Volume() <= U.UVolume()
    ensures Size(context.keyWeight, context.valueWeight) <= USize(context.keyWeight, context.valueWeight) <= U.Size(context.keyWeight,
        context.valueWeight) <= U.USize(context.keyWeight, context.valueWeight)
    ensures LeafBits(context.keyWeight, context.valueWeight) <= ULeafBits(context.keyWeight, context.valueWeight) <= U.LeafBits(context.keyWeight,
        context.valueWeight) <= U.ULeafBits(context.keyWeight, context.valueWeight)
  {
    representation_submap_map(Universe(), U.Model(), context.keyWeight, context.valueWeight);
    subset_cardinality_bound_set(Universe().Keys, U.Model().Keys);
  }
}


// Maps whose keys are maps
trait Map_Map_T<T0(==), T1(==), T2(==)> extends MapFamily<map<T0, T1>, T2> {
  function ExecutableModel():map<map<T0, T1>, T2>
  ghost function {:opaque} Model():map<map<T0, T1>, T2> { ExecutableModel() }
  ghost function Universe():map<map<T0, T1>, T2>

  ghost predicate Valid()
    ensures Valid() ==> Model().Keys <= Universe().Keys
    ensures Valid() ==> (forall key | key in Model().Keys :: Model()[key] == Universe()[key])
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality() &&
    CardinalityKeys() <= UCardinalityKeys() &&
    Volume() <= UVolume() &&
    VolumeKeys() <= UVolumeKeys()
  }

  ghost function CardinalityKeys():nat { MaxCardinality_map(Model().Keys) }
  ghost function {:opaque} UCardinalityKeys():nat { MaxCardinality_map(Universe().Keys) }

  ghost function Volume():nat { Cardinality() * (1 + CardinalityKeys()) }
  ghost function UVolume():nat { UCardinality() * (1 + UCardinalityKeys()) }
  ghost function VolumeKeys():nat { CardinalityKeys() }
  ghost function UVolumeKeys():nat { UCardinalityKeys() }

  ghost function Size(keyWeight:T0 -> nat, innerValueWeight:T1 -> nat, valueWeight:T2 -> nat):(size:nat)
    ensures size == StructuralSize(Volume(), LeafBits(keyWeight, innerValueWeight, valueWeight))
    ensures Volume() <= size && LeafBits(keyWeight, innerValueWeight, valueWeight) <= size
    ensures Cardinality() <= size && CardinalityKeys() <= size
    ensures VolumeKeys() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USize(keyWeight, innerValueWeight, valueWeight)
  {
    representation_submap_map_map_t(Model(), Universe(), keyWeight, innerValueWeight, valueWeight, Valid());
    RepresentationSize_map_map_t(Model(), keyWeight, innerValueWeight, valueWeight)
  }

  ghost function USize(keyWeight:T0 -> nat, innerValueWeight:T1 -> nat, valueWeight:T2 -> nat):(size:nat)
    ensures size == StructuralSize(UVolume(), ULeafBits(keyWeight, innerValueWeight, valueWeight))
    ensures UVolume() <= size && ULeafBits(keyWeight, innerValueWeight, valueWeight) <= size
    ensures UCardinality() <= size && UCardinalityKeys() <= size
    ensures UVolumeKeys() <= size
    ensures 1 <= size
  {
    reveal UCardinalityKeys();
    RepresentationSize_map_map_t(Universe(), keyWeight, innerValueWeight, valueWeight)
  }

  ghost function LeafBits(keyWeight:T0 -> nat, innerValueWeight:T1 -> nat, valueWeight:T2 -> nat):(bits:nat)
    ensures 1 <= bits
    ensures Valid() ==> bits <= ULeafBits(keyWeight, innerValueWeight, valueWeight)
  {
    representation_submap_map_map_t(Model(), Universe(), keyWeight, innerValueWeight, valueWeight, Valid());
    MaxLeafBits_map_map_t(Model(), keyWeight, innerValueWeight, valueWeight)
  }
  ghost function ULeafBits(keyWeight:T0 -> nat, innerValueWeight:T1 -> nat, valueWeight:T2 -> nat):(bits:nat)
    ensures 1 <= bits
  { MaxLeafBits_map_map_t(Universe(), keyWeight, innerValueWeight, valueWeight) }

  ghost function Cost(work:nat, operandSize:nat, context:NestedMapContext<T0,T1,T2>):(cost:nat)
    ensures
      (work <= context.bound+1 && Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := Size(context.keyWeight, context.innerValueWeight, context.valueWeight);
    collection_step_bound(work, size, operandSize, context.bound);
    CostRepresentation(work, size, operandSize)
  }

  method Get(key:Map<T0, T1>, ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>) returns (value:T2, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures context.valueWeight(value) <= Size(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight), context)


  method Insert(key:Map<T0, T1>, value:T2, ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>)
      returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.Keys() == Keys() + {key.Model()}
    ensures result.ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <=
          MaxLeafWeight(ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight),
            MaxLeafWeight(key.LeafBits(context.keyWeight, context.innerValueWeight), context.valueWeight(value)))
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight) + context.valueWeight(value), context)


  method Remove(key:Map<T0, T1>, ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>)
      returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == UCardinalityKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures result.Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= Size(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures result.USize(context.keyWeight, context.innerValueWeight, context.valueWeight) == USize(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight), context)


  method PickKey(ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>) returns (key:Map<T0, T1>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Volume() <= UCardinalityKeys()
    ensures key.UVolume() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures key.USize(context.keyWeight, context.innerValueWeight) == key.Size(context.keyWeight, context.innerValueWeight)
    ensures key.Size(context.keyWeight, context.innerValueWeight) <= Size(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures key.ULeafBits(context.keyWeight, context.innerValueWeight) <= LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(key.TraversalWork(), 0, context)

  method Count(ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>) returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)

  method ContainsKey(key:Map<T0, T1>, ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight), context)

  method IsEmpty(ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Copy(ghost counter_in:nat, ghost context:NestedMapContext<T0,T1,T2>) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures result.Size(context.keyWeight, context.innerValueWeight, context.valueWeight) == Size(context.keyWeight, context.innerValueWeight,
        context.valueWeight) && result.USize(context.keyWeight, context.innerValueWeight, context.valueWeight) == Size(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)

  // Complexity bounds

  lemma u_leaf_bits_bound(bits:nat, keyWeight:T0 -> nat, innerValueWeight:T1 -> nat, valueWeight:T2 -> nat)
    requires 1 <= bits
    requires forall item | item in Universe() :: (child => MaxLeafBits_map(child, keyWeight, innerValueWeight))(item) <= bits && valueWeight(Universe()[item]) <= bits
    ensures ULeafBits(keyWeight, innerValueWeight, valueWeight) <= bits
  {
    max_leaf_bits_bound_map(Universe(), child => MaxLeafBits_map(child, keyWeight, innerValueWeight), valueWeight, bits);
  }

  lemma u_size_bound(volume:nat, bits:nat, keyWeight:T0 -> nat, innerValueWeight:T1 -> nat, valueWeight:T2 -> nat)
    requires UVolume() <= volume && ULeafBits(keyWeight, innerValueWeight, valueWeight) <= bits && 1 <= bits
    ensures USize(keyWeight, innerValueWeight, valueWeight) <= StructuralSize(volume, bits)
  {
    structural_size_monotonic(UVolume(), ULeafBits(keyWeight, innerValueWeight, valueWeight), volume, bits);
  }
  
  lemma {:isolate_assertions} universe_within_bound(U:Map_Map_T<T0, T1, T2>, context:NestedMapContext<T0,T1,T2>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures CardinalityKeys() <= UCardinalityKeys() <= U.CardinalityKeys() <= U.UCardinalityKeys()
    ensures Volume() <= UVolume() <= U.Volume() <= U.UVolume()
    ensures VolumeKeys() <= UVolumeKeys() <= U.VolumeKeys() <= U.UVolumeKeys()
    ensures Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= USize(context.keyWeight, context.innerValueWeight,
        context.valueWeight) <= U.Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= U.USize(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
    ensures LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <= ULeafBits(context.keyWeight, context.innerValueWeight,
        context.valueWeight) <= U.LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <= U.ULeafBits(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
  {
    representation_submap_map_map_t(Universe(), U.Model(), context.keyWeight, context.innerValueWeight, context.valueWeight);
    reveal UCardinalityKeys();
    subset_cardinality_bound_set(Universe().Keys, U.Model().Keys);
    max_by_monotonic(Universe().Keys, U.Model().Keys, item => |item|);
    nonnegative_product_monotonic(UCardinality(), 1 + UCardinalityKeys(), U.Cardinality(), 1 + U.CardinalityKeys());
  }

  lemma u_volume_bound(count:nat, key:nat)
    requires UCardinality() <= count && UCardinalityKeys() <= key
    ensures UVolume() <= count * (1 + key)
  {
    nonnegative_product_monotonic(UCardinality(), 1 + UCardinalityKeys(), count, 1 + key);
  }

  lemma u_cardinality_keys_bound(bound:nat)
    requires forall key | key in Universe().Keys :: |key| <= bound
    ensures UCardinalityKeys() <= bound
  {
    reveal UCardinalityKeys();
    max_by_bound(Universe().Keys, bound, item => |item|);
  }
}


// Maps whose keys are sets
trait Map_Set_T<K(==), V(==)> extends MapFamily<set<K>, V> {
  function ExecutableModel():map<set<K>, V>
  ghost function {:opaque} Model():map<set<K>, V> { ExecutableModel() }
  ghost function Universe():map<set<K>, V>

  ghost predicate Valid()
    ensures Valid() ==> Model().Keys <= Universe().Keys
    ensures Valid() ==> (forall key | key in Model().Keys :: Model()[key] == Universe()[key])
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality() &&
    CardinalityKeys() <= UCardinalityKeys() &&
    Volume() <= UVolume() &&
    VolumeKeys() <= UVolumeKeys()
  }

  ghost function CardinalityKeys():nat { MaxCardinality_set(Model().Keys) }
  ghost function {:opaque} UCardinalityKeys():nat { MaxCardinality_set(Universe().Keys) }

  ghost function Volume():nat { Cardinality() * (1 + CardinalityKeys()) }
  ghost function UVolume():nat { UCardinality() * (1 + UCardinalityKeys()) }
  ghost function VolumeKeys():nat { CardinalityKeys() }
  ghost function UVolumeKeys():nat { UCardinalityKeys() }

  ghost function Size(keyWeight:K -> nat, valueWeight:V -> nat):(size:nat)
    ensures size == StructuralSize(Volume(), LeafBits(keyWeight, valueWeight))
    ensures Volume() <= size && LeafBits(keyWeight, valueWeight) <= size
    ensures Cardinality() <= size && CardinalityKeys() <= size
    ensures VolumeKeys() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USize(keyWeight, valueWeight)
  {
    representation_submap_map_set_t(Model(), Universe(), keyWeight, valueWeight, Valid());
    RepresentationSize_map_set_t(Model(), keyWeight, valueWeight)
  }

  ghost function USize(keyWeight:K -> nat, valueWeight:V -> nat):(size:nat)
    ensures size == StructuralSize(UVolume(), ULeafBits(keyWeight, valueWeight))
    ensures UVolume() <= size && ULeafBits(keyWeight, valueWeight) <= size
    ensures UCardinality() <= size && UCardinalityKeys() <= size
    ensures UVolumeKeys() <= size
    ensures 1 <= size
  {
    reveal UCardinalityKeys();
    RepresentationSize_map_set_t(Universe(), keyWeight, valueWeight)
  }

  ghost function LeafBits(keyWeight:K -> nat, valueWeight:V -> nat):(bits:nat)
    ensures 1 <= bits
    ensures Valid() ==> bits <= ULeafBits(keyWeight, valueWeight)
  {
    representation_submap_map_set_t(Model(), Universe(), keyWeight, valueWeight, Valid());
    MaxLeafBits_map_set_t(Model(), keyWeight, valueWeight)
  }
  ghost function ULeafBits(keyWeight:K -> nat, valueWeight:V -> nat):(bits:nat)
    ensures 1 <= bits
  { MaxLeafBits_map_set_t(Universe(), keyWeight, valueWeight) }

  ghost function Cost(work:nat, operandSize:nat, context:MapContext<K,V>):(cost:nat)
    ensures
      (work <= context.bound+1 && Size(context.keyWeight, context.valueWeight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := Size(context.keyWeight, context.valueWeight);
    collection_step_bound(work, size, operandSize, context.bound);
    CostRepresentation(work, size, operandSize)
  }

  method Get(key:Set<K>, ghost counter_in:nat, ghost context:MapContext<K,V>) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures context.valueWeight(value) <= Size(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight), context)


  method ContainsKey(key:Set<K>, ghost counter_in:nat, ghost context:MapContext<K,V>) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight), context)

  method Insert(key:Set<K>, value:V, ghost counter_in:nat, ghost context:MapContext<K,V>) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.ULeafBits(context.keyWeight, context.valueWeight) <= MaxLeafWeight(ULeafBits(context.keyWeight, context.valueWeight),
        MaxLeafWeight(key.LeafBits(context.keyWeight), context.valueWeight(value)))
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight) + context.valueWeight(value), context)


  method Remove(key:Set<K>, ghost counter_in:nat, ghost context:MapContext<K,V>) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == UCardinalityKeys()
    ensures if key.Model() in Keys()
            then result.Cardinality() == Cardinality() - 1
            else result.Cardinality() == Cardinality()
    ensures result.Model() == Model() - {key.Model()}
    ensures result.Universe() == Universe()
    ensures result.Keys() == Keys() - {key.Model()}
    ensures result.Size(context.keyWeight, context.valueWeight) <= Size(context.keyWeight, context.valueWeight)
    ensures result.USize(context.keyWeight, context.valueWeight) == USize(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight), context)


  method PickKey(ghost counter_in:nat, ghost context:MapContext<K,V>) returns (key:Set<K>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Volume() <= UCardinalityKeys()
    ensures key.UVolume() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures key.USize(context.keyWeight) == key.Size(context.keyWeight)
    ensures key.Size(context.keyWeight) <= Size(context.keyWeight, context.valueWeight)
    ensures key.ULeafBits(context.keyWeight) <= LeafBits(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(key.TraversalWork(), 0, context)

  method Count(ghost counter_in:nat, ghost context:MapContext<K,V>) returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)

  method IsEmpty(ghost counter_in:nat, ghost context:MapContext<K,V>) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Copy(ghost counter_in:nat, ghost context:MapContext<K,V>) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures result.Size(context.keyWeight, context.valueWeight) == Size(context.keyWeight, context.valueWeight) && result.USize(context.keyWeight,
        context.valueWeight) == Size(context.keyWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)

  // Complexity bounds

  lemma u_leaf_bits_bound(bits:nat, keyWeight:K -> nat, valueWeight:V -> nat)
    requires 1 <= bits
    requires forall item | item in Universe() :: (child => MaxLeafBits_set(child, keyWeight))(item) <= bits && valueWeight(Universe()[item]) <= bits
    ensures ULeafBits(keyWeight, valueWeight) <= bits
  {
    max_leaf_bits_bound_map(Universe(), child => MaxLeafBits_set(child, keyWeight), valueWeight, bits);
  }

  lemma u_size_bound(volume:nat, bits:nat, keyWeight:K -> nat, valueWeight:V -> nat)
    requires UVolume() <= volume && ULeafBits(keyWeight, valueWeight) <= bits && 1 <= bits
    ensures USize(keyWeight, valueWeight) <= StructuralSize(volume, bits)
  {
    structural_size_monotonic(UVolume(), ULeafBits(keyWeight, valueWeight), volume, bits);
  }

  lemma {:isolate_assertions} universe_within_bound(U:Map_Set_T<K, V>, context:MapContext<K,V>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures CardinalityKeys() <= UCardinalityKeys() <= U.CardinalityKeys() <= U.UCardinalityKeys()
    ensures Volume() <= UVolume() <= U.Volume() <= U.UVolume()
    ensures VolumeKeys() <= UVolumeKeys() <= U.VolumeKeys() <= U.UVolumeKeys()
    ensures Size(context.keyWeight, context.valueWeight) <= USize(context.keyWeight, context.valueWeight) <= U.Size(context.keyWeight,
        context.valueWeight) <= U.USize(context.keyWeight, context.valueWeight)
    ensures LeafBits(context.keyWeight, context.valueWeight) <= ULeafBits(context.keyWeight, context.valueWeight) <= U.LeafBits(context.keyWeight,
        context.valueWeight) <= U.ULeafBits(context.keyWeight, context.valueWeight)
  {
    representation_submap_map_set_t(Universe(), U.Model(), context.keyWeight, context.valueWeight);
    reveal UCardinalityKeys();
    subset_cardinality_bound_set(Universe().Keys, U.Model().Keys);
    max_by_monotonic(Universe().Keys, U.Model().Keys, item => |item|);
    nonnegative_product_monotonic(UCardinality(), 1 + UCardinalityKeys(), U.Cardinality(), 1 + U.CardinalityKeys());
  }

  lemma u_volume_bound(count:nat, key:nat)
    requires UCardinality() <= count && UCardinalityKeys() <= key
    ensures UVolume() <= count*(1+key)
  {
    nonnegative_product_monotonic(UCardinality(), 1 + UCardinalityKeys(), count, 1 + key);
  }

  lemma u_cardinality_keys_bound(bound:nat)
    requires forall key | key in Universe().Keys :: |key| <= bound
    ensures UCardinalityKeys() <= bound
  {
    reveal UCardinalityKeys();
    max_by_bound(Universe().Keys, bound, item => |item|);
  }
}


// Maps whose keys are maps whose keys are sets
trait Map_MapSet_T<K(==), V(==), R(==)> extends MapFamily<map<set<K>, V>, R> {
  function ExecutableModel():map<map<set<K>, V>, R>
  ghost function {:opaque} Model():map<map<set<K>, V>, R> { ExecutableModel() }
  ghost function Universe():map<map<set<K>, V>, R>
  
  ghost predicate Valid()
    ensures Valid() ==> Model().Keys <= Universe().Keys
    ensures Valid() ==> (forall key | key in Model().Keys :: Model()[key] == Universe()[key])
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality() &&
    CardinalityKeys() <= UCardinalityKeys() &&
    CardinalityKeysKeys() <= UCardinalityKeysKeys() &&
    Volume() <= UVolume() &&
    VolumeKeys() <= UVolumeKeys() &&
    VolumeKeysKeys() <= UVolumeKeysKeys()
  }
  
  ghost function CardinalityKeys():nat { MaxCardinality_map(Model().Keys) }
  ghost function {:opaque} UCardinalityKeys():nat { MaxCardinality_map(Universe().Keys) }
  ghost function CardinalityKeysKeys():nat { MaxSetKeyCardinality_map_set_t(Model().Keys) }
  ghost function {:opaque} UCardinalityKeysKeys():nat { MaxSetKeyCardinality_map_set_t(Universe().Keys) }

  ghost function Volume():nat { Cardinality() * (1 + VolumeKeys()) }
  ghost function UVolume():nat { UCardinality() * (1 + UVolumeKeys()) }
  ghost function VolumeKeys():nat { CardinalityKeys() * (1 + CardinalityKeysKeys()) }
  ghost function UVolumeKeys():nat { UCardinalityKeys() * (1 + UCardinalityKeysKeys()) }
  ghost function VolumeKeysKeys():nat { CardinalityKeysKeys() }
  ghost function UVolumeKeysKeys():nat { UCardinalityKeysKeys() }

  ghost function Size(keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:R -> nat):(size:nat)
    ensures size == StructuralSize(Volume(), LeafBits(keyWeight, innerValueWeight, valueWeight))
    ensures Volume() <= size && LeafBits(keyWeight, innerValueWeight, valueWeight) <= size
    ensures Cardinality() <= size && CardinalityKeys() <= size && CardinalityKeysKeys() <= size
    ensures VolumeKeys() <= size && VolumeKeysKeys() <= size
    ensures 1 <= size
    ensures Valid() ==> size <= USize(keyWeight, innerValueWeight, valueWeight)
  {
    assert CardinalityKeysKeys() <= VolumeKeys();
    assert VolumeKeys() <= Volume();
    representation_submap_map_mapset_t(Model(), Universe(), keyWeight, innerValueWeight, valueWeight, Valid());
    RepresentationSize_map_mapset_t(Model(), keyWeight, innerValueWeight, valueWeight)
  }

  ghost function USize(keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:R -> nat):(size:nat)
    ensures size == StructuralSize(UVolume(), ULeafBits(keyWeight, innerValueWeight, valueWeight))
    ensures UVolume() <= size && ULeafBits(keyWeight, innerValueWeight, valueWeight) <= size
    ensures UCardinality() <= size && UCardinalityKeys() <= size && UCardinalityKeysKeys() <= size
    ensures UVolumeKeys() <= size && UVolumeKeysKeys() <= size
    ensures 1 <= size
  {
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    assert UCardinalityKeysKeys() <= UVolumeKeys();
    assert UVolumeKeys() <= UVolume();
    RepresentationSize_map_mapset_t(Universe(), keyWeight, innerValueWeight, valueWeight)
  }

  ghost function LeafBits(keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:R -> nat):(bits:nat)
    ensures 1 <= bits
    ensures Valid() ==> bits <= ULeafBits(keyWeight, innerValueWeight, valueWeight)
  {
    representation_submap_map_mapset_t(Model(), Universe(), keyWeight, innerValueWeight, valueWeight, Valid());
    MaxLeafBits_map_mapset_t(Model(), keyWeight, innerValueWeight, valueWeight)
  }
  ghost function ULeafBits(keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:R -> nat):(bits:nat)
    ensures 1 <= bits
  { MaxLeafBits_map_mapset_t(Universe(), keyWeight, innerValueWeight, valueWeight) }

  ghost function Cost(work:nat, operandSize:nat, context:NestedMapContext<K,V,R>):(cost:nat)
    ensures
      (work <= context.bound+1 && Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= context.bound && operandSize <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := Size(context.keyWeight, context.innerValueWeight, context.valueWeight);
    collection_step_bound(work, size, operandSize, context.bound);
    CostRepresentation(work, size, operandSize)
  }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures context.valueWeight(value) <= Size(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight), context)


  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight), context)

  method Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>)
      returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.UCardinalityKeysKeys() == (if key.CardinalityKeys() <= UCardinalityKeysKeys() then UCardinalityKeysKeys() else key.CardinalityKeys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures result.ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <=
          MaxLeafWeight(ULeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight),
            MaxLeafWeight(key.LeafBits(context.keyWeight, context.innerValueWeight), context.valueWeight(value)))
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight) + context.valueWeight(value), context)


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
    ensures result.Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= Size(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures result.USize(context.keyWeight, context.innerValueWeight, context.valueWeight) == USize(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(),
      key.Size(context.keyWeight, context.innerValueWeight), context)


  method PickKey(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (key:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Cardinality() <= UCardinalityKeys()
    ensures key.UCardinality() <= UCardinalityKeys()
    ensures key.CardinalityKeys() <= UCardinalityKeysKeys()
    ensures key.UCardinalityKeys() <= UCardinalityKeysKeys()
    ensures key.Volume() <= UVolumeKeys()
    ensures key.UVolume() <= UVolumeKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures key.USize(context.keyWeight, context.innerValueWeight) == key.Size(context.keyWeight, context.innerValueWeight)
    ensures key.Size(context.keyWeight, context.innerValueWeight) <= Size(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures key.ULeafBits(context.keyWeight, context.innerValueWeight) <= LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(key.TraversalWork(), 0, context)

  method Count(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (cardinality:nat, ghost counter_out:nat)
    requires Valid()
    ensures cardinality == Cardinality()
    ensures counter_out == counter_in + Cost(1, 0, context)

  method IsEmpty(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + Cost(1, 0, context)

  method Copy(ghost counter_in:nat, ghost context:NestedMapContext<K,V,R>) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeysKeys() == CardinalityKeysKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.UCardinalityKeysKeys() <= UCardinalityKeysKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures result.Size(context.keyWeight, context.innerValueWeight, context.valueWeight) == Size(context.keyWeight, context.innerValueWeight,
        context.valueWeight) && result.USize(context.keyWeight, context.innerValueWeight, context.valueWeight) == Size(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
    ensures counter_out == counter_in + Cost(TraversalWork(), 0, context)

  // Complexity bounds

  lemma u_leaf_bits_bound(bits:nat, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:R -> nat)
    requires 1 <= bits
    requires forall item | item in Universe() :: (child => MaxLeafBits_map_set_t(child, keyWeight, innerValueWeight))(item) <= bits && valueWeight(Universe()[item]) <= bits
    ensures ULeafBits(keyWeight, innerValueWeight, valueWeight) <= bits
  {
    max_leaf_bits_bound_map(Universe(), child => MaxLeafBits_map_set_t(child, keyWeight, innerValueWeight), valueWeight, bits);
  }

  lemma u_size_bound(volume:nat, bits:nat, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:R -> nat)
    requires UVolume() <= volume && ULeafBits(keyWeight, innerValueWeight, valueWeight) <= bits && 1 <= bits
    ensures USize(keyWeight, innerValueWeight, valueWeight) <= StructuralSize(volume, bits)
  {
    structural_size_monotonic(UVolume(), ULeafBits(keyWeight, innerValueWeight, valueWeight), volume, bits);
  }

  lemma {:isolate_assertions} universe_within_bound(U:Map_MapSet_T<K, V, R>, context:NestedMapContext<K,V,R>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures CardinalityKeys() <= UCardinalityKeys() <= U.CardinalityKeys() <= U.UCardinalityKeys()
    ensures CardinalityKeysKeys() <= UCardinalityKeysKeys() <= U.CardinalityKeysKeys() <= U.UCardinalityKeysKeys()
    ensures Volume() <= UVolume() <= U.Volume() <= U.UVolume()
    ensures VolumeKeys() <= UVolumeKeys() <= U.VolumeKeys() <= U.UVolumeKeys()
    ensures VolumeKeysKeys() <= UVolumeKeysKeys() <= U.VolumeKeysKeys() <= U.UVolumeKeysKeys()
    ensures Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= USize(context.keyWeight, context.innerValueWeight,
        context.valueWeight) <= U.Size(context.keyWeight, context.innerValueWeight, context.valueWeight) <= U.USize(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
    ensures LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <= ULeafBits(context.keyWeight, context.innerValueWeight,
        context.valueWeight) <= U.LeafBits(context.keyWeight, context.innerValueWeight, context.valueWeight) <= U.ULeafBits(context.keyWeight,
        context.innerValueWeight, context.valueWeight)
  {
    representation_submap_map_mapset_t(Universe(), U.Model(), context.keyWeight, context.innerValueWeight, context.valueWeight);
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    subset_cardinality_bound_set(Universe().Keys, U.Model().Keys);
    max_by_monotonic(Universe().Keys, U.Model().Keys, item => |item|);
    max_by_monotonic(Universe().Keys, U.Model().Keys, KeyCardinality_map_set_t);
    nonnegative_product_monotonic(UCardinalityKeys(), 1 + UCardinalityKeysKeys(), U.CardinalityKeys(), 1 + U.CardinalityKeysKeys());
    nonnegative_product_monotonic(UCardinality(), 1 + UVolumeKeys(), U.Cardinality(), 1 + U.VolumeKeys());
  }

  lemma u_volume_bound(count:nat, keys:nat, elements:nat)
    requires UCardinality() <= count && UCardinalityKeys() <= keys
    requires UCardinalityKeysKeys() <= elements
    ensures UVolume() <= count*(1+keys*(1+elements))
    ensures UVolumeKeys() <= keys*(1+elements)
    ensures UVolumeKeysKeys() <= elements
  {
    nonnegative_product_monotonic(UCardinalityKeys(), 1 + UCardinalityKeysKeys(), keys, 1 + elements);
    nonnegative_product_monotonic(UCardinality(), 1 + UVolumeKeys(), count, 1 + keys*(1+elements));
  }

  lemma u_cardinality_keys_bound(bound:nat)
    requires forall key | key in Universe().Keys :: |key| <= bound
    ensures UCardinalityKeys() <= bound
  {
    reveal UCardinalityKeys();
    max_by_bound(Universe().Keys, bound, item => |item|);
  }

  lemma u_cardinality_keys_keys_bound(bound:nat)
    requires forall key | key in Universe().Keys ::
      forall question | question in key.Keys :: |question| <= bound
    ensures UCardinalityKeysKeys() <= bound
  {
    reveal UCardinalityKeysKeys();
    max_set_key_cardinality_bound_map_set_t(Universe().Keys, bound);
  }
}


// Construction cost for all map shapes, independent of key and value types
ghost function CostNew_MapFamily():nat
{ CostRepresentation(1, 1, 0) }
