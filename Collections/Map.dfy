include "../Lemmas/NativeCollectionLemmas.dfy"
include "Set.dfy"
/*
Traits for immutable maps
Concrete implementations are defined in ConcreteMap.dfy.
*/

trait MapFamily<K, V> {
  ghost function Model():map<K, V>
  ghost function Universe():map<K, V>

  ghost function Keys():set<K> { Model().Keys }
  ghost function Values():set<V> { Model().Values }

  ghost predicate Valid()
    ensures Valid() ==> Model().Keys <= Universe().Keys
    ensures Valid() ==> (forall key | key in Model().Keys :: Model()[key] == Universe()[key])

  ghost predicate Init() {
    Valid() && Model() == Universe()
  }

  ghost predicate UniverseWithin(reference:MapFamily<K, V>) {
    Valid() && reference.Valid() && Universe().Keys <= reference.Model().Keys &&
    (forall key | key in Universe().Keys :: Universe()[key] == reference.Model()[key])
  }

  lemma universe_within_transitive(middle:MapFamily<K, V>, reference:MapFamily<K, V>)
    requires UniverseWithin(middle)
    requires middle.UniverseWithin(reference)
    ensures UniverseWithin(reference)
  {}

  ghost function Size():nat
  ghost function USize():nat

  ghost function CostGet():nat { Size() + 1 }
  ghost function UCostGet():nat { USize() + 1 }
  ghost function CostInsert():nat { Size() + 1 }
  ghost function UCostInsert():nat { USize() + 1 }
  ghost function CostContainsKey():nat { Size() + 1 }
  ghost function UCostContainsKey():nat { USize() + 1 }
  ghost function CostCount():nat { 1 }
  ghost function CostIsEmpty():nat { 1 }
  ghost function CostCopy():nat { Size() + 1 }
  ghost function UCostCopy():nat { USize() + 1 }
  ghost function CostRemove():nat { Size() + 1 }
  ghost function UCostRemove():nat { USize() + 1 }
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
    Size() <= USize()
  }

  ghost function Size():nat { Cardinality() }
  ghost function USize():nat { UCardinality() }

  ghost function Cardinality():(cardinality:nat) { |Model()| }
  ghost function UCardinality():nat { |Universe()| }

  method Get(key:T0, ghost counter_in:nat) returns (value:T1, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()

  method Insert(key:T0, value:T1, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures counter_out == counter_in + CostInsert()
    ensures counter_out <= counter_in + UCostInsert()

  method Remove(key:T0, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
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

  method PickKey(ghost counter_in:nat) returns (key:T0, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + CostPickKey()

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()

  method ContainsKey(key:T0, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()

  method IsEmpty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()

  method Copy(ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()

  ghost function CostPickKey():nat { 1 }

  // Complexity bounds

  lemma universe_within_bound(U:Map<T0, T1>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures Size() <= USize() <= U.Size() <= U.USize()
  {
    map_items_inclusion(Universe(), U.Model());
    subset_cardinality_bound(Universe().Keys, U.Model().Keys);
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
    Size() <= USize() &&
    SizeKeys() <= USizeKeys()
  }

  ghost function Size():nat { Cardinality() * CardinalityKeys() }
  ghost function USize():nat { UCardinality() * UCardinalityKeys() }
  ghost function SizeKeys():nat { CardinalityKeys() }
  ghost function USizeKeys():nat { UCardinalityKeys() }

  ghost function Cardinality():(cardinality:nat) { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  ghost function CardinalityKeys():nat { MaxCardinality_map(Model().Keys) }
  ghost function {:opaque} UCardinalityKeys():nat { MaxCardinality_map(Universe().Keys) }

  method Get(key:Map<T0, T1>, ghost counter_in:nat) returns (value:T2, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()

  method Insert(key:Map<T0, T1>, value:T2, ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
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

  method Remove(key:Map<T0, T1>, ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
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

  method PickKey(ghost counter_in:nat) returns (key:Map<T0, T1>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= UCardinalityKeys()
    ensures key.USize() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + CostPickKey(key)
    ensures counter_out <= counter_in + UCostPickKey()

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()

  method ContainsKey(key:Map<T0, T1>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()

  method IsEmpty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()

  method Copy(ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()

  ghost function CostPickKey(key:Map<T0, T1>):nat { key.Size() + 1 }
  ghost function UCostPickKey():nat { UCardinalityKeys() + 1 }

  // Complexity bounds

  lemma universe_within_bound(U:Map_Map_T<T0, T1, T2>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures CardinalityKeys() <= UCardinalityKeys() <= U.CardinalityKeys() <= U.UCardinalityKeys()
    ensures Size() <= USize() <= U.Size() <= U.USize()
    ensures SizeKeys() <= USizeKeys() <= U.SizeKeys() <= U.USizeKeys()
  {
    reveal UCardinalityKeys();
    map_items_inclusion(Universe(), U.Model());
    subset_cardinality_bound(Universe().Keys, U.Model().Keys);
    max_by_monotonic(Universe().Keys, U.Model().Keys, item => |item|);
    nonnegative_product_monotonic(UCardinality(), UCardinalityKeys(), U.Cardinality(), U.CardinalityKeys());
  }

  lemma u_size_bound(count:nat, key:nat)
    requires Valid()
    requires UCardinality() <= count && UCardinalityKeys() <= key
    ensures Cardinality() <= UCardinality()
    ensures USize() <= count * key
  {
    nonnegative_product_monotonic(UCardinality(), UCardinalityKeys(), count, key);
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
    Size() <= USize() &&
    SizeKeys() <= USizeKeys()
  }

  ghost function Size():nat { Cardinality() * CardinalityKeys() }
  ghost function USize():nat { UCardinality() * UCardinalityKeys() }
  ghost function SizeKeys():nat { CardinalityKeys() }
  ghost function USizeKeys():nat { UCardinalityKeys() }

  ghost function Cardinality():nat { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  ghost function CardinalityKeys():nat { MaxCardinality_set(Model().Keys) }
  ghost function {:opaque} UCardinalityKeys():nat { MaxCardinality_set(Universe().Keys) }

  method Get(key:Set<K>, ghost counter_in:nat) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()

  method ContainsKey(key:Set<K>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()

  method Insert(key:Set<K>, value:V, ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Size() <= UCardinalityKeys() then UCardinalityKeys() else key.Size())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert()
    ensures counter_out <= counter_in + UCostInsert()

  method Remove(key:Set<K>, ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
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

  method PickKey(ghost counter_in:nat) returns (key:Set<K>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= UCardinalityKeys()
    ensures key.USize() <= UCardinalityKeys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + CostPickKey(key)
    ensures counter_out <= counter_in + UCostPickKey()

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()

  method IsEmpty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()

  method Copy(ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.UCardinalityKeys() == CardinalityKeys()
    ensures result.UCardinalityKeys() <= UCardinalityKeys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy()
    ensures counter_out <= counter_in + UCostCopy()

  ghost function CostPickKey(key:Set<K>):nat { key.Size() + 1 }
  ghost function UCostPickKey():nat { UCardinalityKeys() + 1 }

  // Complexity bounds

  lemma universe_within_bound(U:Map_Set_T<K, V>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures CardinalityKeys() <= UCardinalityKeys() <= U.CardinalityKeys() <= U.UCardinalityKeys()
    ensures Size() <= USize() <= U.Size() <= U.USize()
    ensures SizeKeys() <= USizeKeys() <= U.SizeKeys() <= U.USizeKeys()
    ensures UCostGet() <= U.CostGet()
    ensures UCostContainsKey() <= U.CostContainsKey()
    ensures UCostInsert() <= U.CostInsert()
  {
    reveal UCardinalityKeys();
    map_items_inclusion(Universe(), U.Model());
    subset_cardinality_bound(Universe().Keys, U.Model().Keys);
    max_by_monotonic(Universe().Keys, U.Model().Keys, item => |item|);
    nonnegative_product_monotonic(UCardinality(), UCardinalityKeys(), U.Cardinality(), U.CardinalityKeys());
  }

  lemma u_size_bound(count:nat, key:nat)
    requires Valid()
    requires UCardinality() <= count && UCardinalityKeys() <= key
    ensures Cardinality() <= UCardinality()
    ensures USize() <= count*key
  {
    nonnegative_product_monotonic(UCardinality(), UCardinalityKeys(), count, key);
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
    Size() <= USize() &&
    SizeKeys() <= USizeKeys() &&
    SizeKeysKeys() <= USizeKeysKeys()
  }

  ghost function Size():nat { Cardinality() * SizeKeys() }
  ghost function USize():nat { UCardinality() * USizeKeys() }
  ghost function SizeKeys():nat { CardinalityKeys() * CardinalityKeysKeys() }
  ghost function USizeKeys():nat { UCardinalityKeys() * UCardinalityKeysKeys() }
  ghost function SizeKeysKeys():nat { CardinalityKeysKeys() }
  ghost function USizeKeysKeys():nat { UCardinalityKeysKeys() }
  
  ghost function Cardinality():nat { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  ghost function CardinalityKeys():nat { MaxCardinality_map(Model().Keys) }
  ghost function {:opaque} UCardinalityKeys():nat { MaxCardinality_map(Universe().Keys) }
  ghost function CardinalityKeysKeys():nat { MaxSetKeyCardinality_map_set_t(Model().Keys) }
  ghost function {:opaque} UCardinalityKeysKeys():nat { MaxSetKeyCardinality_map_set_t(Universe().Keys) }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet()
    ensures counter_out <= counter_in + UCostGet()

  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey()
    ensures counter_out <= counter_in + UCostContainsKey()

  method Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.UCardinalityKeys() == (if key.Cardinality() <= UCardinalityKeys() then UCardinalityKeys() else key.Cardinality())
    ensures result.UCardinalityKeysKeys() == (if key.CardinalityKeys() <= UCardinalityKeysKeys() then UCardinalityKeysKeys() else key.CardinalityKeys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert()
    ensures counter_out <= counter_in + UCostInsert()

  method Remove(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
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

  method PickKey(ghost counter_in:nat) returns (key:Map_Set_T<K, V>, ghost counter_out:nat)
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

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount()

  method IsEmpty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty()

  method Copy(ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
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

  ghost function CostPickKey(key:Map_Set_T<K, V>):nat { key.Size() + 1 }
  ghost function UCostPickKey():nat { USizeKeys() + 1 }

  // Complexity bounds

  lemma universe_within_bound(U:Map_MapSet_T<K, V, R>)
    requires UniverseWithin(U)
    ensures Universe().Keys <= U.Model().Keys
    ensures forall key | key in Universe().Keys :: Universe()[key] == U.Model()[key]
    ensures Cardinality() <= UCardinality() <= U.Cardinality() <= U.UCardinality()
    ensures CardinalityKeys() <= UCardinalityKeys() <= U.CardinalityKeys() <= U.UCardinalityKeys()
    ensures CardinalityKeysKeys() <= UCardinalityKeysKeys() <= U.CardinalityKeysKeys() <= U.UCardinalityKeysKeys()
    ensures Size() <= USize() <= U.Size() <= U.USize()
    ensures SizeKeys() <= USizeKeys() <= U.SizeKeys() <= U.USizeKeys()
    ensures SizeKeysKeys() <= USizeKeysKeys() <= U.SizeKeysKeys() <= U.USizeKeysKeys()
    ensures UCostGet() <= U.CostGet()
    ensures UCostContainsKey() <= U.CostContainsKey()
    ensures UCostInsert() <= U.CostInsert()
  {
    reveal UCardinalityKeys(), UCardinalityKeysKeys();
    map_items_inclusion(Universe(), U.Model());
    subset_cardinality_bound(Universe().Keys, U.Model().Keys);
    max_by_monotonic(Universe().Keys, U.Model().Keys, item => |item|);
    max_by_monotonic(Universe().Keys, U.Model().Keys, SetKeyCardinality);
    nonnegative_product_monotonic(UCardinalityKeys(), UCardinalityKeysKeys(), U.CardinalityKeys(), U.CardinalityKeysKeys());
    nonnegative_product_monotonic(UCardinality(), USizeKeys(), U.Cardinality(), U.SizeKeys());
  }

  lemma u_size_bound(count:nat, keys:nat, elements:nat)
    requires Valid()
    requires UCardinality() <= count && UCardinalityKeys() <= keys
    requires UCardinalityKeysKeys() <= elements
    ensures USize() <= count*keys*elements
    ensures USizeKeys() <= keys*elements
    ensures USizeKeysKeys() <= elements
  {
    nonnegative_product_monotonic(UCardinalityKeys(), UCardinalityKeysKeys(), keys, elements);
    nonnegative_product_monotonic(UCardinality(), USizeKeys(), count, keys*elements);
    multiplication_associative(count, keys, elements);
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
ghost function CostNew_MapFamily():nat { 1 }
