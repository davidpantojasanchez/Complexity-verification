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

  ghost predicate Valid()
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality()
  }

  ghost function Size():nat { Cardinality() }
  ghost function USize():nat { UCardinality() }
  ghost function UCardinality():nat { |Universe()| }

  ghost function Cardinality():(cardinality:nat)
    ensures 0 <= cardinality
  { |Model()| }

  method Get(key:T0, ghost counter_in:nat) returns (value:T1, ghost counter_out:nat)
    requires Valid()
    requires key in Model().Keys
    ensures value == Model()[key]
    ensures counter_out == counter_in + CostGet_Map(this)
    ensures counter_out <= counter_in + UCostGet_Map(this)

  method Insert(key:T0, value:T1, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.Model() == Model()[key := value]
    ensures result.Universe() == Universe()[key := value]
    ensures result.Keys() == Keys() + {key}
    ensures counter_out == counter_in + CostInsert_Map(this)
    ensures counter_out <= counter_in + UCostInsert_Map(this)

  method Remove(key:T0, ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
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

  method PickKey(ghost counter_in:nat) returns (key:T0, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key in Model().Keys
    ensures key in Universe().Keys
    ensures counter_out == counter_in + CostPickKey_Map(this)

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_Map(this)

  method ContainsKey(key:T0, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map(this)

  method IsEmpty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty_Map(this)

  method Copy(ghost counter_in:nat) returns (result:Map<T0, T1>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_Map(this)
    ensures counter_out <= counter_in + UCostCopy_Map(this)
}


// Maps whose keys are maps
trait Map_Map_T<T0(==), T1(==), T2(==)> {
  function Repr():map<map<T0, T1>, T2>
  ghost function {:opaque} Model():map<map<T0, T1>, T2> { Repr() }
  ghost function Universe():map<map<T0, T1>, T2>

  ghost function Keys():set<map<T0, T1>> { Model().Keys }
  ghost function Values():set<T2> { Model().Values }

  // Transparent: existing clients consume representation inclusion directly.
  ghost predicate Valid()
  {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality() &&
    (forall key | key in Universe().Keys :: |key| <= USize_Keys())
  }

  ghost function Size_Keys():nat { MaxCardinality_map(Model().Keys) }
  ghost function Size():nat { Cardinality() * Size_Keys() }
  ghost function USize():nat { UCardinality() * USize_Keys() }
  // Keep universe maxima out of client cost proofs; use the size-bound lemmas.
  ghost function {:opaque} USize_Keys():nat { MaxCardinality_map(Universe().Keys) }
  ghost function UCardinality():nat { |Universe()| }

  ghost function Cardinality():(cardinality:nat)
    ensures 0 <= cardinality
  { |Model()| }

  method Get(key:Map<T0, T1>, ghost counter_in:nat) returns (value:T2, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostGet_Map_Map_T(this)

  method Insert(key:Map<T0, T1>, value:T2, ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
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

  method Remove(key:Map<T0, T1>, ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
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

  method PickKey(ghost counter_in:nat) returns (key:Map<T0, T1>, ghost counter_out:nat)
    requires Model() != map[]
    requires Valid()
    ensures key.Valid()
    ensures key.Size() <= USize_Keys()
    ensures key.USize() <= USize_Keys()
    ensures key.Model() in Model().Keys
    ensures key.Universe() == key.Model()
    ensures counter_out == counter_in + CostPickKey_Map_Map_T(this, key)
    ensures counter_out <= counter_in + UCostPickKey_Map_Map_T(this)

  method Count(ghost counter_in:nat) returns (size:nat, ghost counter_out:nat)
    requires Valid()
    ensures size == Cardinality()
    ensures counter_out == counter_in + CostCount_Map_Map_T(this)

  method ContainsKey(key:Map<T0, T1>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map_Map_T(this)

  method IsEmpty(ghost counter_in:nat) returns (empty:bool, ghost counter_out:nat)
    requires Valid()
    ensures empty == (Model() == map[])
    ensures counter_out == counter_in + CostIsEmpty_Map_Map_T(this)

  method Copy(ghost counter_in:nat) returns (result:Map_Map_T<T0, T1, T2>, ghost counter_out:nat)
    requires Valid()
    ensures result.Valid()
    ensures result.USize_Keys() == Size_Keys()
    ensures result.USize_Keys() <= USize_Keys()
    ensures result.Model() == Model()
    ensures result.Universe() == Model()
    ensures counter_out == counter_in + CostCopy_Map_Map_T(this)
    ensures counter_out <= counter_in + UCostCopy_Map_Map_T(this)
}


// Maps whose keys are sets
trait Map_Set_T<K(==), V(==)> {
  function Repr():map<set<K>, V>
  ghost function {:opaque} Model():map<set<K>, V> { Repr() }
  ghost function Universe():map<set<K>, V>
  ghost function Cardinality():nat { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  ghost function Size_Keys():nat { MaxCardinality_set(Model().Keys) }
  // Keep universe maxima out of client cost proofs; use the size-bound lemmas.
  ghost function {:opaque} USize_Keys():nat { MaxCardinality_set(Universe().Keys) }
  ghost function Size():nat { Cardinality() * Size_Keys() }
  ghost function USize():nat { UCardinality() * USize_Keys() }
  // Quantified representation facts are exposed through explicit connection lemmas.
  ghost predicate {:opaque} Valid() {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality() &&
    (forall key | key in Universe().Keys :: |key| <= USize_Keys())
  }

  method Get(key:Set<K>, ghost counter_in:nat) returns (value:V, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet_Map_Set_T(this)
    ensures counter_out <= counter_in + UCostGet_Map_Set_T(this)

  method ContainsKey(key:Set<K>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map_Set_T(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map_Set_T(this)

  method Insert(key:Set<K>, value:V, ghost counter_in:nat) returns (result:Map_Set_T<K, V>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.USize_Keys() == (if key.Size0() <= USize_Keys() then USize_Keys() else key.Size0())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert_Map_Set_T(this)
    ensures counter_out <= counter_in + UCostInsert_Map_Set_T(this)

}


// Maps whose keys are maps whose keys are sets
trait Map_MapSet_T<K(==), V(==), R(==)> {
  function Repr():map<map<set<K>, V>, R>
  ghost function {:opaque} Model():map<map<set<K>, V>, R> { Repr() }
  ghost function Universe():map<map<set<K>, V>, R>
  ghost function Cardinality():nat { |Model()| }
  ghost function UCardinality():nat { |Universe()| }
  ghost function Size_Keys():nat { MaxCardinality_map(Model().Keys) }
  // Both universe maxima stay behind the explicit size-bound lemmas.
  ghost function {:opaque} USize_Keys():nat { MaxCardinality_map(Universe().Keys) }
  ghost function Size_Keys_Keys():nat { MaxSetKeyCardinality_map_set_t(Model().Keys) }
  ghost function {:opaque} USize_Keys_Keys():nat { MaxSetKeyCardinality_map_set_t(Universe().Keys) }
  ghost function Size():nat { Cardinality() * Size_Keys() * Size_Keys_Keys() }
  ghost function USize():nat { UCardinality() * USize_Keys() * USize_Keys_Keys() }
  // Quantified representation facts are exposed through explicit connection lemmas.
  ghost predicate {:opaque} Valid() {
    Model().Keys <= Universe().Keys &&
    (forall key | key in Model().Keys :: Model()[key] == Universe()[key]) &&
    Cardinality() <= UCardinality() &&
    (forall key | key in Universe().Keys :: |key| <= USize_Keys()) &&
    (forall key | key in Universe().Keys :: forall question | question in key.Keys ::
      |question| <= USize_Keys_Keys())
  }

  method Get(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (value:R, ghost counter_out:nat)
    requires Valid()
    requires key.Model() in Model().Keys
    ensures value == Model()[key.Model()]
    ensures counter_out == counter_in + CostGet_Map_MapSet_T(this)
    ensures counter_out <= counter_in + UCostGet_Map_MapSet_T(this)

  method ContainsKey(key:Map_Set_T<K, V>, ghost counter_in:nat) returns (contains:bool, ghost counter_out:nat)
    requires Valid()
    ensures contains == (key.Model() in Model().Keys)
    ensures counter_out == counter_in + CostContainsKey_Map_MapSet_T(this)
    ensures counter_out <= counter_in + UCostContainsKey_Map_MapSet_T(this)

  method Insert(key:Map_Set_T<K, V>, value:R, ghost counter_in:nat) returns (result:Map_MapSet_T<K, V, R>, ghost counter_out:nat)
    requires Valid() && key.Valid()
    ensures result.Valid()
    ensures result.Cardinality() <= Cardinality() + 1
    ensures result.USize_Keys() == (if key.Cardinality() <= USize_Keys() then USize_Keys() else key.Cardinality())
    ensures result.USize_Keys_Keys() == (if key.Size_Keys() <= USize_Keys_Keys() then USize_Keys_Keys() else key.Size_Keys())
    ensures result.Model() == Model()[key.Model() := value]
    ensures result.Universe() == Universe()[key.Model() := value]
    ensures counter_out == counter_in + CostInsert_Map_MapSet_T(this)
    ensures counter_out <= counter_in + UCostInsert_Map_MapSet_T(this)

}


// Maximum key cardinality; the empty family has size zero.
ghost function {:opaque} MaxCardinality_map<K, V>(maps:set<map<K, V>>):(size:nat)
  ensures maps == {} ==> size == 0
  decreases |maps|
{
  if maps == {} then 0 else
    var m :| m in maps;
    var rest := MaxCardinality_map(maps - {m});
    if |m| > rest then |m| else rest
}
// Maximum set-key cardinality across a family of set-keyed maps.
ghost function {:opaque} MaxSetKeyCardinality_map_set_t<K, V>(maps:set<map<set<K>, V>>):(size:nat)
  ensures maps == {} ==> size == 0
  decreases |maps|
{
  if maps == {} then 0 else
    var m :| m in maps;
    var current := MaxCardinality_set(m.Keys);
    var rest := MaxSetKeyCardinality_map_set_t(maps - {m});
    if current > rest then current else rest
}


ghost predicate Init_Map(M:Map)
{
  M.Valid() && M.Model() == M.Universe()
}
ghost predicate Init_Map_Map_T(M:Map_Map_T)
{
  M.Valid() && M.Model() == M.Universe()
}
ghost predicate Init_Map_Set_T(M:Map_Set_T)
{
  M.Valid() && M.Model() == M.Universe()
}
ghost predicate Init_Map_MapSet_T(M:Map_MapSet_T)
{
  M.Valid() && M.Model() == M.Universe()
}


ghost predicate InUniverse_Map(M:Map, U:Map)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
}
ghost predicate InUniverse_Map_Map_T(M:Map_Map_T, U:Map_Map_T)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  M.USize_Keys() <= U.USize_Keys() &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
}
ghost predicate InUniverse_Map_Set_T(M:Map_Set_T, U:Map_Set_T)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  M.USize_Keys() <= U.USize_Keys() &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
}
ghost predicate InUniverse_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
{
  M.Valid() && U.Valid() &&
  M.Universe().Keys <= U.Model().Keys &&
  M.USize_Keys() <= U.USize_Keys() &&
  M.USize_Keys_Keys() <= U.USize_Keys_Keys() &&
  (forall key | key in M.Universe().Keys :: M.Universe()[key] == U.Model()[key])
}


ghost function CostGet_Map<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function UCostGet_Map<K, V>(M:Map<K, V>):nat { M.USize() + 1 }
ghost function CostInsert_Map<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function UCostInsert_Map<K, V>(M:Map<K, V>):nat { M.USize() + 1 }
ghost function CostRemove_Map<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function UCostRemove_Map<K, V>(M:Map<K, V>):nat { M.USize() + 1 }
ghost function CostPickKey_Map<K, V>(M:Map<K, V>):nat { 1 }
ghost function CostCount_Map<K, V>(M:Map<K, V>):nat { 1 }
ghost function CostContainsKey_Map<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function UCostContainsKey_Map<K, V>(M:Map<K, V>):nat { M.USize() + 1 }
ghost function CostIsEmpty_Map<K, V>(M:Map<K, V>):nat { 1 }
ghost function CostCopy_Map<K, V>(M:Map<K, V>):nat { M.Size() + 1 }
ghost function UCostCopy_Map<K, V>(M:Map<K, V>):nat { M.USize() + 1 }
ghost function CostNew_Map():nat { 1 }

ghost function CostGet_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function UCostGet_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.USize() + 1 }
ghost function CostInsert_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function UCostInsert_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.USize() + 1 }
ghost function CostRemove_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function UCostRemove_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.USize() + 1 }
ghost function CostPickKey_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>, key:Map<K, V>):nat
{ key.Size() + 1 }
ghost function UCostPickKey_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.USize_Keys() + 1 }
ghost function CostCount_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat { 1 }
ghost function CostContainsKey_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.Size() + 1 }
ghost function UCostContainsKey_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.USize() + 1 }
ghost function CostIsEmpty_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat { 1 }
ghost function CostCopy_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat { M.Size() + 1 }
ghost function UCostCopy_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>):nat
{ M.USize() + 1 }
ghost function CostNew_Map_Map_T():nat { 1 }


ghost function CostGet_Map_Set_T<K, V>(M:Map_Set_T<K, V>):nat { M.Size() + 1 }
ghost function UCostGet_Map_Set_T<K, V>(M:Map_Set_T<K, V>):nat { M.USize() + 1 }

ghost function CostContainsKey_Map_Set_T<K, V>(M:Map_Set_T<K, V>):nat { M.Size() + 1 }
ghost function UCostContainsKey_Map_Set_T<K, V>(M:Map_Set_T<K, V>):nat { M.USize() + 1 }

ghost function CostInsert_Map_Set_T<K, V>(M:Map_Set_T<K, V>):nat { M.Size() + 1 }
ghost function UCostInsert_Map_Set_T<K, V>(M:Map_Set_T<K, V>):nat { M.USize() + 1 }

ghost function CostNew_Map_Set_T():nat { 1 }


ghost function CostGet_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.Size() + 1 }
ghost function UCostGet_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.USize() + 1 }

ghost function CostContainsKey_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.Size() + 1 }
ghost function UCostContainsKey_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.USize() + 1 }

ghost function CostInsert_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.Size() + 1 }
ghost function UCostInsert_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>):nat { M.USize() + 1 }

ghost function CostNew_Map_MapSet_T():nat { 1 }
