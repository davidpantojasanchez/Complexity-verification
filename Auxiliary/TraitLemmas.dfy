include "Set.dfy"
include "Map.dfy"
include "ArithmeticLemmas.dfy"
include "NativeCollectionLemmas.dfy"

// -----------------------------------------------------------------------------
// Set: model bounds and fixed reference universes
// -----------------------------------------------------------------------------

// Relate a flat set model to its own universe; use after Valid().
lemma ModelSizeBound_Set<T>(S:Set<T>)
  requires S.Valid()
  ensures S.Cardinality() <= S.UCardinality()
  ensures S.Size0() <= S.USize0()
{}

// Transfer flat set measures and costs from a fixed reference universe.
lemma InUniverseBounds_Set(S:Set, U:Set)
requires InUniverse_Set(S, U)
ensures S.Size0() <= U.Size0()
ensures S.USize0() <= U.USize0()
ensures S.UCardinality() <= U.UCardinality()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UCardinality() <= U.Cardinality()
ensures S.USize0() <= U.Size0()
{
  SubsetCardinalityBound(S.Model(), U.Model());
  SubsetCardinalityBound(S.Universe(), U.Universe());
  SubsetCardinalityBound(S.Universe(), U.Model());
}

// Compose two fixed-universe relations for flat sets.
lemma InUniverseTransitive_Set(S:Set, middle:Set, U:Set)
  requires InUniverse_Set(S, middle)
  requires InUniverse_Set(middle, U)
  ensures InUniverse_Set(S, U)
{}

// -----------------------------------------------------------------------------
// SetSet: model, numeric universe and update bounds
// -----------------------------------------------------------------------------

// Relate a set-family model and member maximum to its own universe.
lemma ModelSizeBound_SetSet<T>(S:SetSet<T>)
  requires S.Valid()
  ensures S.Cardinality() <= S.UCardinality()
  ensures S.Size1() <= S.USize1()
  ensures S.Size0() <= S.USize0()
{
  reveal S.USize1();
  MaxCardinalityMonotonic_set(S.Model(), S.Universe());
  NatMultiplicationMonotonic(S.Cardinality(), S.Size1(), S.USize1());
  NatMultiplicationMonotonic(S.USize1(), S.Cardinality(), S.UCardinality());
}

// Convert a uniform universe-member bound into USize1.
lemma UniverseMemberSizeBound_SetSet<T>(S:SetSet<T>, bound:nat)
  requires S.Valid()
  requires forall s | s in S.Universe() :: |s| <= bound
  ensures S.USize1() <= bound
{
  reveal S.USize1();
  MaxCardinalityBound_set(S.Universe(), bound);
}

// Bound universe members by a containing native universe.
lemma UniverseSubsetSizeBound_SetSet<T>(S:SetSet<T>, universe:set<T>)
  requires S.Valid()
  requires forall s | s in S.Universe() :: s <= universe
  ensures S.USize1() <= |universe|
{
  forall s | s in S.Universe()
    ensures |s| <= |universe|
  {
    SubsetCardinalityBound(s, universe);
  }
  UniverseMemberSizeBound_SetSet(S, |universe|);
}

// Build universe size bounds from independent family and member bounds.
lemma UniverseSizeBound_SetSet<T>(S:SetSet<T>, count:nat, member:nat)
  requires S.Valid()
  requires S.UCardinality() <= count && S.USize1() <= member
  ensures S.USize0() <= count*member
{
  MultiplicationPreservesOrder(S.UCardinality(), S.USize1(), count, member);
}

// Propagate universe measures through persistent Add.
lemma AddUniverseMeasures_SetSet<T>(before:SetSet<T>, result:SetSet<T>, element:Set<T>)
  requires result.Universe() == before.Universe() + {element.Model()}
  ensures result.USize1() ==
    (if element.Size0() <= before.USize1() then before.USize1() else element.Size0())
{
  reveal before.USize1(), result.USize1();
  MaxCardinalityInsert_set(before.Universe(), element.Model());
}

// Transfer SetSet measures and costs from a reference universe.
lemma InUniverseBounds_SetSet(S:SetSet, U:SetSet)
requires InUniverse_SetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.USize0() <= U.USize0()
ensures S.UCardinality() <= U.UCardinality()
ensures S.UCardinality() * S.USize1() <= U.UCardinality() * U.USize1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UCardinality() <= U.Cardinality()
ensures S.USize0() <= U.Size0()
ensures S.USize1() <= U.Size1()
{
  reveal S.USize1(), U.USize1();
  MaxCardinalityMonotonic_set(S.Model(), U.Model());
  MaxCardinalityMonotonic_set(S.Universe(), U.Model());
  SubsetCardinalityBound(S.Model(), U.Model());
  SubsetCardinalityBound(S.Universe(), U.Universe());
  MultiplicationPreservesOrder(S.Cardinality(),S.Size1(),U.Cardinality(), U.Size1());
  MultiplicationPreservesOrder(S.UCardinality(),S.USize1(),U.UCardinality(), U.USize1());
  SubsetCardinalityBound(S.Universe(), U.Model());
  MultiplicationPreservesOrder(S.UCardinality(), S.USize1(), U.Cardinality(), U.Size1());
}

// Compose two SetSet reference-universe relations.
lemma InUniverseTransitive_SetSet(S:SetSet, middle:SetSet, U:SetSet)
  requires InUniverse_SetSet(S, middle)
  requires InUniverse_SetSet(middle, U)
  ensures InUniverse_SetSet(S, U)
{}

// -----------------------------------------------------------------------------
// SetSetSet: model, nested universe and update bounds
// -----------------------------------------------------------------------------

// Relate all nested model measures to the wrapper universe.
lemma ModelSizeBound_SetSetSet<T>(S:SetSetSet<T>)
  requires S.Valid()
  ensures S.Cardinality() <= S.UCardinality()
  ensures S.Size1() <= S.USize1()
  ensures S.Size2() <= S.USize2()
  ensures S.Size0() <= S.USize0()
{
  reveal S.USize1(), S.USize2();
  MaxSizeMonotonic_setset(S.Model(), S.Universe());
  MaxMemberCardinalityMonotonic_setset(S.Model(), S.Universe());
  NatMultiplicationMonotonic(S.Cardinality(), S.Size1(), S.USize1());
  NatMultiplicationMonotonic(S.USize1(), S.Cardinality(), S.UCardinality());
}

// Bound immediately nested member size from a uniform bound.
lemma UniverseMemberSizeBound_SetSetSet<T>(S:SetSetSet<T>, bound:nat)
  requires S.Valid()
  requires forall s | s in S.Universe() :: |s| * MaxCardinality_set(s) <= bound
  ensures S.USize1() <= bound
{
  reveal S.USize1();
  MaxSizeBound_setset(S.Universe(), bound);
}

// Bound lowest-level set cardinality from a uniform leaf bound.
lemma UniverseLeafSizeBound_SetSetSet<T>(S:SetSetSet<T>, bound:nat)
  requires S.Valid()
  requires forall s | s in S.Universe() :: MaxCardinality_set(s) <= bound
  ensures S.USize2() <= bound
{
  reveal S.USize2();
  MaxMemberCardinalityBound_setset(S.Universe(), bound);
}

// Build all nested universe bounds from independent numeric bounds.
lemma UniverseSizeBound_SetSetSet<T>(S:SetSetSet<T>, count:nat, member:nat)
  requires S.Valid()
  requires S.UCardinality() <= count && S.USize1() <= member
  ensures S.USize0() <= count * member
{
  MultiplicationPreservesOrder(S.UCardinality(), S.USize1(), count, member);
}

// Propagate both nested universe measures through persistent Add.
lemma AddUniverseMeasures_SetSetSet<T>(before:SetSetSet<T>, result:SetSetSet<T>, element:SetSet<T>)
  requires result.Universe() == before.Universe() + {element.Model()}
  ensures result.USize1() ==
    (if element.Size0() <= before.USize1() then before.USize1() else element.Size0())
  ensures result.USize2() ==
    (if element.Size1() <= before.USize2() then before.USize2() else element.Size1())
{
  reveal before.USize1(), result.USize1(), before.USize2(), result.USize2();
  MaxSizeInsert_setset(before.Universe(), element.Model());
  MaxMemberCardinalityInsert_setset(before.Universe(), element.Model());
}

// Transfer all nested measures and costs from a reference universe.
lemma InUniverseBounds_SetSetSet(S:SetSetSet, U:SetSetSet)
requires InUniverse_SetSetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.USize0() <= U.USize0()
ensures S.UCardinality() <= U.UCardinality()
ensures S.UCardinality() * S.USize1() <= U.UCardinality() * U.USize1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UCardinality() <= U.Cardinality()
ensures S.USize0() <= U.Size0()
ensures S.USize1() <= U.Size1()
ensures S.USize2() <= U.Size2()
{
  reveal S.USize1(), S.USize2(), U.USize1(), U.USize2();
  MaxSizeMonotonic_setset(S.Model(), U.Model());
  MaxSizeMonotonic_setset(S.Universe(), U.Model());
  MaxMemberCardinalityMonotonic_setset(S.Universe(), U.Model());
  SubsetCardinalityBound(S.Model(), U.Model());
  SubsetCardinalityBound(S.Universe(), U.Universe());
  MultiplicationPreservesOrder(S.Cardinality(),S.Size1(),U.Cardinality(), U.Size1());
  MultiplicationPreservesOrder(S.UCardinality(),S.USize1(),U.UCardinality(), U.USize1());
  SubsetCardinalityBound(S.Universe(), U.Model());
  MultiplicationPreservesOrder(S.UCardinality(), S.USize1(), U.Cardinality(), U.Size1());
}

// Compose two SetSetSet reference-universe relations.
lemma InUniverseTransitive_SetSetSet(S:SetSetSet, middle:SetSetSet, U:SetSetSet)
  requires InUniverse_SetSetSet(S, middle)
  requires InUniverse_SetSetSet(middle, U)
  ensures InUniverse_SetSetSet(S, U)
{}

// -----------------------------------------------------------------------------
// Map: model bounds and fixed reference universes
// -----------------------------------------------------------------------------

// Relate a flat map model to its own universe measures.
lemma ModelSizeBound_Map<K, V>(M:Map<K, V>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.Size() <= M.USize()
{}

// Transfer flat-map measures and costs from a reference universe.
lemma InUniverseBounds_Map(M:Map, U:Map)
  requires InUniverse_Map(M, U)
  ensures M.Size() <= U.Size()
  ensures M.USize() <= U.USize()
  ensures M.UCardinality() <= U.UCardinality()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.Cardinality()
  ensures M.USize() <= U.Size()
{
  reveal M.Valid();
  reveal U.Valid();
  SubsetCardinalityBound(M.Model().Keys, M.Universe().Keys);
  SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  SubsetCardinalityBound(U.Model().Keys, U.Universe().Keys);
}

// Compose flat-map universe relations while preserving bindings.
lemma InUniverseTransitive_Map(M:Map, middle:Map, U:Map)
  requires InUniverse_Map(M, middle)
  requires InUniverse_Map(middle, U)
  ensures InUniverse_Map(M, U)
{
  forall key | key in M.Universe().Keys
    ensures M.Universe()[key] == U.Model()[key]
  {
    assert key in middle.Model().Keys;
    assert key in middle.Universe().Keys;
  }
}

// -----------------------------------------------------------------------------
// Map_Map_T: native-map keys
// -----------------------------------------------------------------------------

// Relate model cardinality and native-map key size to the universe.
lemma ModelSizeBound_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.Size_Keys() <= M.USize_Keys()
  ensures M.Size() <= M.USize()
{
  reveal M.USize_Keys();
  MaxCardinalityMonotonic_map(M.Model().Keys, M.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.Size_Keys(), M.UCardinality(), M.USize_Keys());
}

// Convert a uniform native-map key bound into USize_Keys.
lemma UniverseKeySizeBound_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>, bound:nat)
  requires forall key | key in M.Universe().Keys :: |key| <= bound
  ensures M.USize_Keys() <= bound
{
  reveal M.USize_Keys();
  MaxCardinalityBound_map(M.Universe().Keys, bound);
}

// Build universe bounds from independent count and key-size bounds.
lemma UniverseSizeBound_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>, count:nat, key:nat)
  requires M.Valid()
  requires M.UCardinality() <= count && M.USize_Keys() <= key
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.USize() <= count * key
{
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), count, key);
}

// Propagate universe measures through persistent Insert.
lemma InsertUniverseMeasures_Map_Map_T<K, V, R>(
    before:Map_Map_T<K, V, R>, result:Map_Map_T<K, V, R>, key:Map<K, V>, value:R)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.USize_Keys() ==
    (if key.Size() <= before.USize_Keys() then before.USize_Keys() else key.Size())
{
  reveal before.USize_Keys(), result.USize_Keys();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  MaxCardinalityInsert_map(before.Universe().Keys, key.Model());
}

// Transfer measures, costs and bindings from a reference universe.
lemma InUniverseBounds_Map_Map_T(M:Map_Map_T, U:Map_Map_T)
  requires InUniverse_Map_Map_T(M, U)
  ensures M.USize_Keys() <= U.Size_Keys()
  ensures M.Size() <= U.Size()
  ensures M.USize() <= U.USize()
  ensures M.USize_Keys() <= U.USize_Keys()
  ensures M.UCardinality() <= U.UCardinality()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.Cardinality()
  ensures M.USize() <= U.Size()
{
  reveal M.Valid();
  reveal U.Valid();
  SubsetCardinalityBound(M.Model().Keys, M.Universe().Keys);
  SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  SubsetCardinalityBound(U.Model().Keys, U.Universe().Keys);
  reveal M.USize_Keys(), U.USize_Keys();
  MaxCardinalityMonotonic_map(M.Model().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(M.Universe().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(U.Model().Keys, U.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.Size_Keys(), U.Cardinality(), U.Size_Keys());
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), U.UCardinality(), U.USize_Keys());
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), U.Cardinality(), U.Size_Keys());
}

// Compose two Map_Map_T reference-universe relations.
lemma InUniverseTransitive_Map_Map_T(
    M:Map_Map_T, middle:Map_Map_T, U:Map_Map_T)
  requires InUniverse_Map_Map_T(M, middle)
  requires InUniverse_Map_Map_T(middle, U)
  ensures InUniverse_Map_Map_T(M, U)
{
  reveal middle.Valid();
  assert M.Universe().Keys <= U.Model().Keys;
  forall key | key in M.Universe().Keys
    ensures M.Universe()[key] == U.Model()[key]
  {
    assert key in middle.Model().Keys;
    assert key in middle.Universe().Keys;
  }
}

// -----------------------------------------------------------------------------
// Map_Set_T: native-set keys
// -----------------------------------------------------------------------------

// Relate model cardinality and set-key size to the universe.
lemma ModelSizeBound_Map_Set_T<K, V>(M:Map_Set_T<K, V>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.Size_Keys() <= M.USize_Keys()
  ensures M.Size() <= M.USize()
{
  reveal M.Valid();
  reveal M.USize_Keys();
  MaxCardinalityMonotonic_set(M.Model().Keys, M.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.Size_Keys(), M.UCardinality(), M.USize_Keys());
}

// Convert a uniform set-key bound into USize_Keys.
lemma UniverseKeySizeBound_Map_Set_T<K, V>(M:Map_Set_T<K, V>, bound:nat)
  requires forall key | key in M.Universe().Keys :: |key| <= bound
  ensures M.USize_Keys() <= bound
{
  reveal M.USize_Keys();
  MaxCardinalityBound_set(M.Universe().Keys, bound);
}

// Build universe bounds from independent count and key-size bounds.
lemma UniverseSizeBound_Map_Set_T<K, V>(M:Map_Set_T<K, V>, count:nat, key:nat)
  requires M.Valid()
  requires M.UCardinality() <= count && M.USize_Keys() <= key
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.USize() <= count*key
{
  reveal M.Valid();
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), count, key);
}

// Propagate universe measures through persistent Insert.
lemma InsertUniverseMeasures_Map_Set_T<K, V>(
    before:Map_Set_T<K, V>, result:Map_Set_T<K, V>, key:Set<K>, value:V)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.USize_Keys() ==
    (if key.Size0() <= before.USize_Keys() then before.USize_Keys() else key.Size0())
{
  reveal before.USize_Keys(), result.USize_Keys(), key.Model();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  MaxCardinalityInsert_set(before.Universe().Keys, key.Model());
}

// Transfer measures, costs and bindings from a reference universe.
lemma InUniverseBounds_Map_Set_T(M:Map_Set_T, U:Map_Set_T)
  requires InUniverse_Map_Set_T(M, U)
  ensures M.USize_Keys() <= U.Size_Keys()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.UCardinality()
  ensures M.USize_Keys() <= U.USize_Keys()
  ensures M.Size() <= U.Size()
  ensures M.USize() <= U.Size()
  ensures M.USize() <= U.USize()
  ensures UCostGet_Map_Set_T(M) <= CostGet_Map_Set_T(U)
  ensures UCostContainsKey_Map_Set_T(M) <= CostContainsKey_Map_Set_T(U)
  ensures UCostInsert_Map_Set_T(M) <= CostInsert_Map_Set_T(U)
{
  reveal InUniverse_Map_Set_T();
  reveal M.Valid(), U.Valid();
  ModelSizeBound_Map_Set_T(M);
  ModelSizeBound_Map_Set_T(U);
  SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  reveal M.USize_Keys(), U.USize_Keys();
  MaxCardinalityMonotonic_set(M.Model().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_set(M.Universe().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_set(M.Universe().Keys, U.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.Size_Keys(), U.Cardinality(), U.Size_Keys());
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), U.Cardinality(), U.Size_Keys());
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), U.UCardinality(), U.USize_Keys());
}

// Compose two Map_Set_T reference-universe relations.
lemma InUniverseTransitive_Map_Set_T(M:Map_Set_T, middle:Map_Set_T, U:Map_Set_T)
  requires InUniverse_Map_Set_T(M, middle)
  requires InUniverse_Map_Set_T(middle, U)
  ensures InUniverse_Map_Set_T(M, U)
{
  reveal middle.Valid();
  assert M.Universe().Keys <= U.Model().Keys;
  forall key | key in M.Universe().Keys
    ensures M.Universe()[key] == U.Model()[key]
  {
    assert key in middle.Model().Keys;
    assert key in middle.Universe().Keys;
  }
}

// -----------------------------------------------------------------------------
// Map_MapSet_T: native maps with set-valued keys
// -----------------------------------------------------------------------------

// Relate both nested key measures to the wrapper universe.
lemma ModelSizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.Size_Keys() <= M.USize_Keys()
  ensures M.Size_Keys_Keys() <= M.USize_Keys_Keys()
  ensures M.Size() <= M.USize()
{
  reveal M.Valid();
  reveal M.USize_Keys(), M.USize_Keys_Keys();
  MaxCardinalityMonotonic_map(M.Model().Keys, M.Universe().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Model().Keys, M.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.Size_Keys(), M.UCardinality(), M.USize_Keys());
  MultiplicationPreservesOrder(M.Cardinality()*M.Size_Keys(), M.Size_Keys_Keys(),
    M.UCardinality()*M.USize_Keys(), M.USize_Keys_Keys());
}

// Convert a bound on map-key cardinality into USize_Keys.
lemma UniverseKeySizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>, bound:nat)
  requires forall key | key in M.Universe().Keys :: |key| <= bound
  ensures M.USize_Keys() <= bound
{
  reveal M.USize_Keys();
  MaxCardinalityBound_map(M.Universe().Keys, bound);
}

// Convert a bound on inner set keys into USize_Keys_Keys.
lemma UniverseSetKeySizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>, bound:nat)
  requires forall key | key in M.Universe().Keys ::
    forall question | question in key.Keys :: |question| <= bound
  ensures M.USize_Keys_Keys() <= bound
{
  reveal M.USize_Keys_Keys();
  MaxSetKeyCardinalityBound_map_set_t(M.Universe().Keys, bound);
}

// Build all nested universe bounds from independent numeric bounds.
lemma UniverseSizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>, count:nat, keys:nat, elements:nat)
  requires M.Valid()
  requires M.UCardinality() <= count && M.USize_Keys() <= keys
  requires M.USize_Keys_Keys() <= elements
  ensures M.USize() <= count*keys*elements
{
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), count, keys);
  MultiplicationPreservesOrder(M.UCardinality()*M.USize_Keys(), M.USize_Keys_Keys(), count*keys, elements);
}

// Propagate nested universe measures through persistent Insert.
lemma InsertUniverseMeasures_Map_MapSet_T<K, V, R>(
    before:Map_MapSet_T<K, V, R>, result:Map_MapSet_T<K, V, R>,
    key:Map_Set_T<K, V>, value:R)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.USize_Keys() ==
    (if key.Cardinality() <= before.USize_Keys()
      then before.USize_Keys() else key.Cardinality())
  ensures result.USize_Keys_Keys() ==
    (if key.Size_Keys() <= before.USize_Keys_Keys()
      then before.USize_Keys_Keys() else key.Size_Keys())
{
  reveal before.USize_Keys(), result.USize_Keys();
  reveal before.USize_Keys_Keys(), result.USize_Keys_Keys(), key.Model();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  MaxCardinalityInsert_map(before.Universe().Keys, key.Model());
  MaxSetKeyCardinalityInsert_map_set_t(before.Universe().Keys, key.Model());
}

// Lift native update agreement to wrapper models and universes.
lemma UpdateAgreement_Map_MapSet_T<K, V, R>(
    M:Map_MapSet_T<K, V, R>, key:map<set<K>, V>, value:R)
  requires M.Valid()
  ensures M.Model()[key := value].Keys <= M.Universe()[key := value].Keys
  ensures forall entry {:trigger M.Model()[key := value][entry]} |
    entry in M.Model()[key := value].Keys ::
    M.Model()[key := value][entry] == M.Universe()[key := value][entry]
{
  reveal M.Valid();
  MapUpdateAgreement(M.Model(), M.Universe(), key, value);
}

// Compare nested model sizes through a model-to-model relation.
lemma ModelToModelSizeBound_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires M.Model().Keys <= U.Model().Keys
  ensures M.Size() <= U.Size()
{
  SubsetCardinalityBound(M.Model().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(M.Model().Keys, U.Model().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Model().Keys, U.Model().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.Size_Keys(), U.Cardinality(), U.Size_Keys());
  MultiplicationPreservesOrder(M.Cardinality()*M.Size_Keys(), M.Size_Keys_Keys(),
    U.Cardinality()*U.Size_Keys(), U.Size_Keys_Keys());
}

// Bound a source universe using reference model measures.
lemma UniverseToModelSizeBound_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires M.Universe().Keys <= U.Model().Keys
  ensures M.USize_Keys() <= U.Size_Keys()
  ensures M.USize_Keys_Keys() <= U.Size_Keys_Keys()
  ensures M.USize() <= U.Size()
{
  reveal M.USize_Keys(), M.USize_Keys_Keys();
  SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(M.Universe().Keys, U.Model().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Universe().Keys, U.Model().Keys);
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), U.Cardinality(), U.Size_Keys());
  MultiplicationPreservesOrder(M.UCardinality()*M.USize_Keys(), M.USize_Keys_Keys(),
    U.Cardinality()*U.Size_Keys(), U.Size_Keys_Keys());
}

// Transfer nested universe measures directly between wrappers.
lemma UniverseToUniverseSizeBound_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires M.Universe().Keys <= U.Universe().Keys
  ensures M.USize() <= U.USize()
{
  reveal M.USize_Keys(), U.USize_Keys();
  reveal M.USize_Keys_Keys(), U.USize_Keys_Keys();
  SubsetCardinalityBound(M.Universe().Keys, U.Universe().Keys);
  MaxCardinalityMonotonic_map(M.Universe().Keys, U.Universe().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Universe().Keys, U.Universe().Keys);
  MultiplicationPreservesOrder(M.UCardinality(), M.USize_Keys(), U.UCardinality(), U.USize_Keys());
  MultiplicationPreservesOrder(M.UCardinality()*M.USize_Keys(), M.USize_Keys_Keys(),
    U.UCardinality()*U.USize_Keys(), U.USize_Keys_Keys());
}

// Transfer all measures, costs and bindings from a reference universe.
lemma InUniverseBounds_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires InUniverse_Map_MapSet_T(M, U)
  ensures M.USize_Keys() <= U.Size_Keys()
  ensures M.USize_Keys_Keys() <= U.Size_Keys_Keys()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.UCardinality()
  ensures M.USize_Keys() <= U.USize_Keys()
  ensures M.USize_Keys_Keys() <= U.USize_Keys_Keys()
  ensures M.Size() <= U.Size()
  ensures M.USize() <= U.Size()
  ensures M.USize() <= U.USize()
  ensures UCostGet_Map_MapSet_T(M) <= CostGet_Map_MapSet_T(U)
  ensures UCostContainsKey_Map_MapSet_T(M) <= CostContainsKey_Map_MapSet_T(U)
  ensures UCostInsert_Map_MapSet_T(M) <= CostInsert_Map_MapSet_T(U)
{
  reveal InUniverse_Map_MapSet_T();
  reveal M.Valid(), U.Valid();
  ModelSizeBound_Map_MapSet_T(M);
  ModelSizeBound_Map_MapSet_T(U);
  assert M.Cardinality() <= M.UCardinality() && U.Cardinality() <= U.UCardinality() by {
    reveal M.Valid(), U.Valid();
  }
  assert M.UCardinality() <= U.Cardinality() by {
    SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  }
  assert M.Model().Keys <= U.Model().Keys;
  assert M.Universe().Keys <= U.Universe().Keys;
  ModelToModelSizeBound_Map_MapSet_T(M, U);
  UniverseToModelSizeBound_Map_MapSet_T(M, U);
  UniverseToUniverseSizeBound_Map_MapSet_T(M, U);
}

// Compose two Map_MapSet_T reference-universe relations.
lemma InUniverseTransitive_Map_MapSet_T(M:Map_MapSet_T, middle:Map_MapSet_T, U:Map_MapSet_T)
  requires InUniverse_Map_MapSet_T(M, middle)
  requires InUniverse_Map_MapSet_T(middle, U)
  ensures InUniverse_Map_MapSet_T(M, U)
{
  reveal middle.Valid();
  assert M.Universe().Keys <= U.Model().Keys;
  forall key | key in M.Universe().Keys
    ensures M.Universe()[key] == U.Model()[key]
  {
    assert key in middle.Model().Keys;
    assert key in middle.Universe().Keys;
  }
}
