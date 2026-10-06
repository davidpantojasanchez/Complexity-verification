include "../Collections/Set.dfy"
include "../Collections/Map.dfy"
include "ArithmeticLemmas.dfy"
include "NativeCollectionLemmas.dfy"

// Model bounds
// Relate model cardinalities and derived sizes to the collection universe after Valid().
// Use these variants for Set, SetSet, SetSetSet and all map traits when scalar validity
// does not expose the required nested maxima; flat variants retain the uniform API.

lemma ModelSizeBound_Set<T>(S:Set<T>)
  requires S.Valid()
  ensures S.Cardinality0() <= S.UCardinality0()
  ensures S.Size0() <= S.USize0()
{}

lemma ModelSizeBound_SetSet<T>(S:SetSet<T>)
  requires S.Valid()
  ensures S.Cardinality0() <= S.UCardinality0()
  ensures S.Cardinality1() <= S.UCardinality1()
  ensures S.Size0() <= S.USize0()
{
  reveal S.UCardinality1();
  MaxCardinalityMonotonic_set(S.Model(), S.Universe());
  NatMultiplicationMonotonic(S.Cardinality0(), S.Cardinality1(), S.UCardinality1());
  NatMultiplicationMonotonic(S.UCardinality1(), S.Cardinality0(), S.UCardinality0());
}

lemma ModelSizeBound_SetSetSet<T>(S:SetSetSet<T>)
  requires S.Valid()
  ensures S.Cardinality0() <= S.UCardinality0()
  ensures S.Cardinality1() <= S.UCardinality1()
  ensures S.Cardinality2() <= S.UCardinality2()
  ensures S.Size1() <= S.USize1()
  ensures S.Size2() <= S.USize2()
  ensures S.Size0() <= S.USize0()
{
  reveal S.UCardinality1(), S.UCardinality2();
  MaxCardinalityMonotonic_set(S.Model(), S.Universe());
  MaxMemberCardinalityMonotonic_setset(S.Model(), S.Universe());
  MultiplicationPreservesOrder(S.Cardinality1(), S.Cardinality2(), S.UCardinality1(), S.UCardinality2());
  MultiplicationPreservesOrder(S.Cardinality0(), S.Size1(), S.UCardinality0(), S.USize1());
}

lemma ModelSizeBound_Map<K, V>(M:Map<K, V>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.Size() <= M.USize()
{}

lemma ModelSizeBound_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.CardinalityKeys() <= M.UCardinalityKeys()
  ensures M.Size() <= M.USize()
{
  reveal M.UCardinalityKeys();
  MaxCardinalityMonotonic_map(M.Model().Keys, M.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.CardinalityKeys(), M.UCardinality(), M.UCardinalityKeys());
}

lemma ModelSizeBound_Map_Set_T<K, V>(M:Map_Set_T<K, V>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.CardinalityKeys() <= M.UCardinalityKeys()
  ensures M.Size() <= M.USize()
{
  reveal M.UCardinalityKeys();
  MaxCardinalityMonotonic_set(M.Model().Keys, M.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.CardinalityKeys(), M.UCardinality(), M.UCardinalityKeys());
}

lemma ModelSizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>)
  requires M.Valid()
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.CardinalityKeys() <= M.UCardinalityKeys()
  ensures M.CardinalityKeysKeys() <= M.UCardinalityKeysKeys()
  ensures M.Size() <= M.USize()
  ensures M.SizeKeys() <= M.USizeKeys()
  ensures M.SizeKeysKeys() <= M.USizeKeysKeys()
{
  reveal M.UCardinalityKeys(), M.UCardinalityKeysKeys();
  MaxCardinalityMonotonic_map(M.Model().Keys, M.Universe().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Model().Keys, M.Universe().Keys);
  MultiplicationPreservesOrder(M.CardinalityKeys(), M.CardinalityKeysKeys(), M.UCardinalityKeys(), M.UCardinalityKeysKeys());
  MultiplicationPreservesOrder(M.Cardinality(), M.CardinalityKeys()*M.CardinalityKeysKeys(), M.UCardinality(), M.UCardinalityKeys()*M.UCardinalityKeysKeys());
}

// Uniform content bounds
// Turn bounds on universe members, compound keys or leaves into bounds on opaque
// universe cardinality maxima. Use the applicable SetSet, SetSetSet or nested-map
// variant when the content has a known uniform bound, before composing numeric costs.

lemma UniverseMemberSizeBound_SetSet<T>(S:SetSet<T>, bound:nat)
  requires S.Valid()
  requires forall s | s in S.Universe() :: |s| <= bound
  ensures S.UCardinality1() <= bound
{
  reveal S.UCardinality1();
  MaxCardinalityBound_set(S.Universe(), bound);
}

lemma UniverseMemberSizeBound_SetSetSet<T>(S:SetSetSet<T>, members:nat, leaves:nat)
  requires S.Valid()
  requires forall s | s in S.Universe() :: |s| <= members
  requires forall s | s in S.Universe() :: MaxCardinality_set(s) <= leaves
  ensures S.UCardinality1() <= members
  ensures S.UCardinality2() <= leaves
  ensures S.USize1() <= members*leaves
  ensures S.USize2() <= leaves
{
  reveal S.UCardinality1(), S.UCardinality2();
  MaxCardinalityBound_set(S.Universe(), members);
  MaxMemberCardinalityBound_setset(S.Universe(), leaves);
  UniverseSize1Bound_SetSetSet(S, members, leaves);
}

lemma UniverseLeafSizeBound_SetSetSet<T>(S:SetSetSet<T>, bound:nat)
  requires S.Valid()
  requires forall s | s in S.Universe() :: MaxCardinality_set(s) <= bound
  ensures S.UCardinality2() <= bound
  ensures S.USize2() <= bound
{
  reveal S.UCardinality2();
  MaxMemberCardinalityBound_setset(S.Universe(), bound);
}

lemma UniverseKeySizeBound_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>, bound:nat)
  requires forall key | key in M.Universe().Keys :: |key| <= bound
  ensures M.UCardinalityKeys() <= bound
{
  reveal M.UCardinalityKeys();
  MaxCardinalityBound_map(M.Universe().Keys, bound);
}

lemma UniverseKeySizeBound_Map_Set_T<K, V>(M:Map_Set_T<K, V>, bound:nat)
  requires forall key | key in M.Universe().Keys :: |key| <= bound
  ensures M.UCardinalityKeys() <= bound
{
  reveal M.UCardinalityKeys();
  MaxCardinalityBound_set(M.Universe().Keys, bound);
}

lemma UniverseKeySizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>, bound:nat)
  requires forall key | key in M.Universe().Keys :: |key| <= bound
  ensures M.UCardinalityKeys() <= bound
{
  reveal M.UCardinalityKeys();
  MaxCardinalityBound_map(M.Universe().Keys, bound);
}

lemma UniverseSetKeySizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>, bound:nat)
  requires forall key | key in M.Universe().Keys ::
    forall question | question in key.Keys :: |question| <= bound
  ensures M.UCardinalityKeysKeys() <= bound
{
  reveal M.UCardinalityKeysKeys();
  MaxSetKeyCardinalityBound_map_set_t(M.Universe().Keys, bound);
}

// Numeric size envelopes
// Compose independent cardinality bounds into total or inner universe-size products
// for nested sets and maps. Use these when growing collections lack a fixed reference
// universe; supply a separate bound for each dimension rather than one shared budget.

lemma UniverseSizeBound_SetSet<T>(S:SetSet<T>, count:nat, member:nat)
  requires S.Valid()
  requires S.UCardinality0() <= count && S.UCardinality1() <= member
  ensures S.USize0() <= count*member
{
  MultiplicationPreservesOrder(S.UCardinality0(), S.UCardinality1(), count, member);
}

lemma UniverseSize1Bound_SetSetSet<T>(S:SetSetSet<T>, members:nat, leaves:nat)
  requires S.UCardinality1() <= members && S.UCardinality2() <= leaves
  ensures S.USize1() <= members*leaves
  ensures S.USize2() <= leaves
{
  MultiplicationPreservesOrder(S.UCardinality1(), S.UCardinality2(), members, leaves);
}

lemma UniverseSizeBound_SetSetSet<T>(S:SetSetSet<T>, count:nat, members:nat, leaves:nat)
  requires S.Valid()
  requires S.UCardinality0() <= count && S.UCardinality1() <= members
  requires S.UCardinality2() <= leaves
  ensures S.USize0() <= count*members*leaves
  ensures S.USize1() <= members*leaves
  ensures S.USize2() <= leaves
{
  UniverseSize1Bound_SetSetSet(S, members, leaves);
  MultiplicationPreservesOrder(S.UCardinality0(), S.USize1(), count, members*leaves);
  MultiplicationAssociative(count, members, leaves);
}

lemma UniverseSizeBound_Map_Map_T<K, V, R>(M:Map_Map_T<K, V, R>, count:nat, key:nat)
  requires M.Valid()
  requires M.UCardinality() <= count && M.UCardinalityKeys() <= key
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.USize() <= count * key
{
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys(), count, key);
}

lemma UniverseSizeBound_Map_Set_T<K, V>(M:Map_Set_T<K, V>, count:nat, key:nat)
  requires M.Valid()
  requires M.UCardinality() <= count && M.UCardinalityKeys() <= key
  ensures M.Cardinality() <= M.UCardinality()
  ensures M.USize() <= count*key
{
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys(), count, key);
}

lemma UniverseSizeKeysBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>, keys:nat, elements:nat)
  requires M.UCardinalityKeys() <= keys && M.UCardinalityKeysKeys() <= elements
  ensures M.USizeKeys() <= keys*elements
  ensures M.USizeKeysKeys() <= elements
{
  MultiplicationPreservesOrder(M.UCardinalityKeys(), M.UCardinalityKeysKeys(), keys, elements);
}

lemma UniverseSizeBound_Map_MapSet_T<K, V, R>(M:Map_MapSet_T<K, V, R>, count:nat, keys:nat, elements:nat)
  requires M.Valid()
  requires M.UCardinality() <= count && M.UCardinalityKeys() <= keys
  requires M.UCardinalityKeysKeys() <= elements
  ensures M.USize() <= count*keys*elements
  ensures M.USizeKeys() <= keys*elements
  ensures M.USizeKeysKeys() <= elements
{
  UniverseSizeKeysBound_Map_MapSet_T(M, keys, elements);
  MultiplicationPreservesOrder(M.UCardinality(), M.USizeKeys(), count, keys*elements);
  MultiplicationAssociative(count, keys, elements);
}

// Persistent update measures
// Describe the exact maxima after Add on nested sets or Insert on compound-key maps.
// Use these in concrete implementations or proofs relating an updated universe to its
// previous contents; inserted model measures determine the maxima, not private budgets.

lemma AddUniverseMeasures_SetSet<T>(before:SetSet<T>, result:SetSet<T>, element:Set<T>)
  requires result.Universe() == before.Universe() + {element.Model()}
  ensures result.UCardinality1() ==
    (if element.Size0() <= before.UCardinality1() then before.UCardinality1() else element.Size0())
{
  reveal before.UCardinality1(), result.UCardinality1();
  MaxCardinalityInsert_set(before.Universe(), element.Model());
}

lemma AddUniverseMeasures_SetSetSet<T>(before:SetSetSet<T>, result:SetSetSet<T>, element:SetSet<T>)
  requires result.Universe() == before.Universe() + {element.Model()}
  ensures result.UCardinality1() ==
    (if element.Cardinality0() <= before.UCardinality1() then before.UCardinality1() else element.Cardinality0())
  ensures result.UCardinality2() ==
    (if element.Cardinality1() <= before.UCardinality2() then before.UCardinality2() else element.Cardinality1())
{
  reveal before.UCardinality1(), result.UCardinality1();
  reveal before.UCardinality2(), result.UCardinality2();
  MaxCardinalityInsert_set(before.Universe(), element.Model());
  MaxMemberCardinalityInsert_setset(before.Universe(), element.Model());
}

lemma InsertUniverseMeasures_Map_Map_T<K, V, R>(
    before:Map_Map_T<K, V, R>, result:Map_Map_T<K, V, R>, key:Map<K, V>, value:R)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.UCardinalityKeys() ==
    (if key.Size() <= before.UCardinalityKeys() then before.UCardinalityKeys() else key.Size())
{
  reveal before.UCardinalityKeys(), result.UCardinalityKeys();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  MaxCardinalityInsert_map(before.Universe().Keys, key.Model());
}

lemma InsertUniverseMeasures_Map_Set_T<K, V>(
    before:Map_Set_T<K, V>, result:Map_Set_T<K, V>, key:Set<K>, value:V)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.UCardinalityKeys() ==
    (if key.Size0() <= before.UCardinalityKeys() then before.UCardinalityKeys() else key.Size0())
{
  reveal before.UCardinalityKeys(), result.UCardinalityKeys(), key.Model();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  MaxCardinalityInsert_set(before.Universe().Keys, key.Model());
}

lemma InsertUniverseMeasures_Map_MapSet_T<K, V, R>(
    before:Map_MapSet_T<K, V, R>, result:Map_MapSet_T<K, V, R>,
    key:Map_Set_T<K, V>, value:R)
  requires result.Universe() == before.Universe()[key.Model() := value]
  ensures result.UCardinalityKeys() ==
    (if key.Cardinality() <= before.UCardinalityKeys()
      then before.UCardinalityKeys() else key.Cardinality())
  ensures result.UCardinalityKeysKeys() ==
    (if key.CardinalityKeys() <= before.UCardinalityKeysKeys()
      then before.UCardinalityKeysKeys() else key.CardinalityKeys())
{
  reveal before.UCardinalityKeys(), result.UCardinalityKeys();
  reveal before.UCardinalityKeysKeys(), result.UCardinalityKeysKeys(), key.Model();
  assert result.Universe().Keys == before.Universe().Keys + {key.Model()};
  MaxCardinalityInsert_map(before.Universe().Keys, key.Model());
  MaxSetKeyCardinalityInsert_map_set_t(before.Universe().Keys, key.Model());
}

// Universe inclusion bounds
// Transfer universe cardinalities and derived products through native universe
// inclusion for SetSetSet and Map_MapSet_T. Use when only universe-to-universe
// inclusion is known, without the stronger fixed-reference model relation.

lemma UniverseToUniverseSizeBound_SetSetSet<T>(S:SetSetSet<T>, U:SetSetSet<T>)
  requires S.Universe() <= U.Universe()
  ensures S.UCardinality0() <= U.UCardinality0()
  ensures S.UCardinality1() <= U.UCardinality1()
  ensures S.UCardinality2() <= U.UCardinality2()
  ensures S.USize0() <= U.USize0()
  ensures S.USize1() <= U.USize1()
  ensures S.USize2() <= U.USize2()
{
  reveal S.UCardinality1(), S.UCardinality2();
  reveal U.UCardinality1(), U.UCardinality2();
  SubsetCardinalityBound(S.Universe(), U.Universe());
  MaxCardinalityMonotonic_set(S.Universe(), U.Universe());
  MaxMemberCardinalityMonotonic_setset(S.Universe(), U.Universe());
  MultiplicationPreservesOrder(S.UCardinality1(), S.UCardinality2(), U.UCardinality1(), U.UCardinality2());
  MultiplicationPreservesOrder(S.UCardinality0(), S.USize1(), U.UCardinality0(), U.USize1());
}

lemma UniverseToUniverseSizeBound_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires M.Universe().Keys <= U.Universe().Keys
  ensures M.USize() <= U.USize()
  ensures M.USizeKeys() <= U.USizeKeys()
  ensures M.USizeKeysKeys() <= U.USizeKeysKeys()
{
  reveal M.UCardinalityKeys(), U.UCardinalityKeys();
  reveal M.UCardinalityKeysKeys(), U.UCardinalityKeysKeys();
  SubsetCardinalityBound(M.Universe().Keys, U.Universe().Keys);
  MaxCardinalityMonotonic_map(M.Universe().Keys, U.Universe().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Universe().Keys, U.Universe().Keys);
  MultiplicationPreservesOrder(M.UCardinalityKeys(), M.UCardinalityKeysKeys(), U.UCardinalityKeys(), U.UCardinalityKeysKeys());
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys()*M.UCardinalityKeysKeys(), U.UCardinality(), U.UCardinalityKeys()*U.UCardinalityKeysKeys());
}

// Fixed reference bounds
// Transfer model and universe measures through InUniverse for all seven collection
// traits. Use a stable reference model to bound traversal state and universe-based
// operation costs, preserving map value agreement through the relation.

lemma InUniverseBounds_Set(S:Set, U:Set)
requires InUniverse_Set(S, U)
ensures S.Size0() <= U.Size0()
ensures S.USize0() <= U.USize0()
ensures S.UCardinality0() <= U.UCardinality0()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UCardinality0() <= U.Cardinality0()
ensures S.USize0() <= U.Size0()
{
  SubsetCardinalityBound(S.Model(), U.Model());
  SubsetCardinalityBound(S.Universe(), U.Universe());
  SubsetCardinalityBound(S.Universe(), U.Model());
}

lemma InUniverseBounds_SetSet(S:SetSet, U:SetSet)
requires InUniverse_SetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.USize0() <= U.USize0()
ensures S.UCardinality0() <= U.UCardinality0()
ensures S.UCardinality0() * S.UCardinality1() <= U.UCardinality0() * U.UCardinality1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UCardinality0() <= U.Cardinality0()
ensures S.USize0() <= U.Size0()
ensures S.UCardinality1() <= U.Cardinality1()
  ensures S.Cardinality1() <= U.Cardinality1()
{
  reveal S.UCardinality1(), U.UCardinality1();
  MaxCardinalityMonotonic_set(S.Model(), U.Model());
  MaxCardinalityMonotonic_set(S.Universe(), U.Model());
  SubsetCardinalityBound(S.Model(), U.Model());
  SubsetCardinalityBound(S.Universe(), U.Universe());
  MultiplicationPreservesOrder(S.Cardinality0(),S.Cardinality1(),U.Cardinality0(), U.Cardinality1());
  MultiplicationPreservesOrder(S.UCardinality0(),S.UCardinality1(),U.UCardinality0(), U.UCardinality1());
  SubsetCardinalityBound(S.Universe(), U.Model());
  MultiplicationPreservesOrder(S.UCardinality0(), S.UCardinality1(), U.Cardinality0(), U.Cardinality1());
}

lemma InUniverseBounds_SetSetSet(S:SetSetSet, U:SetSetSet)
requires InUniverse_SetSetSet(S, U)
ensures S.Size0() <= U.Size0()
ensures S.USize0() <= U.USize0()
ensures S.UCardinality0() <= U.UCardinality0()
ensures S.UCardinality0() * S.USize1() <= U.UCardinality0() * U.USize1()
ensures |S.Model()| <= |U.Model()|
ensures |S.Universe()| <= |U.Universe()|
ensures S.UCardinality0() <= U.Cardinality0()
ensures S.USize0() <= U.Size0()
ensures S.UCardinality1() <= U.Cardinality1()
ensures S.UCardinality2() <= U.Cardinality2()
ensures S.UCardinality1() <= U.UCardinality1()
ensures S.UCardinality2() <= U.UCardinality2()
ensures S.Size1() <= U.Size1()
ensures S.Size2() <= U.Size2()
ensures S.USize1() <= U.Size1()
ensures S.USize2() <= U.Size2()
ensures S.USize1() <= U.USize1()
ensures S.USize2() <= U.USize2()
  ensures S.Cardinality1() <= U.Cardinality1()
  ensures S.Cardinality2() <= U.Cardinality2()
{
  ModelSizeBound_SetSetSet(S);
  ModelSizeBound_SetSetSet(U);
  reveal S.UCardinality1(), S.UCardinality2();
  MaxCardinalityMonotonic_set(S.Universe(), U.Model());
  MaxMemberCardinalityMonotonic_setset(S.Universe(), U.Model());
  SubsetCardinalityBound(S.Model(), U.Model());
  SubsetCardinalityBound(S.Universe(), U.Universe());
  SubsetCardinalityBound(S.Universe(), U.Model());
  MultiplicationPreservesOrder(S.UCardinality1(), S.UCardinality2(), U.Cardinality1(), U.Cardinality2());
  MultiplicationPreservesOrder(S.UCardinality0(), S.USize1(), U.Cardinality0(), U.Size1());
}

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

lemma InUniverseBounds_Map_Map_T(M:Map_Map_T, U:Map_Map_T)
  requires InUniverse_Map_Map_T(M, U)
  ensures M.UCardinalityKeys() <= U.CardinalityKeys()
  ensures M.Size() <= U.Size()
  ensures M.USize() <= U.USize()
  ensures M.UCardinalityKeys() <= U.UCardinalityKeys()
  ensures M.UCardinality() <= U.UCardinality()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.Cardinality()
  ensures M.USize() <= U.Size()
  ensures M.CardinalityKeys() <= U.CardinalityKeys()
{
  reveal M.Valid();
  reveal U.Valid();
  SubsetCardinalityBound(M.Model().Keys, M.Universe().Keys);
  SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  SubsetCardinalityBound(U.Model().Keys, U.Universe().Keys);
  reveal M.UCardinalityKeys(), U.UCardinalityKeys();
  MaxCardinalityMonotonic_map(M.Model().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(M.Universe().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(U.Model().Keys, U.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.CardinalityKeys(), U.Cardinality(), U.CardinalityKeys());
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys(), U.UCardinality(), U.UCardinalityKeys());
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys(), U.Cardinality(), U.CardinalityKeys());
}

lemma InUniverseBounds_Map_Set_T(M:Map_Set_T, U:Map_Set_T)
  requires InUniverse_Map_Set_T(M, U)
  ensures M.UCardinalityKeys() <= U.CardinalityKeys()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.UCardinality()
  ensures M.UCardinalityKeys() <= U.UCardinalityKeys()
  ensures M.Size() <= U.Size()
  ensures M.USize() <= U.Size()
  ensures M.USize() <= U.USize()
  ensures UCostGet_Map_Set_T(M) <= CostGet_Map_Set_T(U)
  ensures UCostContainsKey_Map_Set_T(M) <= CostContainsKey_Map_Set_T(U)
  ensures UCostInsert_Map_Set_T(M) <= CostInsert_Map_Set_T(U)
  ensures M.CardinalityKeys() <= U.CardinalityKeys()
{
  reveal InUniverse_Map_Set_T();
  reveal M.Valid(), U.Valid();
  ModelSizeBound_Map_Set_T(M);
  ModelSizeBound_Map_Set_T(U);
  SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  reveal M.UCardinalityKeys(), U.UCardinalityKeys();
  MaxCardinalityMonotonic_set(M.Model().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_set(M.Universe().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_set(M.Universe().Keys, U.Universe().Keys);
  MultiplicationPreservesOrder(M.Cardinality(), M.CardinalityKeys(), U.Cardinality(), U.CardinalityKeys());
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys(), U.Cardinality(), U.CardinalityKeys());
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys(), U.UCardinality(), U.UCardinalityKeys());
}

lemma InUniverseBounds_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires InUniverse_Map_MapSet_T(M, U)
  ensures M.UCardinalityKeys() <= U.CardinalityKeys()
  ensures M.UCardinalityKeysKeys() <= U.CardinalityKeysKeys()
  ensures M.Cardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.Cardinality()
  ensures M.UCardinality() <= U.UCardinality()
  ensures M.UCardinalityKeys() <= U.UCardinalityKeys()
  ensures M.UCardinalityKeysKeys() <= U.UCardinalityKeysKeys()
  ensures M.Size() <= U.Size()
  ensures M.USize() <= U.Size()
  ensures M.USize() <= U.USize()
  ensures UCostGet_Map_MapSet_T(M) <= CostGet_Map_MapSet_T(U)
  ensures UCostContainsKey_Map_MapSet_T(M) <= CostContainsKey_Map_MapSet_T(U)
  ensures UCostInsert_Map_MapSet_T(M) <= CostInsert_Map_MapSet_T(U)
  ensures M.SizeKeys() <= U.SizeKeys()
  ensures M.SizeKeysKeys() <= U.SizeKeysKeys()
  ensures M.USizeKeys() <= U.SizeKeys()
  ensures M.USizeKeysKeys() <= U.SizeKeysKeys()
  ensures M.USizeKeys() <= U.USizeKeys()
  ensures M.USizeKeysKeys() <= U.USizeKeysKeys()
  ensures M.CardinalityKeys() <= U.CardinalityKeys()
  ensures M.CardinalityKeysKeys() <= U.CardinalityKeysKeys()
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

// Fixed reference transitivity
// Compose two InUniverse relations for all seven collection traits. Use when a
// collection is bounded through an intermediate wrapper and a direct relation to
// the final reference is needed; map variants also preserve value agreement.

lemma InUniverseTransitive_Set(S:Set, middle:Set, U:Set)
  requires InUniverse_Set(S, middle)
  requires InUniverse_Set(middle, U)
  ensures InUniverse_Set(S, U)
{}

lemma InUniverseTransitive_SetSet(S:SetSet, middle:SetSet, U:SetSet)
  requires InUniverse_SetSet(S, middle)
  requires InUniverse_SetSet(middle, U)
  ensures InUniverse_SetSet(S, U)
{}

lemma InUniverseTransitive_SetSetSet(S:SetSetSet, middle:SetSetSet, U:SetSetSet)
  requires InUniverse_SetSetSet(S, middle)
  requires InUniverse_SetSetSet(middle, U)
  ensures InUniverse_SetSetSet(S, U)
{}

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

// Bound universe members by a containing native universe

lemma UniverseSubsetSizeBound_SetSet<T>(S:SetSet<T>, universe:set<T>)
  requires S.Valid()
  requires forall s | s in S.Universe() :: s <= universe
  ensures S.UCardinality1() <= |universe|
{
  forall s | s in S.Universe()
    ensures |s| <= |universe|
  {
    SubsetCardinalityBound(s, universe);
  }
  UniverseMemberSizeBound_SetSet(S, |universe|);
}

// Lift native update agreement to wrapper models and universes

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

// Compare nested model sizes through a model-to-model relation

lemma ModelToModelSizeBound_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires M.Model().Keys <= U.Model().Keys
  ensures M.Size() <= U.Size()
  ensures M.SizeKeys() <= U.SizeKeys()
  ensures M.SizeKeysKeys() <= U.SizeKeysKeys()
{
  SubsetCardinalityBound(M.Model().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(M.Model().Keys, U.Model().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Model().Keys, U.Model().Keys);
  MultiplicationPreservesOrder(M.CardinalityKeys(), M.CardinalityKeysKeys(), U.CardinalityKeys(), U.CardinalityKeysKeys());
  MultiplicationPreservesOrder(M.Cardinality(), M.CardinalityKeys()*M.CardinalityKeysKeys(), U.Cardinality(), U.CardinalityKeys()*U.CardinalityKeysKeys());
}

// Bound a source universe using reference model measures.
lemma UniverseToModelSizeBound_Map_MapSet_T(M:Map_MapSet_T, U:Map_MapSet_T)
  requires M.Universe().Keys <= U.Model().Keys
  ensures M.UCardinalityKeys() <= U.CardinalityKeys()
  ensures M.UCardinalityKeysKeys() <= U.CardinalityKeysKeys()
  ensures M.USize() <= U.Size()
  ensures M.USizeKeys() <= U.SizeKeys()
  ensures M.USizeKeysKeys() <= U.SizeKeysKeys()
{
  reveal M.UCardinalityKeys(), M.UCardinalityKeysKeys();
  SubsetCardinalityBound(M.Universe().Keys, U.Model().Keys);
  MaxCardinalityMonotonic_map(M.Universe().Keys, U.Model().Keys);
  MaxSetKeyCardinalityMonotonic_map_set_t(M.Universe().Keys, U.Model().Keys);
  MultiplicationPreservesOrder(M.UCardinalityKeys(), M.UCardinalityKeysKeys(), U.CardinalityKeys(), U.CardinalityKeysKeys());
  MultiplicationPreservesOrder(M.UCardinality(), M.UCardinalityKeys()*M.UCardinalityKeysKeys(), U.Cardinality(), U.CardinalityKeys()*U.CardinalityKeysKeys());
}
