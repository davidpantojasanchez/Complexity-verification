include "Set.dfy"
include "Map.dfy"
include "ArithmeticLemmas.dfy"

// -----------------------------------------------------------------------------
// Native set families: maximum member cardinality
// -----------------------------------------------------------------------------

// Expose the defining maximum for a family of native sets; use when unfolding MaxCardinality_set safely.
lemma MaxCardinalityProperties_set<K>(sets:set<set<K>>)
  ensures forall s | s in sets :: |s| <= MaxCardinality_set(sets)
  ensures sets != {} ==> exists s | s in sets :: MaxCardinality_set(sets) == |s|
  decreases |sets|
{
  forall s | s in sets
    ensures forall t | t in sets - {s} :: |t| <= MaxCardinality_set(sets - {s})
    ensures sets - {s} != {} ==>
      exists t | t in sets - {s} :: MaxCardinality_set(sets - {s}) == |t|
  {
    MaxCardinalityProperties_set(sets - {s});
  }
  reveal MaxCardinality_set();
}

// Bound one member set by the family maximum; use after proving membership.
lemma MaxCardinalityMember_set<K>(sets:set<set<K>>, key:set<K>)
  requires key in sets
  ensures |key| <= MaxCardinality_set(sets)
{
  MaxCardinalityProperties_set(sets);
}

// Describe how the maximum changes after insertion; use when growing a native set family.
lemma MaxCardinalityInsert_set<K>(sets:set<set<K>>, key:set<K>)
  ensures MaxCardinality_set(sets + {key}) ==
    (if |key| <= MaxCardinality_set(sets) then MaxCardinality_set(sets) else |key|)
{
  MaxCardinalityProperties_set(sets);
  MaxCardinalityProperties_set(sets + {key});
}

// Turn a uniform member-cardinality bound into a maximum bound.
lemma MaxCardinalityBound_set<K>(sets:set<set<K>>, bound:nat)
  requires forall s | s in sets :: |s| <= bound
  ensures MaxCardinality_set(sets) <= bound
{ MaxCardinalityProperties_set(sets); }

// Transfer the maximum across inclusion of native set families.
lemma MaxCardinalityMonotonic_set<K>(smaller:set<set<K>>, larger:set<set<K>>)
  requires smaller <= larger
  ensures MaxCardinality_set(smaller) <= MaxCardinality_set(larger)
{
  MaxCardinalityProperties_set(smaller);
  MaxCardinalityProperties_set(larger);
}

// -----------------------------------------------------------------------------
// Native map families: maximum member cardinality
// -----------------------------------------------------------------------------

// Expose the defining maximum for a family of native maps; use when unfolding MaxCardinality_map safely.
lemma MaxCardinalityProperties_map<K, V>(maps:set<map<K, V>>)
  ensures forall m | m in maps :: |m| <= MaxCardinality_map(maps)
  ensures maps != {} ==> exists m | m in maps :: MaxCardinality_map(maps) == |m|
  decreases |maps|
{
  forall m | m in maps
    ensures forall k | k in maps - {m} :: |k| <= MaxCardinality_map(maps - {m})
    ensures maps - {m} != {} ==>
      exists k | k in maps - {m} :: MaxCardinality_map(maps - {m}) == |k|
  {
    MaxCardinalityProperties_map(maps - {m});
  }
  reveal MaxCardinality_map();
}

// Bound one member map by the family maximum; use after proving membership.
lemma MaxCardinalityMember_map<K, V>(maps:set<map<K, V>>, key:map<K, V>)
  requires key in maps
  ensures |key| <= MaxCardinality_map(maps)
{
  MaxCardinalityProperties_map(maps);
}

// Describe how the maximum changes after inserting a native map.
lemma MaxCardinalityInsert_map<K, V>(maps:set<map<K, V>>, key:map<K, V>)
  ensures MaxCardinality_map(maps + {key}) ==
    (if |key| <= MaxCardinality_map(maps) then MaxCardinality_map(maps) else |key|)
{
  MaxCardinalityProperties_map(maps);
  MaxCardinalityProperties_map(maps + {key});
}

// Turn a uniform map-cardinality bound into a maximum bound.
lemma MaxCardinalityBound_map<K, V>(maps:set<map<K, V>>, bound:nat)
  requires forall m | m in maps :: |m| <= bound
  ensures MaxCardinality_map(maps) <= bound
{ MaxCardinalityProperties_map(maps); }

// Transfer the map-cardinality maximum across family inclusion.
lemma MaxCardinalityMonotonic_map<K, V>(smaller:set<map<K, V>>, larger:set<map<K, V>>)
  requires smaller <= larger
  ensures MaxCardinality_map(smaller) <= MaxCardinality_map(larger)
{
  MaxCardinalityProperties_map(smaller);
  MaxCardinalityProperties_map(larger);
}

// -----------------------------------------------------------------------------
// Nested native set families: maximum member size
// -----------------------------------------------------------------------------

// Expose the maximum total member size of a nested native set family.
lemma MaxSizeProperties_setset<K>(sets:set<set<set<K>>>)
  ensures forall s | s in sets :: |s| * MaxCardinality_set(s) <= MaxSize_setset(sets)
  ensures sets != {} ==> exists s | s in sets :: MaxSize_setset(sets) == |s| * MaxCardinality_set(s)
  decreases |sets|
{
  forall s | s in sets
    ensures forall t | t in sets - {s} :: |t| * MaxCardinality_set(t) <= MaxSize_setset(sets - {s})
    ensures sets - {s} != {} ==>
      exists t | t in sets - {s} :: MaxSize_setset(sets - {s}) == |t| * MaxCardinality_set(t)
  {
    MaxSizeProperties_setset(sets - {s});
  }
  reveal MaxSize_setset();
}

// Bound one nested member total size by the family maximum.
lemma MaxSizeMember_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>)
  requires member in sets
  ensures |member| * MaxCardinality_set(member) <= MaxSize_setset(sets)
{
  MaxSizeProperties_setset(sets);
}

// Describe the nested-member size maximum after insertion.
lemma MaxSizeInsert_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>)
  ensures MaxSize_setset(sets + {member}) ==
    (if |member| * MaxCardinality_set(member) <= MaxSize_setset(sets)
      then MaxSize_setset(sets) else |member| * MaxCardinality_set(member))
{
  MaxSizeProperties_setset(sets);
  MaxSizeProperties_setset(sets + {member});
}

// Derive a nested-member size maximum from a uniform bound.
lemma MaxSizeBound_setset<K>(sets:set<set<set<K>>>, bound:nat)
  requires forall s | s in sets :: |s| * MaxCardinality_set(s) <= bound
  ensures MaxSize_setset(sets) <= bound
{
  MaxSizeProperties_setset(sets);
}

// Transfer the nested-member size maximum across family inclusion.
lemma MaxSizeMonotonic_setset<K>(smaller:set<set<set<K>>>, larger:set<set<set<K>>>)
  requires smaller <= larger
  ensures MaxSize_setset(smaller) <= MaxSize_setset(larger)
{
  MaxSizeProperties_setset(smaller);
  MaxSizeProperties_setset(larger);
}

// -----------------------------------------------------------------------------
// Nested native set families: maximum leaf cardinality
// -----------------------------------------------------------------------------

// Expose the maximum leaf cardinality of a nested native set family.
lemma MaxMemberCardinalityProperties_setset<K>(sets:set<set<set<K>>>)
  ensures forall s | s in sets :: MaxCardinality_set(s) <= MaxMemberCardinality_setset(sets)
  ensures sets != {} ==> exists s | s in sets :: MaxMemberCardinality_setset(sets) == MaxCardinality_set(s)
  decreases |sets|
{
  forall s | s in sets
    ensures forall t | t in sets - {s} :: MaxCardinality_set(t) <= MaxMemberCardinality_setset(sets - {s})
    ensures sets - {s} != {} ==>
      exists t | t in sets - {s} :: MaxMemberCardinality_setset(sets - {s}) == MaxCardinality_set(t)
  {
    MaxMemberCardinalityProperties_setset(sets - {s});
  }
  reveal MaxMemberCardinality_setset();
}

// Bound one member leaf maximum by the family-wide maximum.
lemma MaxMemberCardinalityMember_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>)
  requires member in sets
  ensures MaxCardinality_set(member) <= MaxMemberCardinality_setset(sets)
{
  MaxMemberCardinalityProperties_setset(sets);
}

// Describe the leaf-cardinality maximum after inserting a nested member.
lemma MaxMemberCardinalityInsert_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>)
  ensures MaxMemberCardinality_setset(sets + {member}) ==
    (if MaxCardinality_set(member) <= MaxMemberCardinality_setset(sets)
      then MaxMemberCardinality_setset(sets) else MaxCardinality_set(member))
{
  MaxMemberCardinalityProperties_setset(sets);
  MaxMemberCardinalityProperties_setset(sets + {member});
}

// Derive a leaf-cardinality maximum from a uniform bound.
lemma MaxMemberCardinalityBound_setset<K>(sets:set<set<set<K>>>, bound:nat)
  requires forall s | s in sets :: MaxCardinality_set(s) <= bound
  ensures MaxMemberCardinality_setset(sets) <= bound
{
  MaxMemberCardinalityProperties_setset(sets);
}

// Transfer the leaf-cardinality maximum across nested-family inclusion.
lemma MaxMemberCardinalityMonotonic_setset<K>(smaller:set<set<set<K>>>, larger:set<set<set<K>>>)
  requires smaller <= larger
  ensures MaxMemberCardinality_setset(smaller) <= MaxMemberCardinality_setset(larger)
{
  MaxMemberCardinalityProperties_setset(smaller);
  MaxMemberCardinalityProperties_setset(larger);
}

// Bound a concrete leaf after proving both nesting memberships.
lemma MaxMemberCardinalityLeaf_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>, leaf:set<K>)
  requires member in sets && leaf in member
  ensures |leaf| <= MaxMemberCardinality_setset(sets)
{
  MaxCardinalityMember_set(member, leaf);
  MaxMemberCardinalityMember_setset(sets, member);
}

// Establish both nested maxima from independent member and leaf bounds.
lemma MaxNumericBounds_setset<K>(sets:set<set<set<K>>>, cardinality:nat, members:nat, leaves:nat)
  requires |sets| <= cardinality
  requires forall s | s in sets :: |s| <= members
  requires forall s | s in sets :: forall t | t in s :: |t| <= leaves
  ensures MaxSize_setset(sets) <= members * leaves
  ensures MaxMemberCardinality_setset(sets) <= leaves
  ensures |sets| * MaxSize_setset(sets) <= cardinality * members * leaves
{
  forall s | s in sets
    ensures MaxCardinality_set(s) <= leaves
    ensures |s| * MaxCardinality_set(s) <= members * leaves
  {
    MaxCardinalityBound_set(s, leaves);
    NatMultiplicationMonotonic(|s|, MaxCardinality_set(s), leaves);
    NatMultiplicationMonotonic(leaves, |s|, members);
  }
  MaxSizeBound_setset(sets, members * leaves);
  MaxMemberCardinalityBound_setset(sets, leaves);
  NatMultiplicationMonotonic(|sets|, MaxSize_setset(sets), members * leaves);
  NatMultiplicationMonotonic(members * leaves, |sets|, cardinality);
}

// -----------------------------------------------------------------------------
// Families of native set-keyed maps
// -----------------------------------------------------------------------------

// Expose the largest set key in a family of native set-keyed maps.
lemma MaxSetKeyCardinalityProperties_map_set_t<K, V>(maps:set<map<set<K>, V>>)
  ensures forall m | m in maps ::
    MaxCardinality_set(m.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
  ensures forall m | m in maps :: forall key | key in m.Keys ::
    |key| <= MaxSetKeyCardinality_map_set_t(maps)
  ensures maps != {} ==> exists m | m in maps ::
    MaxSetKeyCardinality_map_set_t(maps) == MaxCardinality_set(m.Keys)
  decreases |maps|
{
  forall m | m in maps
    ensures forall restMap | restMap in maps - {m} ::
      MaxCardinality_set(restMap.Keys) <= MaxSetKeyCardinality_map_set_t(maps - {m})
    ensures forall restMap | restMap in maps - {m} ::
      forall key | key in restMap.Keys ::
        |key| <= MaxSetKeyCardinality_map_set_t(maps - {m})
    ensures maps - {m} != {} ==> exists restMap | restMap in maps - {m} ::
      MaxSetKeyCardinality_map_set_t(maps - {m}) == MaxCardinality_set(restMap.Keys)
  {
    MaxSetKeyCardinalityProperties_map_set_t(maps - {m});
  }
  forall m | m in maps
    ensures forall key | key in m.Keys :: |key| <= MaxCardinality_set(m.Keys)
  {
    MaxCardinalityProperties_set(m.Keys);
  }
  reveal MaxSetKeyCardinality_map_set_t();
}

// Bound one member map set-key maximum by the family maximum.
lemma MaxSetKeyCardinalityMember_map_set_t<K, V>(maps:set<map<set<K>, V>>, key:map<set<K>, V>)
  requires key in maps
  ensures MaxCardinality_set(key.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
  ensures forall question | question in key.Keys ::
    |question| <= MaxSetKeyCardinality_map_set_t(maps)
{
  MaxSetKeyCardinalityProperties_map_set_t(maps);
  MaxCardinalityProperties_set(key.Keys);
}

// Describe the set-key maximum after inserting a member map.
lemma MaxSetKeyCardinalityInsert_map_set_t<K, V>(maps:set<map<set<K>, V>>, key:map<set<K>, V>)
  ensures MaxSetKeyCardinality_map_set_t(maps + {key}) ==
    (if MaxCardinality_set(key.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
      then MaxSetKeyCardinality_map_set_t(maps)
      else MaxCardinality_set(key.Keys))
{
  MaxSetKeyCardinalityProperties_map_set_t(maps);
  MaxSetKeyCardinalityProperties_map_set_t(maps + {key});
}

// Derive the set-key maximum from a uniform bound over member maps.
lemma MaxSetKeyCardinalityBound_map_set_t<K, V>(maps:set<map<set<K>, V>>, bound:nat)
  requires forall m | m in maps :: forall key | key in m.Keys :: |key| <= bound
  ensures MaxSetKeyCardinality_map_set_t(maps) <= bound
{
  MaxSetKeyCardinalityProperties_map_set_t(maps);
  forall m | m in maps
    ensures MaxCardinality_set(m.Keys) <= bound
  {
    MaxCardinalityBound_set(m.Keys, bound);
  }
  if maps == {} {
    reveal MaxSetKeyCardinality_map_set_t();
  } else {
    var m :| m in maps && MaxSetKeyCardinality_map_set_t(maps) == MaxCardinality_set(m.Keys);
  }
}

// Transfer the set-key maximum across inclusion of map families.
lemma MaxSetKeyCardinalityMonotonic_map_set_t<K, V>(
    smaller:set<map<set<K>, V>>, larger:set<map<set<K>, V>>)
  requires smaller <= larger
  ensures MaxSetKeyCardinality_map_set_t(smaller) <= MaxSetKeyCardinality_map_set_t(larger)
{
  MaxSetKeyCardinalityProperties_map_set_t(smaller);
  MaxSetKeyCardinalityProperties_map_set_t(larger);
}

// -----------------------------------------------------------------------------
// Native map updates relative to a reference universe
// -----------------------------------------------------------------------------

// Show that updating an admitted key stays inside a reference map universe.
lemma MapUpdatePreservesUniverse<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
    returns (updatedModel:map<K, V>, updatedUniverse:map<K, V>)
  requires model.Keys <= universe.Keys
  requires forall entry | entry in model.Keys :: model[entry] == universe[entry]
  ensures updatedModel.Keys <= updatedUniverse.Keys
  ensures updatedModel == model[key := value] && updatedUniverse == universe[key := value]
  ensures forall entry | entry in updatedModel.Keys :: updatedModel[entry] == updatedUniverse[entry]
{
  updatedModel := model[key := value];
  updatedUniverse := universe[key := value];
}

// Preserve reference-map value agreement after updating both maps at the same key.
lemma MapUpdateAgreement<K, V>(model:map<K, V>, universe:map<K, V>, key:K, value:V)
  requires model.Keys <= universe.Keys
  requires forall entry | entry in model.Keys :: model[entry] == universe[entry]
  ensures model[key := value].Keys <= universe[key := value].Keys
  ensures forall entry {:trigger model[key := value][entry]} |
    entry in model[key := value].Keys ::
    model[key := value][entry] == universe[key := value][entry]
{
  ghost var updatedModel, updatedUniverse :=
    MapUpdatePreservesUniverse(model, universe, key, value);
}
