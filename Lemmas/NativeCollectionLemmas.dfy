include "../Collections/Set.dfy"
include "../Collections/Map.dfy"
include "ArithmeticLemmas.dfy"

// Maximum properties
// Expose upper bounds for every member and a maximality witness for nonempty
// families of native sets, maps, nested sets or set-keyed maps. Use these to reason
// about opaque recursive maxima without unfolding them in algorithm contracts.

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

// Member bounds
// Bound a selected member by the family maximum after proving membership. Native
// set and map variants bound cardinality; nested-set and set-keyed-map variants
// bound the member maximum. Use for Pick results and compound collection measures.

lemma MaxCardinalityMember_set<K>(sets:set<set<K>>, key:set<K>)
  requires key in sets
  ensures |key| <= MaxCardinality_set(sets)
{
  MaxCardinalityProperties_set(sets);
}

lemma MaxCardinalityMember_map<K, V>(maps:set<map<K, V>>, key:map<K, V>)
  requires key in maps
  ensures |key| <= MaxCardinality_map(maps)
{
  MaxCardinalityProperties_map(maps);
}

lemma MaxMemberCardinalityMember_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>)
  requires member in sets
  ensures MaxCardinality_set(member) <= MaxMemberCardinality_setset(sets)
{
  MaxMemberCardinalityProperties_setset(sets);
}

lemma MaxSetKeyCardinalityMember_map_set_t<K, V>(maps:set<map<set<K>, V>>, key:map<set<K>, V>)
  requires key in maps
  ensures MaxCardinality_set(key.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
  ensures forall question | question in key.Keys ::
    |question| <= MaxSetKeyCardinality_map_set_t(maps)
{
  MaxSetKeyCardinalityProperties_map_set_t(maps);
  MaxCardinalityProperties_set(key.Keys);
}

// Insertion maxima
// Express the maximum after insertion as the larger of the old and inserted
// measures across the four native family shapes. Use to prove persistent Add/Insert
// contracts and exact updates of content-derived universe cardinalities.

lemma MaxCardinalityInsert_set<K>(sets:set<set<K>>, key:set<K>)
  ensures MaxCardinality_set(sets + {key}) ==
    (if |key| <= MaxCardinality_set(sets) then MaxCardinality_set(sets) else |key|)
{
  MaxCardinalityProperties_set(sets);
  MaxCardinalityProperties_set(sets + {key});
}

lemma MaxCardinalityInsert_map<K, V>(maps:set<map<K, V>>, key:map<K, V>)
  ensures MaxCardinality_map(maps + {key}) ==
    (if |key| <= MaxCardinality_map(maps) then MaxCardinality_map(maps) else |key|)
{
  MaxCardinalityProperties_map(maps);
  MaxCardinalityProperties_map(maps + {key});
}

lemma MaxMemberCardinalityInsert_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>)
  ensures MaxMemberCardinality_setset(sets + {member}) ==
    (if MaxCardinality_set(member) <= MaxMemberCardinality_setset(sets)
      then MaxMemberCardinality_setset(sets) else MaxCardinality_set(member))
{
  MaxMemberCardinalityProperties_setset(sets);
  MaxMemberCardinalityProperties_setset(sets + {member});
}

lemma MaxSetKeyCardinalityInsert_map_set_t<K, V>(maps:set<map<set<K>, V>>, key:map<set<K>, V>)
  ensures MaxSetKeyCardinality_map_set_t(maps + {key}) ==
    (if MaxCardinality_set(key.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
      then MaxSetKeyCardinality_map_set_t(maps)
      else MaxCardinality_set(key.Keys))
{
  MaxSetKeyCardinalityProperties_map_set_t(maps);
  MaxSetKeyCardinalityProperties_map_set_t(maps + {key});
}

// Uniform maximum bounds
// Turn a uniform bound over family members or their leaves/set keys into a bound
// on the corresponding maximum. Use in trait universe-bound proofs when all
// contents satisfy a numeric envelope, including empty families.

lemma MaxCardinalityBound_set<K>(sets:set<set<K>>, bound:nat)
  requires forall s | s in sets :: |s| <= bound
  ensures MaxCardinality_set(sets) <= bound
{ MaxCardinalityProperties_set(sets); }

lemma MaxCardinalityBound_map<K, V>(maps:set<map<K, V>>, bound:nat)
  requires forall m | m in maps :: |m| <= bound
  ensures MaxCardinality_map(maps) <= bound
{ MaxCardinalityProperties_map(maps); }

lemma MaxMemberCardinalityBound_setset<K>(sets:set<set<set<K>>>, bound:nat)
  requires forall s | s in sets :: MaxCardinality_set(s) <= bound
  ensures MaxMemberCardinality_setset(sets) <= bound
{
  MaxMemberCardinalityProperties_setset(sets);
}

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

// Maximum monotonicity
// Transfer maximum bounds through inclusion of native set, map, nested-set or
// set-keyed-map families. Use to relate model and universe measures and fixed
// reference bounds without changing the content-derived maximum definitions.

lemma MaxCardinalityMonotonic_set<K>(smaller:set<set<K>>, larger:set<set<K>>)
  requires smaller <= larger
  ensures MaxCardinality_set(smaller) <= MaxCardinality_set(larger)
{
  MaxCardinalityProperties_set(smaller);
  MaxCardinalityProperties_set(larger);
}

lemma MaxCardinalityMonotonic_map<K, V>(smaller:set<map<K, V>>, larger:set<map<K, V>>)
  requires smaller <= larger
  ensures MaxCardinality_map(smaller) <= MaxCardinality_map(larger)
{
  MaxCardinalityProperties_map(smaller);
  MaxCardinalityProperties_map(larger);
}

lemma MaxMemberCardinalityMonotonic_setset<K>(smaller:set<set<set<K>>>, larger:set<set<set<K>>>)
  requires smaller <= larger
  ensures MaxMemberCardinality_setset(smaller) <= MaxMemberCardinality_setset(larger)
{
  MaxMemberCardinalityProperties_setset(smaller);
  MaxMemberCardinalityProperties_setset(larger);
}

lemma MaxSetKeyCardinalityMonotonic_map_set_t<K, V>(
    smaller:set<map<set<K>, V>>, larger:set<map<set<K>, V>>)
  requires smaller <= larger
  ensures MaxSetKeyCardinality_map_set_t(smaller) <= MaxSetKeyCardinality_map_set_t(larger)
{
  MaxSetKeyCardinalityProperties_map_set_t(smaller);
  MaxSetKeyCardinalityProperties_map_set_t(larger);
}

// Native map update agreement
// Update a model and its universe at the same key while preserving domain
// inclusion and value agreement. Use the returned-map or contract-only form
// to prove native updates and specialized map implementation invariants.

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

// Bound a concrete leaf after proving both nesting memberships

lemma MaxMemberCardinalityLeaf_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>, leaf:set<K>)
  requires member in sets && leaf in member
  ensures |leaf| <= MaxMemberCardinality_setset(sets)
{
  MaxCardinalityMember_set(member, leaf);
  MaxMemberCardinalityMember_setset(sets, member);
}
