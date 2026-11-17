
// Maximum value of an element (e.g. a set) in the set items according to the property weight (e.g. cardinality)
ghost function {:opaque} MaxBy<E>(items:set<E>, weight:E -> nat):(maximum:nat)
  ensures items == {} ==> maximum == 0
  decreases |items|
{
  if items == {} then 0 else
    var item :| item in items;
    var rest := MaxBy(items - {item}, weight);
    if weight(item) > rest then weight(item) else rest
}

// Maximum properties: upper bounds and a maximal witness for nonempty sets.
lemma max_by_properties<E>(items:set<E>, weight:E -> nat)
  ensures forall item | item in items :: weight(item) <= MaxBy(items, weight)
  ensures items != {} ==> exists item | item in items :: MaxBy(items, weight) == weight(item)
  decreases |items|
{
  forall item | item in items
    ensures forall rest | rest in items - {item} :: weight(rest) <= MaxBy(items - {item}, weight)
    ensures items - {item} != {} ==>
      exists rest | rest in items - {item} :: MaxBy(items - {item}, weight) == weight(rest)
  {
    max_by_properties(items - {item}, weight);
  }
  reveal MaxBy();
}

// Member bounds: compare one weight against the input set maximum.
lemma max_by_member<E>(items:set<E>, item:E, weight:E -> nat)
  requires item in items
  ensures weight(item) <= MaxBy(items, weight)
{ max_by_properties(items, weight); }

// Insertion: adjoining a member updates the maximum exactly.
lemma max_by_insert<E>(items:set<E>, item:E, weight:E -> nat)
  ensures MaxBy(items + {item}, weight) ==
    (if weight(item) <= MaxBy(items, weight) then MaxBy(items, weight) else weight(item))
{
  max_by_properties(items, weight);
  max_by_properties(items + {item}, weight);
}

// Uniform bounds: lift a bound on every weight to the maximum.
lemma max_by_bound<E>(items:set<E>, bound:nat, weight:E -> nat)
  requires forall item | item in items :: weight(item) <= bound
  ensures MaxBy(items, weight) <= bound
{ max_by_properties(items, weight); }

// Inclusion monotonicity uses the same weight on both sets.
lemma max_by_monotonic<E>(smaller:set<E>, larger:set<E>, weight:E -> nat)
  requires smaller <= larger
  ensures MaxBy(smaller, weight) <= MaxBy(larger, weight)
{
  max_by_properties(smaller, weight);
  max_by_properties(larger, weight);
}

// Transparent adapters name each independent dimension; MaxBy stays opaque.
ghost function MaxCardinality_set<K>(sets:set<set<K>>):(cardinality:nat)
  ensures sets == {} ==> cardinality == 0
{ MaxBy(sets, item => |item|) }

ghost function MaxMemberCardinality_setset<K>(sets:set<set<set<K>>>):(cardinality:nat)
  ensures sets == {} ==> cardinality == 0
  ensures MaxCardinality_set(sets) == 0 ==> cardinality == 0
{
  assert MaxCardinality_set(sets) == 0 ==> MaxBy(sets, item => MaxCardinality_set(item)) == 0 by {
    if MaxCardinality_set(sets) == 0 {
      max_by_properties(sets, item => |item|);
      max_by_bound(sets, 0, item => MaxCardinality_set(item));
    }
  }
  MaxBy(sets, item => MaxCardinality_set(item))
}

ghost function MaxCardinality_map<K, V>(maps:set<map<K, V>>):(cardinality:nat)
  ensures maps == {} ==> cardinality == 0
{ MaxBy(maps, item => |item|) }

// A named weight resolves the map's set-valued key type without nested lambdas.
ghost function KeyCardinality_map_set_t<K, V>(item:map<set<K>, V>):nat
{ MaxCardinality_set(item.Keys) }

ghost function MaxSetKeyCardinality_map_set_t<K, V>(maps:set<map<set<K>, V>>):(cardinality:nat)
  ensures maps == {} ==> cardinality == 0
  ensures MaxCardinality_map(maps) == 0 ==> cardinality == 0
{
  assert MaxCardinality_map(maps) == 0 ==> MaxBy(maps, KeyCardinality_map_set_t) == 0 by {
    if MaxCardinality_map(maps) == 0 {
      max_by_properties(maps, item => |item|);
      max_by_bound(maps, 0, KeyCardinality_map_set_t);
    }
  }
  MaxBy(maps, KeyCardinality_map_set_t)
}

// Structural bridges: cross the map maximum and its inner set-key maximum.
lemma max_set_key_cardinality_properties_map_set_t<K, V>(maps:set<map<set<K>, V>>)
  ensures forall m | m in maps ::
    MaxCardinality_set(m.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
  ensures forall m | m in maps :: forall key | key in m.Keys ::
    |key| <= MaxSetKeyCardinality_map_set_t(maps)
  ensures maps != {} ==> exists m | m in maps ::
    MaxSetKeyCardinality_map_set_t(maps) == MaxCardinality_set(m.Keys)
  decreases |maps|
{
  max_by_properties(maps, KeyCardinality_map_set_t);
  forall m | m in maps
    ensures forall key | key in m.Keys :: |key| <= MaxCardinality_set(m.Keys)
  {
    max_by_properties(m.Keys, item => |item|);
  }
}

lemma max_set_key_cardinality_member_map_set_t<K, V>(maps:set<map<set<K>, V>>, key:map<set<K>, V>)
  requires key in maps
  ensures MaxCardinality_set(key.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
  ensures forall question | question in key.Keys ::
    |question| <= MaxSetKeyCardinality_map_set_t(maps)
{
  max_by_member(maps, key, KeyCardinality_map_set_t);
  max_by_properties(key.Keys, item => |item|);
}

lemma max_set_key_cardinality_bound_map_set_t<K, V>(maps:set<map<set<K>, V>>, bound:nat)
  requires forall m | m in maps :: forall key | key in m.Keys :: |key| <= bound
  ensures MaxSetKeyCardinality_map_set_t(maps) <= bound
{
  forall m | m in maps
    ensures MaxCardinality_set(m.Keys) <= bound
  {
    max_by_bound(m.Keys, bound, item => |item|);
  }
  max_by_bound(maps, bound, KeyCardinality_map_set_t);
}

// Leaf bound: cross both maxima of a set of sets of sets.
lemma max_member_cardinality_leaf_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>, leaf:set<K>)
  requires member in sets && leaf in member
  ensures |leaf| <= MaxMemberCardinality_setset(sets)
{
  max_by_member(member, leaf, item => |item|);
  max_by_member(sets, member, item => MaxCardinality_set(item));
}
