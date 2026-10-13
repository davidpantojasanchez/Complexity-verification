include "ArithmeticLemmas.dfy"

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

// Transparent adapters name each independent dimension; MaxBy stays opaque.
ghost function MaxCardinality_set<K>(sets:set<set<K>>):(size:nat)
  ensures sets == {} ==> size == 0
{ MaxBy(sets, item => |item|) }

ghost function MaxMemberCardinality_setset<K>(sets:set<set<set<K>>>):(size:nat)
  ensures sets == {} ==> size == 0
{ MaxBy(sets, item => MaxCardinality_set(item)) }

ghost function MaxCardinality_map<K, V>(maps:set<map<K, V>>):(size:nat)
  ensures maps == {} ==> size == 0
{ MaxBy(maps, item => |item|) }

// A named weight resolves the map's set-valued key type without nested lambdas.
ghost function SetKeyCardinality<K, V>(item:map<set<K>, V>):nat
{ MaxCardinality_set(item.Keys) }

ghost function MaxSetKeyCardinality_map_set_t<K, V>(maps:set<map<set<K>, V>>):(size:nat)
  ensures maps == {} ==> size == 0
{ MaxBy(maps, SetKeyCardinality) }

// Maximum properties: upper bounds and a maximal witness for nonempty families.
lemma MaxByProperties<E>(items:set<E>, weight:E -> nat)
  ensures forall item | item in items :: weight(item) <= MaxBy(items, weight)
  ensures items != {} ==> exists item | item in items :: MaxBy(items, weight) == weight(item)
  decreases |items|
{
  forall item | item in items
    ensures forall rest | rest in items - {item} :: weight(rest) <= MaxBy(items - {item}, weight)
    ensures items - {item} != {} ==>
      exists rest | rest in items - {item} :: MaxBy(items - {item}, weight) == weight(rest)
  {
    MaxByProperties(items - {item}, weight);
  }
  reveal MaxBy();
}

// Member bounds: compare one weight against the family maximum.
lemma MaxByMember<E>(items:set<E>, item:E, weight:E -> nat)
  requires item in items
  ensures weight(item) <= MaxBy(items, weight)
{ MaxByProperties(items, weight); }

// Insertion: adjoining a member updates the maximum exactly.
lemma MaxByInsert<E>(items:set<E>, item:E, weight:E -> nat)
  ensures MaxBy(items + {item}, weight) ==
    (if weight(item) <= MaxBy(items, weight) then MaxBy(items, weight) else weight(item))
{
  MaxByProperties(items, weight);
  MaxByProperties(items + {item}, weight);
}

// Uniform bounds: lift a bound on every weight to the maximum.
lemma MaxByBound<E>(items:set<E>, bound:nat, weight:E -> nat)
  requires forall item | item in items :: weight(item) <= bound
  ensures MaxBy(items, weight) <= bound
{ MaxByProperties(items, weight); }

// Inclusion monotonicity uses the same weight on both families.
lemma MaxByMonotonic<E>(smaller:set<E>, larger:set<E>, weight:E -> nat)
  requires smaller <= larger
  ensures MaxBy(smaller, weight) <= MaxBy(larger, weight)
{
  MaxByProperties(smaller, weight);
  MaxByProperties(larger, weight);
}

// Structural bridges: cross the map maximum and its inner set-key maximum.
lemma MaxSetKeyCardinalityProperties_map_set_t<K, V>(maps:set<map<set<K>, V>>)
  ensures forall m | m in maps ::
    MaxCardinality_set(m.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
  ensures forall m | m in maps :: forall key | key in m.Keys ::
    |key| <= MaxSetKeyCardinality_map_set_t(maps)
  ensures maps != {} ==> exists m | m in maps ::
    MaxSetKeyCardinality_map_set_t(maps) == MaxCardinality_set(m.Keys)
  decreases |maps|
{
  MaxByProperties(maps, SetKeyCardinality);
  forall m | m in maps
    ensures forall key | key in m.Keys :: |key| <= MaxCardinality_set(m.Keys)
  {
    MaxByProperties(m.Keys, item => |item|);
  }
}

lemma MaxSetKeyCardinalityMember_map_set_t<K, V>(maps:set<map<set<K>, V>>, key:map<set<K>, V>)
  requires key in maps
  ensures MaxCardinality_set(key.Keys) <= MaxSetKeyCardinality_map_set_t(maps)
  ensures forall question | question in key.Keys ::
    |question| <= MaxSetKeyCardinality_map_set_t(maps)
{
  MaxByMember(maps, key, SetKeyCardinality);
  MaxByProperties(key.Keys, item => |item|);
}

lemma MaxSetKeyCardinalityBound_map_set_t<K, V>(maps:set<map<set<K>, V>>, bound:nat)
  requires forall m | m in maps :: forall key | key in m.Keys :: |key| <= bound
  ensures MaxSetKeyCardinality_map_set_t(maps) <= bound
{
  forall m | m in maps
    ensures MaxCardinality_set(m.Keys) <= bound
  {
    MaxByBound(m.Keys, bound, item => |item|);
  }
  MaxByBound(maps, bound, SetKeyCardinality);
}

// Leaf bound: cross both maxima of a depth-two set family.
lemma MaxMemberCardinalityLeaf_setset<K>(sets:set<set<set<K>>>, member:set<set<K>>, leaf:set<K>)
  requires member in sets && leaf in member
  ensures |leaf| <= MaxMemberCardinality_setset(sets)
{
  MaxByMember(member, leaf, item => |item|);
  MaxByMember(sets, member, item => MaxCardinality_set(item));
}
