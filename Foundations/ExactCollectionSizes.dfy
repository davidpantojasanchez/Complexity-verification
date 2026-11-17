include "CollectionMaxima.dfy"
include "../Arithmetic/PolynomialBounds.dfy"
include "../Arithmetic/BitLengths.dfy"

// Exact native representation sizes: generic sets/maps and Boolean answer maps.

// Exact set size and its map-entry interpretation; headers count even for
// empty containers, and generic leaves supply their own representation weight.
ghost function {:opaque} Size_set<E>(items:set<E>, weight:E -> nat):nat
  decreases |items|
{
  if items == {} then 1 else
    var item :| item in items;
    1 + weight(item) + Size_set(items - {item}, weight)
}

// A map entry carries a header, its key and its value. Size_set supplies the
// entry header and the outer header; this view does not materialize the keys.
ghost function Size_map<K, V>(items:map<K, V>, keyWeight:K -> nat, valueWeight:V -> nat):nat
{ Size_set(items.Keys, (key:K) => if key in items then keyWeight(key) + valueWeight(items[key]) else 0) }

lemma size_bound_set<E>(items:set<E>, weight:E -> nat, maximum:nat)
  requires forall item | item in items :: weight(item) <= maximum
  ensures 1 + |items| <= Size_set(items, weight) <= 1 + |items|*(1+maximum)
  decreases |items|
{
  forall item | item in items
    ensures 1+|items| <= 1+weight(item)+Size_set(items - {item}, weight) <= 1+|items|*(1+maximum)
  {
    size_bound_set(items - {item}, weight, maximum);
    assert |items - {item}|+1 == |items|;
  }
  reveal Size_set();
}

lemma size_member_set<E>(items:set<E>, weight:E -> nat, item:E)
  requires item in items
  ensures weight(item) < Size_set(items, weight)
  decreases |items|
{
  forall chosen | chosen in items && chosen != item
    ensures weight(item) < Size_set(items - {chosen}, weight)
  {
    size_member_set(items - {chosen}, weight, item);
  }
  reveal Size_set();
}

lemma size_properties_set<E>(items:set<E>, weight:E -> nat)
  ensures 1+|items| <= Size_set(items, weight)
  ensures MaxBy(items, weight) <= Size_set(items, weight)
{
  max_by_properties(items, weight);
  size_bound_set(items, weight, MaxBy(items, weight));
  forall item | item in items
    ensures weight(item) <= Size_set(items, weight)
  {
    size_member_set(items, weight, item);
  }
  max_by_bound(items, Size_set(items, weight), weight);
}

// Extensional weights and subset sizes apply to nested shapes too, using
// the sizes of children as element weights.
lemma {:induction false} size_extensional_set<E>(items:set<E>, left:E -> nat, right:E -> nat)
  requires forall item | item in items :: left(item) == right(item)
  ensures Size_set(items, left) == Size_set(items, right)
  decreases |items|
{
  reveal Size_set();
  if items != {} {
    var item :| item in items;
    size_remove_set(items, left, item);
    size_remove_set(items, right, item);
    size_extensional_set(items - {item}, left, right);
  }
}

lemma {:induction false} size_remove_set<E>(items:set<E>, weight:E -> nat, item:E)
  requires item in items
  ensures Size_set(items, weight) == Size_set(items - {item}, weight)+1+weight(item)
  decreases |items|
{
  reveal Size_set();
  forall chosen | chosen in items
    ensures 1+weight(chosen)+Size_set(items - {chosen}, weight) ==
      Size_set(items - {item}, weight)+1+weight(item)
  {
    if chosen != item {
      size_remove_set(items - {chosen}, weight, item);
      size_remove_set(items - {item}, weight, chosen);
      assert (items - {chosen}) - {item} == (items - {item}) - {chosen};
    }
  }
}

lemma {:induction false} size_subset_set<E>(items:set<E>, reference:set<E>, weight:E -> nat)
  requires items <= reference
  ensures Size_set(items, weight) <= Size_set(reference, weight)
  decreases |reference - items|
{
  if items != reference {
    if reference - items == {} {
      forall item | item in reference
        ensures item in items
      {
        assert item !in reference - items;
      }
      assert reference <= items;
    }
    assert reference - items != {};
    var removed :| removed in reference - items;
    size_remove_set(reference, weight, removed);
    size_subset_set(items, reference - {removed}, weight);
  }
}

lemma size_bound_map<K, V>(items:map<K, V>, keyWeight:K -> nat, valueWeight:V -> nat,
    keyMaximum:nat, valueMaximum:nat)
  requires forall key | key in items :: keyWeight(key) <= keyMaximum && valueWeight(items[key]) <= valueMaximum
  ensures 1 + |items| <= Size_map(items, keyWeight, valueWeight) <=
    1 + |items|*(1+keyMaximum+valueMaximum)
{
  size_bound_set(items.Keys, (key:K) => if key in items then keyWeight(key) + valueWeight(items[key]) else 0, keyMaximum+valueMaximum);
}

lemma size_member_map<K, V>(items:map<K, V>, keyWeight:K -> nat, valueWeight:V -> nat, key:K)
  requires key in items
  ensures keyWeight(key)+valueWeight(items[key]) < Size_map(items, keyWeight, valueWeight)
{
  size_member_set(items.Keys, (entry:K) => if entry in items then keyWeight(entry)+valueWeight(items[entry]) else 0, key);
}

lemma size_properties_map<K, V>(items:map<K, V>, keyWeight:K -> nat, valueWeight:V -> nat)
  ensures 1+|items| <= Size_map(items, keyWeight, valueWeight)
{
  size_properties_set(items.Keys, (key:K) => if key in items then keyWeight(key)+valueWeight(items[key]) else 0);
}

// Representation size depends on weights on stored entries only.
lemma size_extensional_map<K,V>(items:map<K,V>, leftKey:K -> nat, rightKey:K -> nat,
    leftValue:V -> nat, rightValue:V -> nat)
  requires forall key | key in items :: leftKey(key) == rightKey(key) && leftValue(items[key]) == rightValue(items[key])
  ensures Size_map(items, leftKey, leftValue) == Size_map(items, rightKey, rightValue)
{
  size_extensional_set(items.Keys,
    key => if key in items then leftKey(key)+leftValue(items[key]) else 0,
    key => if key in items then rightKey(key)+rightValue(items[key]) else 0);
}

// Boolean answer maps and weighted populations reuse the same generic sizes.
ghost function Size_map_t_bool<Q>(answers:map<Q, bool>, weight:Q -> nat):nat
{ Size_map(answers, weight, BoolBits) }

lemma size_bound_map_t_bool<Q>(answers:map<Q, bool>, weight:Q -> nat, count:nat, bits:nat)
  requires |answers| <= count
  requires forall question | question in answers :: weight(question) <= bits
  ensures Size_map_t_bool(answers, weight) <= 1+count*(2+bits)
{
  size_bound_map(answers, weight, BoolBits, bits, 1);
  nonnegative_product_monotonic(|answers|, 2+bits, count, 2+bits);
}

lemma size_bound_map_map_t_bool_t<Q, V>(population:map<map<Q, bool>, V>, weight:Q -> nat, valueWeight:V -> nat,
    count:nat, questions:nat, bits:nat, values:nat)
  requires |population| <= count
  requires forall candidate | candidate in population :: |candidate| <= questions && valueWeight(population[candidate]) <= values
  requires forall candidate | candidate in population :: forall question | question in candidate :: weight(question) <= bits
  ensures Size_map(population, (candidate:map<Q, bool>) => Size_map_t_bool(candidate, weight), valueWeight) <=
    1+count*(2+questions*(2+bits)+values)
{
  forall candidate | candidate in population
    ensures Size_map_t_bool(candidate, weight) <= 1+questions*(2+bits)
  {
    size_bound_map_t_bool(candidate, weight, questions, bits);
  }
  size_bound_map(population, (candidate:map<Q, bool>) => Size_map_t_bool(candidate, weight), valueWeight,
    1+questions*(2+bits), values);
  nonnegative_product_monotonic(|population|, 2+questions*(2+bits)+values, count, 2+questions*(2+bits)+values);
}
