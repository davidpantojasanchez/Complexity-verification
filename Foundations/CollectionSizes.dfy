include "CollectionMeasures.dfy"
include "PolynomialBounds.dfy"
include "../Arithmetic/BitLengths.dfy"

// Exact native representation sizes: generic sets/maps, sets of integer sets, then Boolean answer maps.

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

lemma size_step_bound(count:nat, tail:nat, weight:nat, maximum:nat)
  requires 1+count <= tail <= 1+count*(1+maximum) && weight <= maximum
  ensures 1+(count+1) <= 1+weight+tail <= 1+(count+1)*(1+maximum)
{}

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
    size_step_bound(|items - {item}|, Size_set(items - {item}, weight), weight(item), maximum);
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

// Extensional weights and persistent updates. These laws apply to nested
// shapes too: their element/key weights are the sizes of the children.
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

lemma size_add_set<E>(items:set<E>, weight:E -> nat, item:E)
  ensures Size_set(items + {item}, weight) <= Size_set(items, weight)+1+weight(item)
  ensures item !in items ==>
    Size_set(items + {item}, weight) == Size_set(items, weight)+1+weight(item)
{
  if item !in items {
    size_remove_set(items + {item}, weight, item);
    assert (items + {item}) - {item} == items;
  } else {
    assert items + {item} == items;
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

lemma size_remove_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, key:K)
  ensures Size_map(items - {key}, keyWeight, valueWeight) <= Size_map(items, keyWeight, valueWeight)
  ensures key in items ==> (Size_map(items, keyWeight, valueWeight) ==
    Size_map(items - {key}, keyWeight, valueWeight)+1+keyWeight(key)+valueWeight(items[key]))
{
  var remaining := items - {key};
  var weight := (entry:K) => if entry in items then keyWeight(entry)+valueWeight(items[entry]) else 0;
  var remainingWeight := (entry:K) => if entry in remaining then keyWeight(entry)+valueWeight(remaining[entry]) else 0;
  size_extensional_set(remaining.Keys, weight, remainingWeight);
  if key in items {
    assert remaining.Keys == items.Keys - {key};
    size_remove_set(items.Keys, weight, key);
  } else {
    assert remaining == items;
  }
}

lemma size_submap_map<K,V>(items:map<K,V>, reference:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat)
  requires items.Keys <= reference.Keys
  requires forall key | key in items :: items[key] == reference[key]
  ensures Size_map(items, keyWeight, valueWeight) <= Size_map(reference, keyWeight, valueWeight)
{
  var left := (key:K) => if key in items then keyWeight(key)+valueWeight(items[key]) else 0;
  var right := (key:K) => if key in reference then keyWeight(key)+valueWeight(reference[key]) else 0;
  size_extensional_set(items.Keys, left, right);
  size_subset_set(items.Keys, reference.Keys, right);
}

lemma size_insert_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, key:K, value:V)
  ensures Size_map(items[key := value], keyWeight, valueWeight) <=
    Size_map(items, keyWeight, valueWeight)+1+keyWeight(key)+valueWeight(value)
{
  var updated := items[key := value];
  size_remove_map(updated, keyWeight, valueWeight, key);
  size_remove_map(items, keyWeight, valueWeight, key);
  assert updated - {key} == items - {key};
}

// Integer-labelled sets and sets of sets share the signed length model.
ghost function Size_setint(items:set<int>):nat
{ Size_set(items, IntBits) }

ghost function Size_setsetint(items:set<set<int>>):(size:nat)
  ensures size == Size_set(items, child => Size_set(child, IntBits))
{
  size_extensional_set(items, Size_setint, child => Size_set(child, IntBits));
  Size_set(items, Size_setint)
}

ghost function MaxBits_setint(items:set<int>):nat
{ MaxBy(items, IntBits) }

ghost function MaxBits_setsetint(items:set<set<int>>):nat
{ MaxBy(items, MaxBits_setint) }

lemma bits_member_setsetint(sets:set<set<int>>, member:set<int>, value:int)
  requires member in sets && value in member
  ensures IntBits(value) <= MaxBits_setsetint(sets)
{
  max_by_member(sets, member, MaxBits_setint);
  max_by_member(member, value, IntBits);
}

// Applies to every retained, copied or selected native set in a fixed universe.
lemma size_bound_setint(items:set<int>, count:nat, bits:nat)
  requires |items| <= count
  requires forall value | value in items :: IntBits(value) <= bits
  ensures Size_setint(items) <= 1+count*(1+bits)
{
  size_bound_set(items, IntBits, bits);
  nonnegative_product_monotonic(|items|, 1+bits, count, 1+bits);
}

lemma size_bound_setsetint(items:set<set<int>>, count:nat, width:nat, bits:nat)
  requires |items| <= count
  requires forall member | member in items :: |member| <= width
  requires forall member | member in items :: forall value | value in member :: IntBits(value) <= bits
  ensures Size_set(items, Size_setint) <= 1+count*(2+width*(1+bits))
{
  forall member | member in items
    ensures Size_setint(member) <= 1+width*(1+bits)
  {
    size_bound_setint(member, width, bits);
  }
  size_bound_set(items, Size_setint, 1+width*(1+bits));
  nonnegative_product_monotonic(|items|, 2+width*(1+bits), count, 2+width*(1+bits));
}

lemma size_bound_setsetsetint(items:set<set<set<int>>>, n:nat)
  requires |items| <= n
  requires forall sets | sets in items :: |sets| <= n
  requires forall sets | sets in items :: forall member | member in sets :: |member| <= n
  requires forall sets | sets in items :: forall member | member in sets ::
    forall value | value in member :: IntBits(value) <= n
  ensures Size_set(items, Size_setsetint) <= 1+n*(2+n*(2+n*(1+n)))
{
  forall sets | sets in items
    ensures Size_setsetint(sets) <= 1+n*(2+n*(1+n))
  {
    size_bound_setsetint(sets, n, n, n);
  }
  size_bound_set(items, Size_setsetint, 1+n*(2+n*(1+n)));
  nonnegative_product_monotonic(|items|, 2+n*(2+n*(1+n)), n, 2+n*(2+n*(1+n)));
}

lemma size_properties_setsetint(items:set<set<int>>)
  ensures |items| <= Size_setsetint(items)
  ensures MaxCardinality_set(items) <= Size_setsetint(items)
  ensures MaxBits_setsetint(items) <= Size_setsetint(items)
{
  size_properties_set(items, Size_setint);
  forall member | member in items
    ensures |member| <= Size_setsetint(items) && MaxBits_setint(member) <= Size_setsetint(items)
  {
    size_member_set(items, Size_setint, member);
    size_properties_set(member, IntBits);
  }
  max_by_bound(items, Size_setsetint(items), (member:set<int>) => |member|);
  max_by_bound(items, Size_setsetint(items), MaxBits_setint);
}

// Fixed polynomial envelope for a set of sets with bounded dimensions and labels.
lemma size_polynomial_bound_setsetint(items:set<set<int>>, n:nat)
  requires |items| <= n
  requires forall member | member in items :: |member| <= n
  requires forall member | member in items :: forall value | value in member :: IntBits(value) <= n
  ensures Size_setsetint(items) <= 4*NatPower(n+1, 3)
{
  size_bound_setsetint(items, n, n, n);
  polynomial_product_bound(n, n, 1+n, 1, 1, 1, 1);
  assert 2+n*(1+n) <= 3*NatPower(n+1, 2);
  polynomial_product_bound(n, n, 2+n*(1+n), 1, 3, 1, 2);
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
