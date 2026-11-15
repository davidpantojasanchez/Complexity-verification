include "StructuralSizes.dfy"
include "Collections.dfy"

// Maxima describe leaves, not sizes of compound keys. Normalizing the empty
// maximum to one gives a common positive multiplier for every shape.
ghost function MaxLeafWeight(left:nat, right:nat):(maximum:nat)
  ensures left <= maximum && right <= maximum
{ if right <= left then left else right }

ghost function MaxLeafBits_set<E>(items:set<E>, weight:E -> nat):(bits:nat)
  ensures 1 <= bits
  ensures items == {} ==> bits == 1
{
  var maximum := MaxBy(items, weight);
  if maximum == 0 then 1 else maximum
}

ghost function MaxLeafBits_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat):(bits:nat)
  ensures 1 <= bits
  ensures items == map[] ==> bits == 1
{
  MaxLeafBits_set(items.Keys, key =>
    if key in items then MaxLeafWeight(keyWeight(key), valueWeight(items[key])) else 0)
}

ghost function MaxLeafBits_setset<E>(items:set<set<E>>, weight:E -> nat):(bits:nat)
  ensures 1 <= bits
{ MaxLeafBits_set(items, child => MaxLeafBits_set(child, weight)) }

ghost function MaxLeafBits_setsetset<E>(items:set<set<set<E>>>, weight:E -> nat):(bits:nat)
  ensures 1 <= bits
{ MaxLeafBits_set(items, child => MaxLeafBits_setset(child, weight)) }

ghost function MaxLeafBits_map_set_t<K,V>(items:map<set<K>,V>, keyWeight:K -> nat, valueWeight:V -> nat):(bits:nat)
  ensures 1 <= bits
{ MaxLeafBits_map(items, key => MaxLeafBits_set(key, keyWeight), valueWeight) }

ghost function MaxLeafBits_map_map_t<K,V,W>(items:map<map<K,V>,W>, keyWeight:K -> nat,
    innerValueWeight:V -> nat, valueWeight:W -> nat):(bits:nat)
  ensures 1 <= bits
{ MaxLeafBits_map(items, key => MaxLeafBits_map(key, keyWeight, innerValueWeight), valueWeight) }

ghost function MaxLeafBits_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>, keyWeight:K -> nat,
    innerValueWeight:V -> nat, valueWeight:W -> nat):(bits:nat)
  ensures 1 <= bits
{ MaxLeafBits_map(items, key => MaxLeafBits_map_set_t(key, keyWeight, innerValueWeight), valueWeight) }

// Independent cardinality maxima retain the existing structural paths. The
// recurrence accounts for intermediate entries, including empty children.
ghost function StructuralVolume_setset<E>(items:set<set<E>>):nat
{ StructuralVolume(|items|, MaxCardinality_set(items)) }

ghost function StructuralVolume_setsetset<E>(items:set<set<set<E>>>):nat
{ StructuralVolume(|items|, StructuralVolume(MaxCardinality_set(items), MaxMemberCardinality_setset(items))) }

ghost function StructuralVolume_map_set_t<K,V>(items:map<set<K>,V>):nat
{ StructuralVolume(|items|, MaxCardinality_set(items.Keys)) }

ghost function StructuralVolume_map_map_t<K,V,W>(items:map<map<K,V>,W>):nat
{ StructuralVolume(|items|, MaxCardinality_map(items.Keys)) }

ghost function StructuralVolume_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>):nat
{ StructuralVolume(|items|, StructuralVolume(MaxCardinality_map(items.Keys), MaxSetKeyCardinality_map_set_t(items.Keys))) }

// Uniform envelopes used by receivers and external compound operands.
ghost function RepresentationSize_set<E>(items:set<E>, weight:E -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_set(items, weight) <= size
{ StructuralSize(|items|, MaxLeafBits_set(items, weight)) }

ghost function RepresentationSize_setset<E>(items:set<set<E>>, weight:E -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_setset(items, weight) <= size
{ StructuralSize(StructuralVolume_setset(items), MaxLeafBits_setset(items, weight)) }

ghost function RepresentationSize_setsetset<E>(items:set<set<set<E>>>, weight:E -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_setsetset(items, weight) <= size
{ StructuralSize(StructuralVolume_setsetset(items), MaxLeafBits_setsetset(items, weight)) }

ghost function RepresentationSize_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map(items, keyWeight, valueWeight) <= size
{ StructuralSize(|items|, MaxLeafBits_map(items, keyWeight, valueWeight)) }

ghost function RepresentationSize_map_set_t<K,V>(items:map<set<K>,V>, keyWeight:K -> nat, valueWeight:V -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map_set_t(items, keyWeight, valueWeight) <= size
{ StructuralSize(StructuralVolume_map_set_t(items), MaxLeafBits_map_set_t(items, keyWeight, valueWeight)) }

ghost function RepresentationSize_map_map_t<K,V,W>(items:map<map<K,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight) <= size
{ StructuralSize(StructuralVolume_map_map_t(items), MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight)) }

ghost function RepresentationSize_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight) <= size
{ StructuralSize(StructuralVolume_map_mapset_t(items), MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)) }

// Member and uniform-bound laws are shared by all shapes through their leaf
// projections. Neither method computes a maximum at runtime.
lemma max_leaf_bits_member_set<E>(items:set<E>, weight:E -> nat, item:E)
  requires item in items
  ensures weight(item) <= MaxLeafBits_set(items, weight)
{ max_by_member(items, item, weight); }

lemma max_leaf_bits_bound_set<E>(items:set<E>, weight:E -> nat, bound:nat)
  requires 1 <= bound
  requires forall item | item in items :: weight(item) <= bound
  ensures MaxLeafBits_set(items, weight) <= bound
{ max_by_bound(items, bound, weight); }

lemma max_leaf_bits_member_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, key:K)
  requires key in items
  ensures keyWeight(key) <= MaxLeafBits_map(items, keyWeight, valueWeight)
  ensures valueWeight(items[key]) <= MaxLeafBits_map(items, keyWeight, valueWeight)
{
  max_leaf_bits_member_set(items.Keys, k =>
    if k in items then MaxLeafWeight(keyWeight(k), valueWeight(items[k])) else 0, key);
}

lemma max_leaf_bits_bound_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, bound:nat)
  requires 1 <= bound
  requires forall key | key in items :: keyWeight(key) <= bound && valueWeight(items[key]) <= bound
  ensures MaxLeafBits_map(items, keyWeight, valueWeight) <= bound
{
  max_leaf_bits_bound_set(items.Keys, key =>
    if key in items then MaxLeafWeight(keyWeight(key), valueWeight(items[key])) else 0, bound);
}

// Inclusion uses one fixed interpretation. Map inclusion additionally preserves
// retained bindings; replacing a value is not covered by this monotonicity law.
lemma max_leaf_bits_subset_set<E>(smaller:set<E>, larger:set<E>, weight:E -> nat)
  requires smaller <= larger
  ensures MaxLeafBits_set(smaller, weight) <= MaxLeafBits_set(larger, weight)
{ max_by_monotonic(smaller, larger, weight); }

lemma max_leaf_bits_submap_map<K,V>(smaller:map<K,V>, larger:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat)
  requires smaller.Keys <= larger.Keys
  requires forall key | key in smaller :: smaller[key] == larger[key]
  ensures MaxLeafBits_map(smaller, keyWeight, valueWeight) <= MaxLeafBits_map(larger, keyWeight, valueWeight)
{
  forall key | key in smaller
    ensures keyWeight(key) <= MaxLeafBits_map(larger, keyWeight, valueWeight)
    ensures valueWeight(smaller[key]) <= MaxLeafBits_map(larger, keyWeight, valueWeight)
  { max_leaf_bits_member_map(larger, keyWeight, valueWeight, key); }
  max_leaf_bits_bound_map(smaller, keyWeight, valueWeight, MaxLeafBits_map(larger, keyWeight, valueWeight));
}

// Persistent insertion may replace a map value; its weight must be included.
lemma max_leaf_bits_insert_set<E>(items:set<E>, weight:E -> nat, item:E)
  ensures MaxLeafBits_set(items+{item}, weight) <= MaxLeafWeight(MaxLeafBits_set(items, weight), weight(item))
{ max_by_insert(items, item, weight); }

lemma max_leaf_bits_insert_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, key:K, value:V)
  ensures MaxLeafBits_map(items[key:=value], keyWeight, valueWeight) <=
    MaxLeafWeight(MaxLeafBits_map(items, keyWeight, valueWeight), MaxLeafWeight(keyWeight(key), valueWeight(value)))
{
  var bound := MaxLeafWeight(MaxLeafBits_map(items, keyWeight, valueWeight), MaxLeafWeight(keyWeight(key), valueWeight(value)));
  forall item | item in items[key:=value]
    ensures keyWeight(item) <= bound && valueWeight(items[key:=value][item]) <= bound
  {
    if item != key { max_leaf_bits_member_map(items, keyWeight, valueWeight, item); }
  }
  max_leaf_bits_bound_map(items[key:=value], keyWeight, valueWeight, bound);
}

// Bridge a child's maximum to its exact reference size before composing a
// parent. This proves input-size relevance, not just a bound in free parameters.
lemma max_leaf_bits_size_set<E>(items:set<E>, leafWeight:E -> nat, sizeWeight:E -> nat)
  requires forall item | item in items :: leafWeight(item) <= sizeWeight(item)
  ensures MaxLeafBits_set(items, leafWeight) <= Size_set(items, sizeWeight)
{
  size_properties_set(items, sizeWeight);
  forall item | item in items
    ensures leafWeight(item) <= Size_set(items, sizeWeight)
  { size_member_set(items, sizeWeight, item); }
  max_leaf_bits_bound_set(items, leafWeight, Size_set(items, sizeWeight));
}

lemma max_leaf_bits_size_map<K,V>(items:map<K,V>, keyLeaf:K -> nat, valueLeaf:V -> nat,
    keySize:K -> nat, valueSize:V -> nat)
  requires forall key | key in items :: keyLeaf(key) <= keySize(key) && valueLeaf(items[key]) <= valueSize(items[key])
  ensures MaxLeafBits_map(items, keyLeaf, valueLeaf) <= Size_map(items, keySize, valueSize)
{
  size_properties_map(items, keySize, valueSize);
  forall key | key in items
    ensures keyLeaf(key) <= Size_map(items, keySize, valueSize)
    ensures valueLeaf(items[key]) <= Size_map(items, keySize, valueSize)
  { size_member_map(items, keySize, valueSize, key); }
  max_leaf_bits_bound_map(items, keyLeaf, valueLeaf, Size_map(items, keySize, valueSize));
}

// Flat shape bridges: exact size <= structural envelope <= fixed polynomial
// of exact size. Leaf maxima are derived from the contents, including zero
// weights and empty inputs; bit interpretations remain the caller's fixed model.
lemma representation_bound_set<E>(items:set<E>, weight:E -> nat)
  ensures |items| <= Size_set(items, weight)
  ensures MaxLeafBits_set(items, weight) <= Size_set(items, weight)
  ensures Size_set(items, weight) <= StructuralSize(|items|, MaxLeafBits_set(items, weight))
  ensures StructuralSize(|items|, MaxLeafBits_set(items, weight)) <= 4*NatPower(Size_set(items, weight)+1, 2)
{
  var bits := MaxLeafBits_set(items, weight);
  forall item | item in items
    ensures weight(item) <= bits
  { max_leaf_bits_member_set(items, weight, item); }
  structural_size_set(items, weight, |items|, 0, bits, false);
  size_properties_set(items, weight);
  max_leaf_bits_size_set(items, weight, weight);
  structural_size_polynomial(|items|, bits, Size_set(items, weight), 1, 1);
}

lemma representation_bound_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat)
  ensures |items| <= Size_map(items, keyWeight, valueWeight)
  ensures MaxLeafBits_map(items, keyWeight, valueWeight) <= Size_map(items, keyWeight, valueWeight)
  ensures Size_map(items, keyWeight, valueWeight) <= StructuralSize(|items|, MaxLeafBits_map(items, keyWeight, valueWeight))
  ensures StructuralSize(|items|, MaxLeafBits_map(items, keyWeight, valueWeight)) <=
    4*NatPower(Size_map(items, keyWeight, valueWeight)+1, 2)
{
  var bits := MaxLeafBits_map(items, keyWeight, valueWeight);
  forall key | key in items
    ensures keyWeight(key) <= bits && valueWeight(items[key]) <= bits
  { max_leaf_bits_member_map(items, keyWeight, valueWeight, key); }
  structural_size_map(items, keyWeight, valueWeight, |items|, 0, bits, false);
  size_properties_map(items, keyWeight, valueWeight);
  max_leaf_bits_size_map(items, keyWeight, valueWeight, keyWeight, valueWeight);
  structural_size_polynomial(|items|, bits, Size_map(items, keyWeight, valueWeight), 1, 1);
}

// Nested set bridges use independent dimensional maxima, not the maximum of
// complete child volumes. The same interpretation passes to every contained leaf.
lemma representation_bound_setset<E>(items:set<set<E>>, weight:E -> nat)
  ensures var size := Size_set(items, child => Size_set(child, weight));
    |items| <= size && MaxCardinality_set(items) <= size &&
    MaxLeafBits_setset(items, weight) <= size &&
    size <= StructuralSize(StructuralVolume_setset(items), MaxLeafBits_setset(items, weight)) <= 7*NatPower(size+1, 3)
{
  var exact := (child:set<E>) => Size_set(child, weight);
  var leaf := (child:set<E>) => MaxLeafBits_set(child, weight);
  var size := Size_set(items, exact);
  var bits := MaxLeafBits_setset(items, weight);
  var width := MaxCardinality_set(items);
  size_properties_set(items, exact);
  forall child | child in items
    ensures exact(child) <= StructuralSize(width, bits)
    ensures leaf(child) <= exact(child) && |child| <= size
  {
    representation_bound_set(child, weight);
    max_by_member(items, child, member => |member|);
    max_leaf_bits_member_set(items, leaf, child);
    structural_size_monotonic(|child|, leaf(child), width, bits);
    size_member_set(items, exact, child);
  }
  structural_size_set(items, exact, |items|, width, bits, true);
  max_leaf_bits_size_set(items, leaf, exact);
  max_by_bound(items, size, child => |child|);
  structural_volume_polynomial(|items|, width, size, 1, 1);
  structural_size_polynomial(StructuralVolume_setset(items), bits, size, 2, 2);
}

lemma representation_bound_setsetset<E>(items:set<set<set<E>>>, weight:E -> nat)
  ensures var size := Size_set(items, sets => Size_set(sets, child => Size_set(child, weight)));
    |items| <= size && MaxCardinality_set(items) <= size && MaxMemberCardinality_setset(items) <= size &&
    MaxLeafBits_setsetset(items, weight) <= size &&
    size <= StructuralSize(StructuralVolume_setsetset(items), MaxLeafBits_setsetset(items, weight)) <= 10*NatPower(size+1, 4)
{
  var exact := (sets:set<set<E>>) => Size_set(sets, child => Size_set(child, weight));
  var leaf := (sets:set<set<E>>) => MaxLeafBits_setset(sets, weight);
  var size := Size_set(items, exact);
  var bits := MaxLeafBits_setsetset(items, weight);
  var width := MaxCardinality_set(items);
  var innerWidth := MaxMemberCardinality_setset(items);
  var childVolume := StructuralVolume(width, innerWidth);
  size_properties_set(items, exact);
  forall sets | sets in items
    ensures exact(sets) <= StructuralSize(childVolume, bits)
    ensures leaf(sets) <= exact(sets)
    ensures |sets| <= size && MaxCardinality_set(sets) <= size
  {
    representation_bound_setset(sets, weight);
    max_by_member(items, sets, child => |child|);
    max_by_member(items, sets, child => MaxCardinality_set(child));
    max_leaf_bits_member_set(items, leaf, sets);
    structural_volume_monotonic(|sets|, MaxCardinality_set(sets), width, innerWidth);
    structural_size_monotonic(StructuralVolume_setset(sets), leaf(sets), childVolume, bits);
    size_member_set(items, exact, sets);
  }
  structural_size_set(items, exact, |items|, childVolume, bits, true);
  max_leaf_bits_size_set(items, leaf, exact);
  max_by_bound(items, size, sets => |sets|);
  max_by_bound(items, size, sets => MaxCardinality_set(sets));
  structural_volume_polynomial(width, innerWidth, size, 1, 1);
  structural_volume_polynomial(|items|, childVolume, size, 2, 2);
  structural_size_polynomial(StructuralVolume_setsetset(items), bits, size, 3, 3);
}

// Nested map bridges include every value field as well as all key leaves.
// Even empty nested keys may distinguish entries through intermediate values.
lemma representation_bound_map_set_t<K,V>(items:map<set<K>,V>, keyWeight:K -> nat, valueWeight:V -> nat)
  ensures var size := Size_map(items, key => Size_set(key, keyWeight), valueWeight);
    |items| <= size && MaxCardinality_set(items.Keys) <= size &&
    MaxLeafBits_map_set_t(items, keyWeight, valueWeight) <= size &&
    size <= StructuralSize(StructuralVolume_map_set_t(items), MaxLeafBits_map_set_t(items, keyWeight, valueWeight)) <=
      7*NatPower(size+1, 3)
{
  var exact := (key:set<K>) => Size_set(key, keyWeight);
  var leaf := (key:set<K>) => MaxLeafBits_set(key, keyWeight);
  var size := Size_map(items, exact, valueWeight);
  var bits := MaxLeafBits_map_set_t(items, keyWeight, valueWeight);
  var width := MaxCardinality_set(items.Keys);
  size_properties_map(items, exact, valueWeight);
  forall key | key in items
    ensures exact(key) <= StructuralSize(width, bits) && valueWeight(items[key]) <= bits
    ensures leaf(key) <= exact(key) && |key| <= size
  {
    representation_bound_set(key, keyWeight);
    max_by_member(items.Keys, key, child => |child|);
    max_leaf_bits_member_map(items, leaf, valueWeight, key);
    structural_size_monotonic(|key|, leaf(key), width, bits);
    size_member_map(items, exact, valueWeight, key);
  }
  structural_size_map(items, exact, valueWeight, |items|, width, bits, true);
  max_leaf_bits_size_map(items, leaf, valueWeight, exact, valueWeight);
  max_by_bound(items.Keys, size, key => |key|);
  structural_volume_polynomial(|items|, width, size, 1, 1);
  structural_size_polynomial(StructuralVolume_map_set_t(items), bits, size, 2, 2);
}

lemma representation_bound_map_map_t<K,V,W>(items:map<map<K,V>,W>, keyWeight:K -> nat,
    innerValueWeight:V -> nat, valueWeight:W -> nat)
  ensures var size := Size_map(items, key => Size_map(key, keyWeight, innerValueWeight), valueWeight);
    |items| <= size && MaxCardinality_map(items.Keys) <= size &&
    MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight) <= size &&
    size <= StructuralSize(StructuralVolume_map_map_t(items), MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight)) <=
      7*NatPower(size+1, 3)
{
  var exact := (key:map<K,V>) => Size_map(key, keyWeight, innerValueWeight);
  var leaf := (key:map<K,V>) => MaxLeafBits_map(key, keyWeight, innerValueWeight);
  var size := Size_map(items, exact, valueWeight);
  var bits := MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight);
  var width := MaxCardinality_map(items.Keys);
  size_properties_map(items, exact, valueWeight);
  forall key | key in items
    ensures exact(key) <= StructuralSize(width, bits) && valueWeight(items[key]) <= bits
    ensures leaf(key) <= exact(key) && |key| <= size
  {
    representation_bound_map(key, keyWeight, innerValueWeight);
    max_by_member(items.Keys, key, child => |child|);
    max_leaf_bits_member_map(items, leaf, valueWeight, key);
    structural_size_monotonic(|key|, leaf(key), width, bits);
    size_member_map(items, exact, valueWeight, key);
  }
  structural_size_map(items, exact, valueWeight, |items|, width, bits, true);
  max_leaf_bits_size_map(items, leaf, valueWeight, exact, valueWeight);
  max_by_bound(items.Keys, size, key => |key|);
  structural_volume_polynomial(|items|, width, size, 1, 1);
  structural_size_polynomial(StructuralVolume_map_map_t(items), bits, size, 2, 2);
}

lemma representation_bound_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>, keyWeight:K -> nat,
    innerValueWeight:V -> nat, valueWeight:W -> nat)
  ensures var size := Size_map(items, key => Size_map(key, child => Size_set(child, keyWeight), innerValueWeight), valueWeight);
    |items| <= size && MaxCardinality_map(items.Keys) <= size && MaxSetKeyCardinality_map_set_t(items.Keys) <= size &&
    MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight) <= size &&
    size <= StructuralSize(StructuralVolume_map_mapset_t(items), MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)) <=
      10*NatPower(size+1, 4)
{
  var exact := (key:map<set<K>,V>) => Size_map(key, child => Size_set(child, keyWeight), innerValueWeight);
  var leaf := (key:map<set<K>,V>) => MaxLeafBits_map_set_t(key, keyWeight, innerValueWeight);
  var size := Size_map(items, exact, valueWeight);
  var bits := MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight);
  var width := MaxCardinality_map(items.Keys);
  var innerWidth := MaxSetKeyCardinality_map_set_t(items.Keys);
  var childVolume := StructuralVolume(width, innerWidth);
  size_properties_map(items, exact, valueWeight);
  forall key | key in items
    ensures exact(key) <= StructuralSize(childVolume, bits) && valueWeight(items[key]) <= bits
    ensures leaf(key) <= exact(key)
    ensures |key| <= size && MaxCardinality_set(key.Keys) <= size
  {
    representation_bound_map_set_t(key, keyWeight, innerValueWeight);
    max_by_member(items.Keys, key, child => |child|);
    max_by_member(items.Keys, key, KeyCardinality_map_set_t);
    max_leaf_bits_member_map(items, leaf, valueWeight, key);
    structural_volume_monotonic(|key|, MaxCardinality_set(key.Keys), width, innerWidth);
    structural_size_monotonic(StructuralVolume_map_set_t(key), leaf(key), childVolume, bits);
    size_member_map(items, exact, valueWeight, key);
  }
  structural_size_map(items, exact, valueWeight, |items|, childVolume, bits, true);
  max_leaf_bits_size_map(items, leaf, valueWeight, exact, valueWeight);
  max_by_bound(items.Keys, size, key => |key|);
  max_by_bound(items.Keys, size, KeyCardinality_map_set_t);
  assert {:split_here} true;
  structural_volume_polynomial(width, innerWidth, size, 1, 1);
  structural_volume_polynomial(|items|, childVolume, size, 2, 2);
  structural_size_polynomial(StructuralVolume_map_mapset_t(items), bits, size, 3, 3);
}

// Model/universe transport. Native inclusion suffices for sets; maps must
// preserve bindings. A conditional premise lets traits use validity to guard
// the bounds on total measures.
lemma representation_subset_set<E>(smaller:set<E>, larger:set<E>, weight:E -> nat, condition:bool := true)
  requires condition ==> smaller <= larger
  ensures condition ==> |smaller| <= |larger|
  ensures condition ==> MaxLeafBits_set(smaller, weight) <= MaxLeafBits_set(larger, weight)
  ensures condition ==>
    StructuralSize(|smaller|, MaxLeafBits_set(smaller, weight)) <=
    StructuralSize(|larger|, MaxLeafBits_set(larger, weight))
{
  if condition {
    subset_cardinality_bound_set(smaller, larger);
    max_leaf_bits_subset_set(smaller, larger, weight);
    structural_size_monotonic(|smaller|, MaxLeafBits_set(smaller, weight), |larger|, MaxLeafBits_set(larger, weight));
  }
}

lemma representation_subset_setset<E>(smaller:set<set<E>>, larger:set<set<E>>, weight:E -> nat, condition:bool := true)
  requires condition ==> smaller <= larger
  ensures condition ==> StructuralVolume_setset(smaller) <= StructuralVolume_setset(larger)
  ensures condition ==> MaxLeafBits_setset(smaller, weight) <= MaxLeafBits_setset(larger, weight)
  ensures condition ==>
    StructuralSize(StructuralVolume_setset(smaller), MaxLeafBits_setset(smaller, weight)) <=
    StructuralSize(StructuralVolume_setset(larger), MaxLeafBits_setset(larger, weight))
{
  if condition {
    subset_cardinality_bound_set(smaller, larger);
    max_by_monotonic(smaller, larger, child => |child|);
    structural_volume_monotonic(|smaller|, MaxCardinality_set(smaller), |larger|, MaxCardinality_set(larger));
    max_leaf_bits_subset_set(smaller, larger, child => MaxLeafBits_set(child, weight));
    structural_size_monotonic(StructuralVolume_setset(smaller), MaxLeafBits_setset(smaller, weight),
      StructuralVolume_setset(larger), MaxLeafBits_setset(larger, weight));
  }
}

lemma representation_subset_setsetset<E>(smaller:set<set<set<E>>>, larger:set<set<set<E>>>, weight:E -> nat, condition:bool := true)
  requires condition ==> smaller <= larger
  ensures condition ==> StructuralVolume_setsetset(smaller) <= StructuralVolume_setsetset(larger)
  ensures condition ==> MaxLeafBits_setsetset(smaller, weight) <= MaxLeafBits_setsetset(larger, weight)
  ensures condition ==>
    StructuralSize(StructuralVolume_setsetset(smaller), MaxLeafBits_setsetset(smaller, weight)) <=
    StructuralSize(StructuralVolume_setsetset(larger), MaxLeafBits_setsetset(larger, weight))
{
  if condition {
    subset_cardinality_bound_set(smaller, larger);
    max_by_monotonic(smaller, larger, child => |child|);
    max_by_monotonic(smaller, larger, child => MaxCardinality_set(child));
    structural_volume_monotonic(MaxCardinality_set(smaller), MaxMemberCardinality_setset(smaller),
      MaxCardinality_set(larger), MaxMemberCardinality_setset(larger));
    structural_volume_monotonic(|smaller|, StructuralVolume(MaxCardinality_set(smaller), MaxMemberCardinality_setset(smaller)),
      |larger|, StructuralVolume(MaxCardinality_set(larger), MaxMemberCardinality_setset(larger)));
    max_leaf_bits_subset_set(smaller, larger, child => MaxLeafBits_setset(child, weight));
    structural_size_monotonic(StructuralVolume_setsetset(smaller), MaxLeafBits_setsetset(smaller, weight),
      StructuralVolume_setsetset(larger), MaxLeafBits_setsetset(larger, weight));
  }
}

lemma representation_submap_map<K,V>(smaller:map<K,V>, larger:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> |smaller| <= |larger|
  ensures condition ==> MaxLeafBits_map(smaller, keyWeight, valueWeight) <= MaxLeafBits_map(larger, keyWeight, valueWeight)
  ensures condition ==>
    StructuralSize(|smaller|, MaxLeafBits_map(smaller, keyWeight, valueWeight)) <=
    StructuralSize(|larger|, MaxLeafBits_map(larger, keyWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_leaf_bits_submap_map(smaller, larger, keyWeight, valueWeight);
    structural_size_monotonic(|smaller|, MaxLeafBits_map(smaller, keyWeight, valueWeight),
      |larger|, MaxLeafBits_map(larger, keyWeight, valueWeight));
  }
}

lemma representation_submap_map_set_t<K,V>(smaller:map<set<K>,V>, larger:map<set<K>,V>,
    keyWeight:K -> nat, valueWeight:V -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> StructuralVolume_map_set_t(smaller) <= StructuralVolume_map_set_t(larger)
  ensures condition ==> MaxLeafBits_map_set_t(smaller, keyWeight, valueWeight) <= MaxLeafBits_map_set_t(larger, keyWeight, valueWeight)
  ensures condition ==>
    StructuralSize(StructuralVolume_map_set_t(smaller), MaxLeafBits_map_set_t(smaller, keyWeight, valueWeight)) <=
    StructuralSize(StructuralVolume_map_set_t(larger), MaxLeafBits_map_set_t(larger, keyWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_by_monotonic(smaller.Keys, larger.Keys, key => |key|);
    structural_volume_monotonic(|smaller|, MaxCardinality_set(smaller.Keys), |larger|, MaxCardinality_set(larger.Keys));
    max_leaf_bits_submap_map(smaller, larger, key => MaxLeafBits_set(key, keyWeight), valueWeight);
    structural_size_monotonic(StructuralVolume_map_set_t(smaller), MaxLeafBits_map_set_t(smaller, keyWeight, valueWeight),
      StructuralVolume_map_set_t(larger), MaxLeafBits_map_set_t(larger, keyWeight, valueWeight));
  }
}

lemma representation_submap_map_map_t<K,V,W>(smaller:map<map<K,V>,W>, larger:map<map<K,V>,W>,
    keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> StructuralVolume_map_map_t(smaller) <= StructuralVolume_map_map_t(larger)
  ensures condition ==> MaxLeafBits_map_map_t(smaller, keyWeight, innerValueWeight, valueWeight) <=
    MaxLeafBits_map_map_t(larger, keyWeight, innerValueWeight, valueWeight)
  ensures condition ==>
    StructuralSize(StructuralVolume_map_map_t(smaller), MaxLeafBits_map_map_t(smaller, keyWeight, innerValueWeight, valueWeight)) <=
    StructuralSize(StructuralVolume_map_map_t(larger), MaxLeafBits_map_map_t(larger, keyWeight, innerValueWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_by_monotonic(smaller.Keys, larger.Keys, key => |key|);
    structural_volume_monotonic(|smaller|, MaxCardinality_map(smaller.Keys), |larger|, MaxCardinality_map(larger.Keys));
    max_leaf_bits_submap_map(smaller, larger, key => MaxLeafBits_map(key, keyWeight, innerValueWeight), valueWeight);
    structural_size_monotonic(StructuralVolume_map_map_t(smaller), MaxLeafBits_map_map_t(smaller, keyWeight, innerValueWeight, valueWeight),
      StructuralVolume_map_map_t(larger), MaxLeafBits_map_map_t(larger, keyWeight, innerValueWeight, valueWeight));
  }
}

lemma representation_submap_map_mapset_t<K,V,W>(smaller:map<map<set<K>,V>,W>, larger:map<map<set<K>,V>,W>,
    keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> StructuralVolume_map_mapset_t(smaller) <= StructuralVolume_map_mapset_t(larger)
  ensures condition ==> MaxLeafBits_map_mapset_t(smaller, keyWeight, innerValueWeight, valueWeight) <=
    MaxLeafBits_map_mapset_t(larger, keyWeight, innerValueWeight, valueWeight)
  ensures condition ==>
    StructuralSize(StructuralVolume_map_mapset_t(smaller), MaxLeafBits_map_mapset_t(smaller, keyWeight, innerValueWeight, valueWeight)) <=
    StructuralSize(StructuralVolume_map_mapset_t(larger), MaxLeafBits_map_mapset_t(larger, keyWeight, innerValueWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_by_monotonic(smaller.Keys, larger.Keys, key => |key|);
    max_by_monotonic(smaller.Keys, larger.Keys, KeyCardinality_map_set_t);
    structural_volume_monotonic(MaxCardinality_map(smaller.Keys), MaxSetKeyCardinality_map_set_t(smaller.Keys),
      MaxCardinality_map(larger.Keys), MaxSetKeyCardinality_map_set_t(larger.Keys));
    structural_volume_monotonic(|smaller|, StructuralVolume(MaxCardinality_map(smaller.Keys), MaxSetKeyCardinality_map_set_t(smaller.Keys)),
      |larger|, StructuralVolume(MaxCardinality_map(larger.Keys), MaxSetKeyCardinality_map_set_t(larger.Keys)));
    max_leaf_bits_submap_map(smaller, larger, key => MaxLeafBits_map_set_t(key, keyWeight, innerValueWeight), valueWeight);
    structural_size_monotonic(StructuralVolume_map_mapset_t(smaller), MaxLeafBits_map_mapset_t(smaller, keyWeight, innerValueWeight, valueWeight),
      StructuralVolume_map_mapset_t(larger), MaxLeafBits_map_mapset_t(larger, keyWeight, innerValueWeight, valueWeight));
  }
}

// Selected fields and children fit their receiver, including empty children.
lemma representation_member_set<E>(items:set<E>, weight:E -> nat, item:E)
  requires item in items
  ensures weight(item) <= RepresentationSize_set(items, weight)
  ensures weight(item) <= MaxLeafBits_set(items, weight)
  {
    max_leaf_bits_member_set(items, weight, item);
  }

lemma representation_member_setset<E>(items:set<set<E>>, weight:E -> nat, item:set<E>)
  requires item in items
  ensures RepresentationSize_set(item, weight) <= RepresentationSize_setset(items, weight)
  ensures MaxLeafBits_set(item, weight) <= MaxLeafBits_setset(items, weight)
  {
    max_leaf_bits_member_set(items, child => MaxLeafBits_set(child, weight), item);
    max_by_member(items, item, child => |child|);
    structural_size_monotonic(|item|, MaxLeafBits_set(item, weight), StructuralVolume_setset(items), MaxLeafBits_setset(items, weight));
  }

lemma representation_member_setsetset<E>(items:set<set<set<E>>>, weight:E -> nat, item:set<set<E>>)
  requires item in items
  ensures RepresentationSize_setset(item, weight) <= RepresentationSize_setsetset(items, weight)
  ensures MaxLeafBits_setset(item, weight) <= MaxLeafBits_setsetset(items, weight)
  {
    max_leaf_bits_member_set(items, child => MaxLeafBits_setset(child, weight), item);
    max_by_member(items, item, child => |child|);
    max_by_member(items, item, child => MaxCardinality_set(child));
    structural_volume_monotonic(|item|, MaxCardinality_set(item), MaxCardinality_set(items), MaxMemberCardinality_setset(items));
    structural_size_monotonic(StructuralVolume_setset(item), MaxLeafBits_setset(item, weight), StructuralVolume_setsetset(items), MaxLeafBits_setsetset(items, weight));
  }

lemma representation_member_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, item:K)
  requires item in items
  ensures keyWeight(item) <= RepresentationSize_map(items, keyWeight, valueWeight)
  ensures keyWeight(item) <= MaxLeafBits_map(items, keyWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSize_map(items, keyWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, keyWeight, valueWeight, item);
  }

lemma representation_member_map_set_t<K,V>(items:map<set<K>,V>, keyWeight:K -> nat, valueWeight:V -> nat, item:set<K>)
  requires item in items
  ensures RepresentationSize_set(item, keyWeight) <= RepresentationSize_map_set_t(items, keyWeight, valueWeight)
  ensures MaxLeafBits_set(item, keyWeight) <= MaxLeafBits_map_set_t(items, keyWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSize_map_set_t(items, keyWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, key => MaxLeafBits_set(key, keyWeight), valueWeight, item);
    max_by_member(items.Keys, item, child => |child|);
    structural_size_monotonic(|item|, MaxLeafBits_set(item, keyWeight), StructuralVolume_map_set_t(items), MaxLeafBits_map_set_t(items, keyWeight, valueWeight));
  }

lemma representation_member_map_map_t<K,V,W>(items:map<map<K,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, item:map<K,V>)
  requires item in items
  ensures RepresentationSize_map(item, keyWeight, innerValueWeight) <= RepresentationSize_map_map_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures MaxLeafBits_map(item, keyWeight, innerValueWeight) <= MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSize_map_map_t(items, keyWeight, innerValueWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, key => MaxLeafBits_map(key, keyWeight, innerValueWeight), valueWeight, item);
    max_by_member(items.Keys, item, child => |child|);
    structural_size_monotonic(|item|, MaxLeafBits_map(item, keyWeight, innerValueWeight), StructuralVolume_map_map_t(items),
        MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight));
  }

lemma representation_member_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, item:map<set<K>,V>)
  requires item in items
  ensures RepresentationSize_map_set_t(item, keyWeight, innerValueWeight) <= RepresentationSize_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures MaxLeafBits_map_set_t(item, keyWeight, innerValueWeight) <= MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSize_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, key => MaxLeafBits_map_set_t(key, keyWeight, innerValueWeight), valueWeight, item);
    max_by_member(items.Keys, item, child => |child|);
    max_by_member(items.Keys, item, KeyCardinality_map_set_t);
    structural_volume_monotonic(|item|, MaxCardinality_set(item.Keys), MaxCardinality_map(items.Keys), MaxSetKeyCardinality_map_set_t(items.Keys));
    structural_size_monotonic(StructuralVolume_map_set_t(item), MaxLeafBits_map_set_t(item, keyWeight, innerValueWeight),
        StructuralVolume_map_mapset_t(items), MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight));
  }
