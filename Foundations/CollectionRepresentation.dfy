include "CollectionMaxima.dfy"
include "StructuralSizes.dfy"
include "CollectionLaws.dfy"

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
ghost function StructuralVolumeBound_setset<E>(items:set<set<E>>):nat
{ StructuralVolumeBound(|items|, MaxCardinality_set(items)) }

ghost function StructuralVolumeBound_setsetset<E>(items:set<set<set<E>>>):nat
{ StructuralVolumeBound(|items|, StructuralVolumeBound(MaxCardinality_set(items), MaxMemberCardinality_setset(items))) }

ghost function StructuralVolumeBound_map_set_t<K,V>(items:map<set<K>,V>):nat
{ StructuralVolumeBound(|items|, MaxCardinality_set(items.Keys)) }

ghost function StructuralVolumeBound_map_map_t<K,V,W>(items:map<map<K,V>,W>):nat
{ StructuralVolumeBound(|items|, MaxCardinality_map(items.Keys)) }

ghost function StructuralVolumeBound_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>):nat
{ StructuralVolumeBound(|items|, StructuralVolumeBound(MaxCardinality_map(items.Keys), MaxSetKeyCardinality_map_set_t(items.Keys))) }

// Uniform envelopes used by receivers and external compound operands.
ghost function RepresentationSizeBound_set<E>(items:set<E>, weight:E -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_set(items, weight) <= size
{ RepresentationSizeBound(|items|, MaxLeafBits_set(items, weight)) }

ghost function RepresentationSizeBound_setset<E>(items:set<set<E>>, weight:E -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_setset(items, weight) <= size
{ RepresentationSizeBound(StructuralVolumeBound_setset(items), MaxLeafBits_setset(items, weight)) }

ghost function RepresentationSizeBound_setsetset<E>(items:set<set<set<E>>>, weight:E -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_setsetset(items, weight) <= size
{ RepresentationSizeBound(StructuralVolumeBound_setsetset(items), MaxLeafBits_setsetset(items, weight)) }

ghost function RepresentationSizeBound_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map(items, keyWeight, valueWeight) <= size
{ RepresentationSizeBound(|items|, MaxLeafBits_map(items, keyWeight, valueWeight)) }

ghost function RepresentationSizeBound_map_set_t<K,V>(items:map<set<K>,V>, keyWeight:K -> nat, valueWeight:V -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map_set_t(items, keyWeight, valueWeight) <= size
{ RepresentationSizeBound(StructuralVolumeBound_map_set_t(items), MaxLeafBits_map_set_t(items, keyWeight, valueWeight)) }

ghost function RepresentationSizeBound_map_map_t<K,V,W>(items:map<map<K,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight) <= size
{ RepresentationSizeBound(StructuralVolumeBound_map_map_t(items), MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight)) }

ghost function RepresentationSizeBound_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat):(size:nat)
  ensures 1 <= size
  ensures MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight) <= size
{ RepresentationSizeBound(StructuralVolumeBound_map_mapset_t(items), MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)) }

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

// Model/universe transport. Native inclusion suffices for sets; maps must
// preserve bindings. A conditional premise lets traits use validity to guard
// the bounds on total measures.
lemma representation_subset_set<E>(smaller:set<E>, larger:set<E>, weight:E -> nat, condition:bool := true)
  requires condition ==> smaller <= larger
  ensures condition ==> |smaller| <= |larger|
  ensures condition ==> MaxLeafBits_set(smaller, weight) <= MaxLeafBits_set(larger, weight)
  ensures condition ==>
    RepresentationSizeBound(|smaller|, MaxLeafBits_set(smaller, weight)) <=
    RepresentationSizeBound(|larger|, MaxLeafBits_set(larger, weight))
{
  if condition {
    subset_cardinality_bound_set(smaller, larger);
    max_leaf_bits_subset_set(smaller, larger, weight);
    representation_size_bound_monotonic(|smaller|, MaxLeafBits_set(smaller, weight), |larger|, MaxLeafBits_set(larger, weight));
  }
}

lemma representation_subset_setset<E>(smaller:set<set<E>>, larger:set<set<E>>, weight:E -> nat, condition:bool := true)
  requires condition ==> smaller <= larger
  ensures condition ==> StructuralVolumeBound_setset(smaller) <= StructuralVolumeBound_setset(larger)
  ensures condition ==> MaxLeafBits_setset(smaller, weight) <= MaxLeafBits_setset(larger, weight)
  ensures condition ==>
    RepresentationSizeBound(StructuralVolumeBound_setset(smaller), MaxLeafBits_setset(smaller, weight)) <=
    RepresentationSizeBound(StructuralVolumeBound_setset(larger), MaxLeafBits_setset(larger, weight))
{
  if condition {
    subset_cardinality_bound_set(smaller, larger);
    max_by_monotonic(smaller, larger, child => |child|);
    structural_volume_bound_monotonic(|smaller|, MaxCardinality_set(smaller), |larger|, MaxCardinality_set(larger));
    max_leaf_bits_subset_set(smaller, larger, child => MaxLeafBits_set(child, weight));
    representation_size_bound_monotonic(StructuralVolumeBound_setset(smaller), MaxLeafBits_setset(smaller, weight),
      StructuralVolumeBound_setset(larger), MaxLeafBits_setset(larger, weight));
  }
}

lemma representation_subset_setsetset<E>(smaller:set<set<set<E>>>, larger:set<set<set<E>>>, weight:E -> nat, condition:bool := true)
  requires condition ==> smaller <= larger
  ensures condition ==> StructuralVolumeBound_setsetset(smaller) <= StructuralVolumeBound_setsetset(larger)
  ensures condition ==> MaxLeafBits_setsetset(smaller, weight) <= MaxLeafBits_setsetset(larger, weight)
  ensures condition ==>
    RepresentationSizeBound(StructuralVolumeBound_setsetset(smaller), MaxLeafBits_setsetset(smaller, weight)) <=
    RepresentationSizeBound(StructuralVolumeBound_setsetset(larger), MaxLeafBits_setsetset(larger, weight))
{
  if condition {
    subset_cardinality_bound_set(smaller, larger);
    max_by_monotonic(smaller, larger, child => |child|);
    max_by_monotonic(smaller, larger, child => MaxCardinality_set(child));
    structural_volume_bound_monotonic(MaxCardinality_set(smaller), MaxMemberCardinality_setset(smaller),
      MaxCardinality_set(larger), MaxMemberCardinality_setset(larger));
    structural_volume_bound_monotonic(|smaller|, StructuralVolumeBound(MaxCardinality_set(smaller), MaxMemberCardinality_setset(smaller)),
      |larger|, StructuralVolumeBound(MaxCardinality_set(larger), MaxMemberCardinality_setset(larger)));
    max_leaf_bits_subset_set(smaller, larger, child => MaxLeafBits_setset(child, weight));
    representation_size_bound_monotonic(StructuralVolumeBound_setsetset(smaller), MaxLeafBits_setsetset(smaller, weight),
      StructuralVolumeBound_setsetset(larger), MaxLeafBits_setsetset(larger, weight));
  }
}

lemma representation_submap_map<K,V>(smaller:map<K,V>, larger:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> |smaller| <= |larger|
  ensures condition ==> MaxLeafBits_map(smaller, keyWeight, valueWeight) <= MaxLeafBits_map(larger, keyWeight, valueWeight)
  ensures condition ==>
    RepresentationSizeBound(|smaller|, MaxLeafBits_map(smaller, keyWeight, valueWeight)) <=
    RepresentationSizeBound(|larger|, MaxLeafBits_map(larger, keyWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_leaf_bits_submap_map(smaller, larger, keyWeight, valueWeight);
    representation_size_bound_monotonic(|smaller|, MaxLeafBits_map(smaller, keyWeight, valueWeight),
      |larger|, MaxLeafBits_map(larger, keyWeight, valueWeight));
  }
}

lemma representation_submap_map_set_t<K,V>(smaller:map<set<K>,V>, larger:map<set<K>,V>,
    keyWeight:K -> nat, valueWeight:V -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> StructuralVolumeBound_map_set_t(smaller) <= StructuralVolumeBound_map_set_t(larger)
  ensures condition ==> MaxLeafBits_map_set_t(smaller, keyWeight, valueWeight) <= MaxLeafBits_map_set_t(larger, keyWeight, valueWeight)
  ensures condition ==>
    RepresentationSizeBound(StructuralVolumeBound_map_set_t(smaller), MaxLeafBits_map_set_t(smaller, keyWeight, valueWeight)) <=
    RepresentationSizeBound(StructuralVolumeBound_map_set_t(larger), MaxLeafBits_map_set_t(larger, keyWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_by_monotonic(smaller.Keys, larger.Keys, key => |key|);
    structural_volume_bound_monotonic(|smaller|, MaxCardinality_set(smaller.Keys), |larger|, MaxCardinality_set(larger.Keys));
    max_leaf_bits_submap_map(smaller, larger, key => MaxLeafBits_set(key, keyWeight), valueWeight);
    representation_size_bound_monotonic(StructuralVolumeBound_map_set_t(smaller), MaxLeafBits_map_set_t(smaller, keyWeight, valueWeight),
      StructuralVolumeBound_map_set_t(larger), MaxLeafBits_map_set_t(larger, keyWeight, valueWeight));
  }
}

lemma representation_submap_map_map_t<K,V,W>(smaller:map<map<K,V>,W>, larger:map<map<K,V>,W>,
    keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> StructuralVolumeBound_map_map_t(smaller) <= StructuralVolumeBound_map_map_t(larger)
  ensures condition ==> MaxLeafBits_map_map_t(smaller, keyWeight, innerValueWeight, valueWeight) <=
    MaxLeafBits_map_map_t(larger, keyWeight, innerValueWeight, valueWeight)
  ensures condition ==>
    RepresentationSizeBound(StructuralVolumeBound_map_map_t(smaller), MaxLeafBits_map_map_t(smaller, keyWeight, innerValueWeight, valueWeight)) <=
    RepresentationSizeBound(StructuralVolumeBound_map_map_t(larger), MaxLeafBits_map_map_t(larger, keyWeight, innerValueWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_by_monotonic(smaller.Keys, larger.Keys, key => |key|);
    structural_volume_bound_monotonic(|smaller|, MaxCardinality_map(smaller.Keys), |larger|, MaxCardinality_map(larger.Keys));
    max_leaf_bits_submap_map(smaller, larger, key => MaxLeafBits_map(key, keyWeight, innerValueWeight), valueWeight);
    representation_size_bound_monotonic(StructuralVolumeBound_map_map_t(smaller), MaxLeafBits_map_map_t(smaller, keyWeight, innerValueWeight, valueWeight),
      StructuralVolumeBound_map_map_t(larger), MaxLeafBits_map_map_t(larger, keyWeight, innerValueWeight, valueWeight));
  }
}

lemma representation_submap_map_mapset_t<K,V,W>(smaller:map<map<set<K>,V>,W>, larger:map<map<set<K>,V>,W>,
    keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, condition:bool := true)
  requires condition ==> smaller.Keys <= larger.Keys
  requires condition ==> forall key | key in smaller :: smaller[key] == larger[key]
  ensures condition ==> StructuralVolumeBound_map_mapset_t(smaller) <= StructuralVolumeBound_map_mapset_t(larger)
  ensures condition ==> MaxLeafBits_map_mapset_t(smaller, keyWeight, innerValueWeight, valueWeight) <=
    MaxLeafBits_map_mapset_t(larger, keyWeight, innerValueWeight, valueWeight)
  ensures condition ==>
    RepresentationSizeBound(StructuralVolumeBound_map_mapset_t(smaller), MaxLeafBits_map_mapset_t(smaller, keyWeight, innerValueWeight, valueWeight)) <=
    RepresentationSizeBound(StructuralVolumeBound_map_mapset_t(larger), MaxLeafBits_map_mapset_t(larger, keyWeight, innerValueWeight, valueWeight))
{
  if condition {
    subset_cardinality_bound_set(smaller.Keys, larger.Keys);
    max_by_monotonic(smaller.Keys, larger.Keys, key => |key|);
    max_by_monotonic(smaller.Keys, larger.Keys, KeyCardinality_map_set_t);
    structural_volume_bound_monotonic(MaxCardinality_map(smaller.Keys), MaxSetKeyCardinality_map_set_t(smaller.Keys),
      MaxCardinality_map(larger.Keys), MaxSetKeyCardinality_map_set_t(larger.Keys));
    structural_volume_bound_monotonic(|smaller|, StructuralVolumeBound(MaxCardinality_map(smaller.Keys), MaxSetKeyCardinality_map_set_t(smaller.Keys)),
      |larger|, StructuralVolumeBound(MaxCardinality_map(larger.Keys), MaxSetKeyCardinality_map_set_t(larger.Keys)));
    max_leaf_bits_submap_map(smaller, larger, key => MaxLeafBits_map_set_t(key, keyWeight, innerValueWeight), valueWeight);
    representation_size_bound_monotonic(StructuralVolumeBound_map_mapset_t(smaller), MaxLeafBits_map_mapset_t(smaller, keyWeight, innerValueWeight, valueWeight),
      StructuralVolumeBound_map_mapset_t(larger), MaxLeafBits_map_mapset_t(larger, keyWeight, innerValueWeight, valueWeight));
  }
}

// Selected fields and children fit their receiver, including empty children.
lemma representation_member_set<E>(items:set<E>, weight:E -> nat, item:E)
  requires item in items
  ensures weight(item) <= RepresentationSizeBound_set(items, weight)
  ensures weight(item) <= MaxLeafBits_set(items, weight)
  {
    max_leaf_bits_member_set(items, weight, item);
  }

lemma representation_member_setset<E>(items:set<set<E>>, weight:E -> nat, item:set<E>)
  requires item in items
  ensures RepresentationSizeBound_set(item, weight) <= RepresentationSizeBound_setset(items, weight)
  ensures MaxLeafBits_set(item, weight) <= MaxLeafBits_setset(items, weight)
  {
    max_leaf_bits_member_set(items, child => MaxLeafBits_set(child, weight), item);
    max_by_member(items, item, child => |child|);
    representation_size_bound_monotonic(|item|, MaxLeafBits_set(item, weight), StructuralVolumeBound_setset(items), MaxLeafBits_setset(items, weight));
  }

lemma representation_member_setsetset<E>(items:set<set<set<E>>>, weight:E -> nat, item:set<set<E>>)
  requires item in items
  ensures RepresentationSizeBound_setset(item, weight) <= RepresentationSizeBound_setsetset(items, weight)
  ensures MaxLeafBits_setset(item, weight) <= MaxLeafBits_setsetset(items, weight)
  {
    max_leaf_bits_member_set(items, child => MaxLeafBits_setset(child, weight), item);
    max_by_member(items, item, child => |child|);
    max_by_member(items, item, child => MaxCardinality_set(child));
    structural_volume_bound_monotonic(|item|, MaxCardinality_set(item), MaxCardinality_set(items), MaxMemberCardinality_setset(items));
    representation_size_bound_monotonic(StructuralVolumeBound_setset(item), MaxLeafBits_setset(item, weight),
      StructuralVolumeBound_setsetset(items), MaxLeafBits_setsetset(items, weight));
  }

lemma representation_member_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat, item:K)
  requires item in items
  ensures keyWeight(item) <= RepresentationSizeBound_map(items, keyWeight, valueWeight)
  ensures keyWeight(item) <= MaxLeafBits_map(items, keyWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSizeBound_map(items, keyWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, keyWeight, valueWeight, item);
  }

lemma representation_member_map_set_t<K,V>(items:map<set<K>,V>, keyWeight:K -> nat, valueWeight:V -> nat, item:set<K>)
  requires item in items
  ensures RepresentationSizeBound_set(item, keyWeight) <= RepresentationSizeBound_map_set_t(items, keyWeight, valueWeight)
  ensures MaxLeafBits_set(item, keyWeight) <= MaxLeafBits_map_set_t(items, keyWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSizeBound_map_set_t(items, keyWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, key => MaxLeafBits_set(key, keyWeight), valueWeight, item);
    max_by_member(items.Keys, item, child => |child|);
    representation_size_bound_monotonic(|item|, MaxLeafBits_set(item, keyWeight), StructuralVolumeBound_map_set_t(items), MaxLeafBits_map_set_t(items, keyWeight, valueWeight));
  }

lemma representation_member_map_map_t<K,V,W>(items:map<map<K,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, item:map<K,V>)
  requires item in items
  ensures RepresentationSizeBound_map(item, keyWeight, innerValueWeight) <= RepresentationSizeBound_map_map_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures MaxLeafBits_map(item, keyWeight, innerValueWeight) <= MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSizeBound_map_map_t(items, keyWeight, innerValueWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, key => MaxLeafBits_map(key, keyWeight, innerValueWeight), valueWeight, item);
    max_by_member(items.Keys, item, child => |child|);
    representation_size_bound_monotonic(|item|, MaxLeafBits_map(item, keyWeight, innerValueWeight), StructuralVolumeBound_map_map_t(items),
        MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight));
  }

lemma representation_member_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>, keyWeight:K -> nat, innerValueWeight:V -> nat, valueWeight:W -> nat, item:map<set<K>,V>)
  requires item in items
  ensures RepresentationSizeBound_map_set_t(item, keyWeight, innerValueWeight) <= RepresentationSizeBound_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures MaxLeafBits_map_set_t(item, keyWeight, innerValueWeight) <= MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)
  ensures valueWeight(items[item]) <= RepresentationSizeBound_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)
  {
    max_leaf_bits_member_map(items, key => MaxLeafBits_map_set_t(key, keyWeight, innerValueWeight), valueWeight, item);
    max_by_member(items.Keys, item, child => |child|);
    max_by_member(items.Keys, item, KeyCardinality_map_set_t);
    structural_volume_bound_monotonic(|item|, MaxCardinality_set(item.Keys), MaxCardinality_map(items.Keys), MaxSetKeyCardinality_map_set_t(items.Keys));
    representation_size_bound_monotonic(StructuralVolumeBound_map_set_t(item), MaxLeafBits_map_set_t(item, keyWeight, innerValueWeight),
        StructuralVolumeBound_map_mapset_t(items), MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight));
  }
