include "CollectionRepresentation.dfy"
include "ExactCollectionSizes.dfy"
include "../Arithmetic/PolynomialBounds.dfy"

// These two native proofs compose over all seven supported collection shapes.
// A child is weighted by its exact reference size; clients will receive the
// resulting envelope from trait contracts, not invoke these lemmas per operation.
lemma representation_size_bound_set<E>(items:set<E>, weight:E -> nat,
    count:nat, child:nat, bits:nat, nested:bool)
  requires |items| <= count && 1 <= bits
  requires !nested ==> child == 0
  requires forall item | item in items ::
    weight(item) <= (if nested then RepresentationSizeBound(child, bits) else bits)
  ensures Size_set(items, weight) <= RepresentationSizeBound(StructuralVolumeBound(count, child), bits)
{
  var maximum := if nested then RepresentationSizeBound(child, bits) else bits;
  size_bound_set(items, weight, maximum);
  nonnegative_product_monotonic(|items|, 1+maximum, count, 1+maximum+bits);
  representation_size_bound_layer(count, child, bits, nested);
}

lemma representation_size_bound_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat,
    count:nat, child:nat, bits:nat, nested:bool)
  requires |items| <= count && 1 <= bits
  requires !nested ==> child == 0
  requires forall key | key in items ::
    keyWeight(key) <= (if nested then RepresentationSizeBound(child, bits) else bits) &&
    valueWeight(items[key]) <= bits
  ensures Size_map(items, keyWeight, valueWeight) <= RepresentationSizeBound(StructuralVolumeBound(count, child), bits)
{
  var maximum := if nested then RepresentationSizeBound(child, bits) else bits;
  size_bound_map(items, keyWeight, valueWeight, maximum, bits);
  nonnegative_product_monotonic(|items|, 1+maximum+bits, count, 1+maximum+bits);
  representation_size_bound_layer(count, child, bits, nested);
}

// Polynomial composition, independently of a collection representation.
// A caller must still derive the dimension and leaf bounds from its input.
lemma structural_volume_bound_polynomial(count:nat, child:nat, n:nat, coefficient:nat, degree:nat)
  requires count <= n && child <= coefficient*NatPower(n+1, degree)
  ensures StructuralVolumeBound(count, child) <= (coefficient+1)*NatPower(n+1, degree+1)
{
  assert 1 <= NatPower(n+1, degree);
  polynomial_product_bound(n, count, 1+child, 1, coefficient+1, 1, degree);
}

lemma representation_size_bound_polynomial(volume:nat, bits:nat, n:nat, coefficient:nat, degree:nat)
  requires volume <= coefficient*NatPower(n+1, degree)
  requires 1 <= bits <= n+1
  ensures RepresentationSizeBound(volume, bits) <= (1+3*coefficient)*NatPower(n+1, degree+1)
{
  polynomial_product_bound(n, volume, bits, coefficient, 1, degree, 1);
  assert 1 <= NatPower(n+1, degree+1);
  calc {
    RepresentationSizeBound(volume, bits);
    == 1+3*(volume*bits);
    <= 1+3*(coefficient*NatPower(n+1, degree+1));
    <= NatPower(n+1, degree+1)+3*(coefficient*NatPower(n+1, degree+1));
    == (1+3*coefficient)*NatPower(n+1, degree+1);
  }
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
  ensures Size_set(items, weight) <= RepresentationSizeBound(|items|, MaxLeafBits_set(items, weight))
  ensures RepresentationSizeBound(|items|, MaxLeafBits_set(items, weight)) <= 4*NatPower(Size_set(items, weight)+1, 2)
{
  var bits := MaxLeafBits_set(items, weight);
  forall item | item in items
    ensures weight(item) <= bits
  { max_leaf_bits_member_set(items, weight, item); }
  representation_size_bound_set(items, weight, |items|, 0, bits, false);
  size_properties_set(items, weight);
  max_leaf_bits_size_set(items, weight, weight);
  representation_size_bound_polynomial(|items|, bits, Size_set(items, weight), 1, 1);
}

lemma representation_bound_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat)
  ensures |items| <= Size_map(items, keyWeight, valueWeight)
  ensures MaxLeafBits_map(items, keyWeight, valueWeight) <= Size_map(items, keyWeight, valueWeight)
  ensures Size_map(items, keyWeight, valueWeight) <= RepresentationSizeBound(|items|, MaxLeafBits_map(items, keyWeight, valueWeight))
  ensures RepresentationSizeBound(|items|, MaxLeafBits_map(items, keyWeight, valueWeight)) <=
    4*NatPower(Size_map(items, keyWeight, valueWeight)+1, 2)
{
  var bits := MaxLeafBits_map(items, keyWeight, valueWeight);
  forall key | key in items
    ensures keyWeight(key) <= bits && valueWeight(items[key]) <= bits
  { max_leaf_bits_member_map(items, keyWeight, valueWeight, key); }
  representation_size_bound_map(items, keyWeight, valueWeight, |items|, 0, bits, false);
  size_properties_map(items, keyWeight, valueWeight);
  max_leaf_bits_size_map(items, keyWeight, valueWeight, keyWeight, valueWeight);
  representation_size_bound_polynomial(|items|, bits, Size_map(items, keyWeight, valueWeight), 1, 1);
}

// Nested set bridges use independent dimensional maxima, not the maximum of
// complete child volumes. The same interpretation passes to every contained leaf.
lemma representation_bound_setset<E>(items:set<set<E>>, weight:E -> nat)
  ensures var size := Size_set(items, child => Size_set(child, weight));
    |items| <= size && MaxCardinality_set(items) <= size &&
    MaxLeafBits_setset(items, weight) <= size &&
    size <= RepresentationSizeBound(StructuralVolumeBound_setset(items), MaxLeafBits_setset(items, weight)) <= 7*NatPower(size+1, 3)
{
  var exact := (child:set<E>) => Size_set(child, weight);
  var leaf := (child:set<E>) => MaxLeafBits_set(child, weight);
  var size := Size_set(items, exact);
  var bits := MaxLeafBits_setset(items, weight);
  var width := MaxCardinality_set(items);
  size_properties_set(items, exact);
  forall child | child in items
    ensures exact(child) <= RepresentationSizeBound(width, bits)
    ensures leaf(child) <= exact(child) && |child| <= size
  {
    representation_bound_set(child, weight);
    max_by_member(items, child, member => |member|);
    max_leaf_bits_member_set(items, leaf, child);
    representation_size_bound_monotonic(|child|, leaf(child), width, bits);
    size_member_set(items, exact, child);
  }
  representation_size_bound_set(items, exact, |items|, width, bits, true);
  max_leaf_bits_size_set(items, leaf, exact);
  max_by_bound(items, size, child => |child|);
  structural_volume_bound_polynomial(|items|, width, size, 1, 1);
  representation_size_bound_polynomial(StructuralVolumeBound_setset(items), bits, size, 2, 2);
}

lemma representation_bound_setsetset<E>(items:set<set<set<E>>>, weight:E -> nat)
  ensures var size := Size_set(items, sets => Size_set(sets, child => Size_set(child, weight)));
    |items| <= size && MaxCardinality_set(items) <= size && MaxMemberCardinality_setset(items) <= size &&
    MaxLeafBits_setsetset(items, weight) <= size &&
    size <= RepresentationSizeBound(StructuralVolumeBound_setsetset(items), MaxLeafBits_setsetset(items, weight)) <= 10*NatPower(size+1, 4)
{
  var exact := (sets:set<set<E>>) => Size_set(sets, child => Size_set(child, weight));
  var leaf := (sets:set<set<E>>) => MaxLeafBits_setset(sets, weight);
  var size := Size_set(items, exact);
  var bits := MaxLeafBits_setsetset(items, weight);
  var width := MaxCardinality_set(items);
  var innerWidth := MaxMemberCardinality_setset(items);
  var childVolume := StructuralVolumeBound(width, innerWidth);
  size_properties_set(items, exact);
  forall sets | sets in items
    ensures exact(sets) <= RepresentationSizeBound(childVolume, bits)
    ensures leaf(sets) <= exact(sets)
    ensures |sets| <= size && MaxCardinality_set(sets) <= size
  {
    representation_bound_setset(sets, weight);
    max_by_member(items, sets, child => |child|);
    max_by_member(items, sets, child => MaxCardinality_set(child));
    max_leaf_bits_member_set(items, leaf, sets);
    structural_volume_bound_monotonic(|sets|, MaxCardinality_set(sets), width, innerWidth);
    representation_size_bound_monotonic(StructuralVolumeBound_setset(sets), leaf(sets), childVolume, bits);
    size_member_set(items, exact, sets);
  }
  representation_size_bound_set(items, exact, |items|, childVolume, bits, true);
  max_leaf_bits_size_set(items, leaf, exact);
  max_by_bound(items, size, sets => |sets|);
  max_by_bound(items, size, sets => MaxCardinality_set(sets));
  structural_volume_bound_polynomial(width, innerWidth, size, 1, 1);
  structural_volume_bound_polynomial(|items|, childVolume, size, 2, 2);
  representation_size_bound_polynomial(StructuralVolumeBound_setsetset(items), bits, size, 3, 3);
}

// Nested map bridges include every value field as well as all key leaves.
// Even empty nested keys may distinguish entries through intermediate values.
lemma representation_bound_map_set_t<K,V>(items:map<set<K>,V>, keyWeight:K -> nat, valueWeight:V -> nat)
  ensures var size := Size_map(items, key => Size_set(key, keyWeight), valueWeight);
    |items| <= size && MaxCardinality_set(items.Keys) <= size &&
    MaxLeafBits_map_set_t(items, keyWeight, valueWeight) <= size &&
    size <= RepresentationSizeBound(StructuralVolumeBound_map_set_t(items), MaxLeafBits_map_set_t(items, keyWeight, valueWeight)) <=
      7*NatPower(size+1, 3)
{
  var exact := (key:set<K>) => Size_set(key, keyWeight);
  var leaf := (key:set<K>) => MaxLeafBits_set(key, keyWeight);
  var size := Size_map(items, exact, valueWeight);
  var bits := MaxLeafBits_map_set_t(items, keyWeight, valueWeight);
  var width := MaxCardinality_set(items.Keys);
  size_properties_map(items, exact, valueWeight);
  forall key | key in items
    ensures exact(key) <= RepresentationSizeBound(width, bits) && valueWeight(items[key]) <= bits
    ensures leaf(key) <= exact(key) && |key| <= size
  {
    representation_bound_set(key, keyWeight);
    max_by_member(items.Keys, key, child => |child|);
    max_leaf_bits_member_map(items, leaf, valueWeight, key);
    representation_size_bound_monotonic(|key|, leaf(key), width, bits);
    size_member_map(items, exact, valueWeight, key);
  }
  representation_size_bound_map(items, exact, valueWeight, |items|, width, bits, true);
  max_leaf_bits_size_map(items, leaf, valueWeight, exact, valueWeight);
  max_by_bound(items.Keys, size, key => |key|);
  structural_volume_bound_polynomial(|items|, width, size, 1, 1);
  representation_size_bound_polynomial(StructuralVolumeBound_map_set_t(items), bits, size, 2, 2);
}

lemma representation_bound_map_map_t<K,V,W>(items:map<map<K,V>,W>, keyWeight:K -> nat,
    innerValueWeight:V -> nat, valueWeight:W -> nat)
  ensures var size := Size_map(items, key => Size_map(key, keyWeight, innerValueWeight), valueWeight);
    |items| <= size && MaxCardinality_map(items.Keys) <= size &&
    MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight) <= size &&
    size <= RepresentationSizeBound(StructuralVolumeBound_map_map_t(items), MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight)) <=
      7*NatPower(size+1, 3)
{
  var exact := (key:map<K,V>) => Size_map(key, keyWeight, innerValueWeight);
  var leaf := (key:map<K,V>) => MaxLeafBits_map(key, keyWeight, innerValueWeight);
  var size := Size_map(items, exact, valueWeight);
  var bits := MaxLeafBits_map_map_t(items, keyWeight, innerValueWeight, valueWeight);
  var width := MaxCardinality_map(items.Keys);
  size_properties_map(items, exact, valueWeight);
  forall key | key in items
    ensures exact(key) <= RepresentationSizeBound(width, bits) && valueWeight(items[key]) <= bits
    ensures leaf(key) <= exact(key) && |key| <= size
  {
    representation_bound_map(key, keyWeight, innerValueWeight);
    max_by_member(items.Keys, key, child => |child|);
    max_leaf_bits_member_map(items, leaf, valueWeight, key);
    representation_size_bound_monotonic(|key|, leaf(key), width, bits);
    size_member_map(items, exact, valueWeight, key);
  }
  representation_size_bound_map(items, exact, valueWeight, |items|, width, bits, true);
  max_leaf_bits_size_map(items, leaf, valueWeight, exact, valueWeight);
  max_by_bound(items.Keys, size, key => |key|);
  structural_volume_bound_polynomial(|items|, width, size, 1, 1);
  representation_size_bound_polynomial(StructuralVolumeBound_map_map_t(items), bits, size, 2, 2);
}

lemma representation_bound_map_mapset_t<K,V,W>(items:map<map<set<K>,V>,W>, keyWeight:K -> nat,
    innerValueWeight:V -> nat, valueWeight:W -> nat)
  ensures var size := Size_map(items, key => Size_map(key, child => Size_set(child, keyWeight), innerValueWeight), valueWeight);
    |items| <= size && MaxCardinality_map(items.Keys) <= size && MaxSetKeyCardinality_map_set_t(items.Keys) <= size &&
    MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight) <= size &&
    size <= RepresentationSizeBound(StructuralVolumeBound_map_mapset_t(items), MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight)) <=
      10*NatPower(size+1, 4)
{
  var exact := (key:map<set<K>,V>) => Size_map(key, child => Size_set(child, keyWeight), innerValueWeight);
  var leaf := (key:map<set<K>,V>) => MaxLeafBits_map_set_t(key, keyWeight, innerValueWeight);
  var size := Size_map(items, exact, valueWeight);
  var bits := MaxLeafBits_map_mapset_t(items, keyWeight, innerValueWeight, valueWeight);
  var width := MaxCardinality_map(items.Keys);
  var innerWidth := MaxSetKeyCardinality_map_set_t(items.Keys);
  var childVolume := StructuralVolumeBound(width, innerWidth);
  size_properties_map(items, exact, valueWeight);
  forall key | key in items
    ensures exact(key) <= RepresentationSizeBound(childVolume, bits) && valueWeight(items[key]) <= bits
    ensures leaf(key) <= exact(key)
    ensures |key| <= size && MaxCardinality_set(key.Keys) <= size
  {
    representation_bound_map_set_t(key, keyWeight, innerValueWeight);
    max_by_member(items.Keys, key, child => |child|);
    max_by_member(items.Keys, key, KeyCardinality_map_set_t);
    max_leaf_bits_member_map(items, leaf, valueWeight, key);
    structural_volume_bound_monotonic(|key|, MaxCardinality_set(key.Keys), width, innerWidth);
    representation_size_bound_monotonic(StructuralVolumeBound_map_set_t(key), leaf(key), childVolume, bits);
    size_member_map(items, exact, valueWeight, key);
  }
  representation_size_bound_map(items, exact, valueWeight, |items|, childVolume, bits, true);
  max_leaf_bits_size_map(items, leaf, valueWeight, exact, valueWeight);
  max_by_bound(items.Keys, size, key => |key|);
  max_by_bound(items.Keys, size, KeyCardinality_map_set_t);
  assert {:split_here} true;
  structural_volume_bound_polynomial(width, innerWidth, size, 1, 1);
  structural_volume_bound_polynomial(|items|, childVolume, size, 2, 2);
  representation_size_bound_polynomial(StructuralVolumeBound_map_mapset_t(items), bits, size, 3, 3);
}

