include "CollectionSizes.dfy"

// One structural layer; a flat collection has childVolume zero. Each dimension
// is independently bounded, so children need not attain their maxima together.
ghost function StructuralVolume(count:nat, childVolume:nat):nat
{ count*(1+childVolume) }

// Representation-size envelope derived from structural volume and leaf bits.
ghost function StructuralSize(volume:nat, bits:nat):(size:nat)
  requires 1 <= bits
  ensures 1 <= size
{ 1+3*volume*bits }

lemma structural_volume_monotonic(count:nat, child:nat, countBound:nat, childBound:nat)
  requires count <= countBound && child <= childBound
  ensures StructuralVolume(count, child) <= StructuralVolume(countBound, childBound)
{
  nonnegative_product_monotonic(count, 1+child, countBound, 1+childBound);
}

lemma structural_size_monotonic(volume:nat, bits:nat, volumeBound:nat, bitsBound:nat)
  requires volume <= volumeBound && 1 <= bits <= bitsBound
  ensures StructuralSize(volume, bits) <= StructuralSize(volumeBound, bitsBound)
{
  nonnegative_product_monotonic(volume, bits, volumeBound, bitsBound);
  calc {
    StructuralSize(volume, bits);
    == 1+3*(volume*bits);
    <= 1+3*(volumeBound*bitsBound);
    == StructuralSize(volumeBound, bitsBound);
  }
}

// Flat keys/elements cost at most B; a nested child includes its own header.
// The other field of a map entry is a leaf. Both cases fit the same factor 3.
lemma structural_size_layer(count:nat, child:nat, bits:nat, nested:bool)
  requires 1 <= bits
  requires !nested ==> child == 0
  ensures 1+count*(1+(if nested then StructuralSize(child, bits) else bits)+bits) <=
    StructuralSize(StructuralVolume(count, child), bits)
{
  var key := if nested then StructuralSize(child, bits) else bits;
  assert 1+key+bits <= 3*(1+child)*bits;
  nonnegative_product_monotonic(count, 1+key+bits, count, 3*(1+child)*bits);
  assert count*(3*(1+child)*bits) == 3*StructuralVolume(count, child)*bits;
}

// These two native proofs compose over all seven supported collection shapes.
// A child is weighted by its exact reference size; clients will receive the
// resulting envelope from trait contracts, not invoke these lemmas per operation.
lemma structural_size_set<E>(items:set<E>, weight:E -> nat,
    count:nat, child:nat, bits:nat, nested:bool)
  requires |items| <= count && 1 <= bits
  requires !nested ==> child == 0
  requires forall item | item in items ::
    weight(item) <= (if nested then StructuralSize(child, bits) else bits)
  ensures Size_set(items, weight) <= StructuralSize(StructuralVolume(count, child), bits)
{
  var maximum := if nested then StructuralSize(child, bits) else bits;
  size_bound_set(items, weight, maximum);
  nonnegative_product_monotonic(|items|, 1+maximum, count, 1+maximum+bits);
  structural_size_layer(count, child, bits, nested);
}

lemma structural_size_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat,
    count:nat, child:nat, bits:nat, nested:bool)
  requires |items| <= count && 1 <= bits
  requires !nested ==> child == 0
  requires forall key | key in items ::
    keyWeight(key) <= (if nested then StructuralSize(child, bits) else bits) &&
    valueWeight(items[key]) <= bits
  ensures Size_map(items, keyWeight, valueWeight) <= StructuralSize(StructuralVolume(count, child), bits)
{
  var maximum := if nested then StructuralSize(child, bits) else bits;
  size_bound_map(items, keyWeight, valueWeight, maximum, bits);
  nonnegative_product_monotonic(|items|, 1+maximum+bits, count, 1+maximum+bits);
  structural_size_layer(count, child, bits, nested);
}

// Polynomial composition, independently of a collection representation.
// A caller must still derive the dimension and leaf bounds from its input.
lemma structural_volume_polynomial(count:nat, child:nat, n:nat, coefficient:nat, degree:nat)
  requires count <= n && child <= coefficient*NatPower(n+1, degree)
  ensures StructuralVolume(count, child) <= (coefficient+1)*NatPower(n+1, degree+1)
{
  assert 1 <= NatPower(n+1, degree);
  polynomial_product_bound(n, count, 1+child, 1, coefficient+1, 1, degree);
}

lemma structural_size_polynomial(volume:nat, bits:nat, n:nat, coefficient:nat, degree:nat)
  requires volume <= coefficient*NatPower(n+1, degree)
  requires 1 <= bits <= n+1
  ensures StructuralSize(volume, bits) <= (1+3*coefficient)*NatPower(n+1, degree+1)
{
  polynomial_product_bound(n, volume, bits, coefficient, 1, degree, 1);
  assert 1 <= NatPower(n+1, degree+1);
  calc {
    StructuralSize(volume, bits);
    == 1+3*(volume*bits);
    <= 1+3*(coefficient*NatPower(n+1, degree+1));
    <= NatPower(n+1, degree+1)+3*(coefficient*NatPower(n+1, degree+1));
    == (1+3*coefficient)*NatPower(n+1, degree+1);
  }
}
