include "CollectionSizes.dfy"

// One fixed-depth layer. childBound covers each leaf or complete child,
// including values stored beside nested keys. Compose once per structural
// dimension; do not iterate over the depth of an arbitrary tree.
ghost function CollectionSizeBound(count:nat, childBound:nat):(bound:nat)
  requires 1 <= childBound
  ensures childBound <= bound
{ 3*(count+1)*childBound }

lemma collection_size_tight_bound(count:nat, childBound:nat)
  requires 1 <= childBound
  ensures 1+count*(1+childBound) <= 1+count*(1+2*childBound) <= CollectionSizeBound(count, childBound)
{
  nonnegative_product_monotonic(count, 1+childBound, count, 1+2*childBound);
  nonnegative_product_monotonic(count, 1+2*childBound, count, 3*childBound);
  calc {
    1+count*(1+2*childBound);
    <= 1+count*(3*childBound);
    <= 3*childBound+count*(3*childBound);
    == 3*(count+1)*childBound;
    == CollectionSizeBound(count, childBound);
  }
}

// The same envelope covers sets and maps; tight bounds remain available from
// size_bound_set/size_bound_map when a client needs greater precision.
lemma size_envelope_set<E>(items:set<E>, weight:E -> nat, count:nat, childBound:nat)
  requires |items| <= count && 1 <= childBound
  requires forall item | item in items :: weight(item) <= childBound
  ensures Size_set(items, weight) <= CollectionSizeBound(count, childBound)
{
  size_bound_set(items, weight, childBound);
  nonnegative_product_monotonic(|items|, 1+childBound, count, 1+childBound);
  collection_size_tight_bound(count, childBound);
}

lemma size_envelope_map<K,V>(items:map<K,V>, keyWeight:K -> nat, valueWeight:V -> nat,
    count:nat, childBound:nat)
  requires |items| <= count && 1 <= childBound
  requires forall key | key in items :: keyWeight(key) <= childBound && valueWeight(items[key]) <= childBound
  ensures Size_map(items, keyWeight, valueWeight) <= CollectionSizeBound(count, childBound)
{
  size_bound_map(items, keyWeight, valueWeight, childBound, childBound);
  nonnegative_product_monotonic(|items|, 1+2*childBound, count, 1+2*childBound);
  collection_size_tight_bound(count, childBound);
}

lemma collection_size_bound_monotonic(count:nat, childBound:nat, countBound:nat, largerChild:nat)
  requires count <= countBound && 1 <= childBound <= largerChild
  ensures CollectionSizeBound(count, childBound) <= CollectionSizeBound(countBound, largerChild)
{
  nonnegative_product_monotonic(count+1, childBound, countBound+1, largerChild);
}

// Each fixed structural layer adds one degree. The caller must derive count
// and child bounds from the input; arbitrary ghost allowances prove no claim
// about complexity in input size.
lemma collection_size_bound_polynomial(count:nat, childBound:nat, n:nat, coefficient:nat, degree:nat)
  requires count <= n && 1 <= childBound
  requires childBound <= coefficient*NatPower(n+1, degree)
  ensures CollectionSizeBound(count, childBound) <= 3*coefficient*NatPower(n+1, degree+1)
{
  polynomial_product_bound(n, count+1, childBound, 1, coefficient, 1, degree);
}
