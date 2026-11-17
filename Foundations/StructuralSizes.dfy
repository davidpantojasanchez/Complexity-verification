include "../Arithmetic/Arithmetic.dfy"

// One structural layer; a flat collection has childVolume zero. Each dimension
// is independently bounded, so children need not attain their maxima together.
ghost function StructuralVolumeBound(count:nat, childVolume:nat):nat
{ count*(1+childVolume) }

// Representation-size envelope derived from structural volume and leaf bits.
ghost function RepresentationSizeBound(volume:nat, bits:nat):(size:nat)
  requires 1 <= bits
  ensures 1 <= size
{ 1+3*volume*bits }

lemma structural_volume_bound_monotonic(count:nat, child:nat, countBound:nat, childBound:nat)
  requires count <= countBound && child <= childBound
  ensures StructuralVolumeBound(count, child) <= StructuralVolumeBound(countBound, childBound)
{
  nonnegative_product_monotonic(count, 1+child, countBound, 1+childBound);
}

lemma representation_size_bound_monotonic(volume:nat, bits:nat, volumeBound:nat, bitsBound:nat)
  requires volume <= volumeBound && 1 <= bits <= bitsBound
  ensures RepresentationSizeBound(volume, bits) <= RepresentationSizeBound(volumeBound, bitsBound)
{
  nonnegative_product_monotonic(volume, bits, volumeBound, bitsBound);
  calc {
    RepresentationSizeBound(volume, bits);
    == 1+3*(volume*bits);
    <= 1+3*(volumeBound*bitsBound);
    == RepresentationSizeBound(volumeBound, bitsBound);
  }
}

// Flat keys/elements cost at most B; a nested child includes its own header.
// The other field of a map entry is a leaf. Both cases fit the same factor 3.
lemma representation_size_bound_layer(count:nat, child:nat, bits:nat, nested:bool)
  requires 1 <= bits
  requires !nested ==> child == 0
  ensures 1+count*(1+(if nested then RepresentationSizeBound(child, bits) else bits)+bits) <=
    RepresentationSizeBound(StructuralVolumeBound(count, child), bits)
{
  var key := if nested then RepresentationSizeBound(child, bits) else bits;
  assert 1+key+bits <= 3*(1+child)*bits;
  nonnegative_product_monotonic(count, 1+key+bits, count, 3*(1+child)*bits);
  assert count*(3*(1+child)*bits) == 3*StructuralVolumeBound(count, child)*bits;
}
