
// Scalar arithmetic: powers, integer products and exact rational comparisons.

ghost function NatPower(base:nat, exponent:nat):nat
  ensures 0 < base ==> 0 < NatPower(base, exponent)
  decreases exponent
{ if exponent == 0 then 1 else base * NatPower(base, exponent-1) }

lemma nat_multiplication_monotonic(factor:nat, lower:nat, upper:nat)
  requires lower <= upper
  ensures factor*lower <= factor*upper
{}

lemma nonnegative_product_monotonic(a:int, b:int, a':int, b':int)
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{}

lemma positive_nat_product_strict(factor:nat, left:nat, right:nat)
  requires 0 < factor && left < right
  ensures factor*left < factor*right
{}

lemma multiplication_associative(a:int, b:int, c:int)
  ensures (a*b)*c == a*(b*c)
{}

lemma multiplication_distributive(a:int, b:int, c:int)
  ensures a*(b+c) == a*b+a*c
{}

lemma product_bound_implies_quotient_bound(factor:nat, value:nat, bound:nat)
  requires 0 < factor
  requires factor*value <= bound
  ensures value <= bound/factor
{
  if bound/factor < value {
    assert bound/factor + 1 <= value;
    nat_multiplication_monotonic(factor, bound/factor + 1, value);
    assert factor*(bound/factor + 1) == factor*(bound/factor) + factor;
    assert bound == factor*(bound/factor) + bound%factor;
    assert bound%factor < factor;
  }
}

lemma power_product(base:nat, left:nat, right:nat)
  ensures NatPower(base, left)*NatPower(base, right) == NatPower(base, left+right)
  decreases left
{
  if left > 0 {
    power_product(base, left-1, right);
    multiplication_associative(base, NatPower(base, left-1), NatPower(base, right));
  }
}

lemma positive_real_scale_order(factor:real, left:real, right:real)
  requires 0.0 < factor
  ensures (left <= right) == (factor * left <= factor * right)
{}

// Positive denominators preserve both inclusive comparisons, also for total=0.
lemma nat_rational_comparison(value:nat, total:nat, numerator:nat, denominator:nat)
  requires 0 < denominator
  ensures ((value as real) <= (numerator as real) / (denominator as real) * (total as real)) ==
    (denominator * value <= numerator * total)
  ensures ((numerator as real) / (denominator as real) * (total as real) <= (value as real)) ==
    (numerator * total <= denominator * value)
{
  var threshold := (numerator as real) / (denominator as real);
  assert threshold * (denominator as real) == numerator as real;
  assert (denominator as real) * (threshold * (total as real)) ==
    (numerator * total) as real;
  assert (denominator as real) * (value as real) == (denominator * value) as real;
  positive_real_scale_order(denominator as real, value as real, threshold * (total as real));
  positive_real_scale_order(denominator as real, threshold * (total as real), value as real);
}
