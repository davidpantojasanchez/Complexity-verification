
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
