ghost function NatPower(base:nat, exponent:nat):nat
  decreases exponent
{ if exponent == 0 then 1 else base * NatPower(base, exponent-1) }


lemma nat_multiplication_monotonic(factor:nat, lower:nat, upper:nat)
  requires lower <= upper
  ensures factor*lower <= factor*upper
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

lemma nonnegative_product_monotonic(a:int, b:int, a':int, b':int)
  requires 0 <= a <= a'
  requires 0 <= b <= b'
  ensures a*b <= a'*b'
{}

lemma multiplication_associative(a:int, b:int, c:int)
  ensures (a*b)*c == a*(b*c)
{}
