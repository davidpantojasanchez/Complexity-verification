include "Arithmetic.dfy"

// Binary lengths and their laws for natural, signed integer and Boolean values.

// Binary magnitude length, with one digit for zero. This is a ghost measure;
// computing it is not an extra executable operation in costed arithmetic.
ghost function {:opaque} NatBits(value:nat):(bits:nat)
  ensures 1 <= bits
  decreases value
{
  if value < 2 then 1 else 1 + NatBits(value / 2)
}

// Signed values add one sign bit to the binary magnitude length.
ghost function IntBits(value:int):nat
{ 1 + NatBits(if value < 0 then -value else value) }

ghost function BoolBits(value:bool):nat { 1 }

// Order and a loose linear envelope support numeric loop and cost bounds.
lemma nat_bits_monotonic(lower:nat, upper:nat)
  requires lower <= upper
  ensures NatBits(lower) <= NatBits(upper)
  decreases upper
{
  reveal NatBits();
  if 2 <= lower {
    nat_bits_monotonic(lower / 2, upper / 2);
  }
}

lemma nat_bits_linear_bound(value:nat)
  ensures NatBits(value) <= value + 1
  decreases value
{
  reveal NatBits();
  if 2 <= value {
    nat_bits_linear_bound(value / 2);
  }
}

// Relate binary length to a strict power-of-two upper bound in both directions.
lemma nat_bits_range(value:nat)
  ensures value < NatPower(2, NatBits(value))
  decreases value
{
  reveal NatBits();
  if 2 <= value {
    nat_bits_range(value / 2);
    assert value == 2 * (value / 2) + value % 2;
  }
}

lemma nat_bits_from_power(value:nat, bits:nat)
  requires 0 < bits
  requires value < NatPower(2, bits)
  ensures NatBits(value) <= bits
  decreases bits
{
  reveal NatBits();
  if 2 <= value {
    assert 1 < bits;
    assert NatPower(2, bits) == 2 * NatPower(2, bits - 1);
    nat_bits_from_power(value / 2, bits - 1);
  }
}

lemma power_two_add(left:nat, right:nat)
  ensures NatPower(2, left + right) == NatPower(2, left) * NatPower(2, right)
  decreases left
{
  if left != 0 {
    power_two_add(left - 1, right);
  }
}

// Addition can grow by one digit; multiplication adds operand lengths.
lemma nat_bits_add(left:nat, right:nat)
  ensures NatBits(left + right) <=
    1 + (if NatBits(left) < NatBits(right)
         then NatBits(right) else NatBits(left))
{
  var maximum := if left < right then right else left;
  nat_bits_monotonic(left, maximum);
  nat_bits_monotonic(right, maximum);
  nat_bits_monotonic(left + right, 2 * maximum);
  if maximum != 0 {
    reveal NatBits();
    assert NatBits(2 * maximum) == 1 + NatBits(maximum);
  } else {
    reveal NatBits();
  }
}

lemma {:isolate_assertions} nat_bits_multiply(left:nat, right:nat)
  ensures NatBits(left * right) <= NatBits(left) + NatBits(right)
{
  nat_bits_range(left);
  nat_bits_range(right);
  power_two_add(NatBits(left), NatBits(right));
  var leftPower := NatPower(2, NatBits(left));
  var rightPower := NatPower(2, NatBits(right));
  nonnegative_product_monotonic(left, right, leftPower - 1, rightPower - 1);
  assert (leftPower - 1) * (rightPower - 1) < leftPower * rightPower;
  nat_bits_from_power(left * right, NatBits(left) + NatBits(right));
}

// A polynomially bounded compact arena needs only linearly many address bits
// in its phase size. The space bound is a separate realization obligation.
lemma nat_bits_power_bound(base:nat, exponent:nat)
  ensures NatBits(NatPower(base, exponent)) <= 1+exponent*NatBits(base)
  decreases exponent
{
  if exponent == 0 {
    assert NatPower(base, exponent) == 1;
    assert NatBits(1) == 1 by { reveal NatBits(); }
  } else {
    nat_bits_power_bound(base, exponent-1);
    nat_bits_multiply(base, NatPower(base, exponent-1));
  }
}

lemma polynomial_address_bits_bound(address:nat, size:nat, coefficient:nat, degree:nat)
  requires address <= coefficient*NatPower(size+1, degree)
  ensures NatBits(address) <= 1+NatBits(coefficient)+degree*(size+2)
{
  nat_bits_monotonic(address, coefficient*NatPower(size+1, degree));
  nat_bits_multiply(coefficient, NatPower(size+1, degree));
  nat_bits_power_bound(size+1, degree);
  nat_bits_linear_bound(size+1);
  nat_multiplication_monotonic(degree, NatBits(size+1), size+2);
}
