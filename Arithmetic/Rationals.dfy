include "BitLengths.dfy"

type PositiveDenominator = value:nat | 0 < value witness 1

// Nonnegative rational
datatype Rational = Rational(numerator:nat, denominator:PositiveDenominator)
{
  // Exact mathematical value used for verification
  ghost function Model():real
  { (numerator as real) / (denominator as real) }
}

// Length of the stored pair, including non-reduced representations.
ghost function RationalBits(threshold:Rational):nat
{ NatBits(threshold.numerator) + NatBits(threshold.denominator) }

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
