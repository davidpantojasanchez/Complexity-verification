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

// Native-value arithmetic with explicit length-sensitive accounting. These
// budgets model elementary binary algorithms; the native operators below are
// not yet a verified implementation of those algorithms or a runtime bound.
// The counters and length measurements are ghost.

method AddNat(left:nat, right:nat, ghost counter_in:nat)
    returns (result:nat, ghost counter:nat)
  ensures result == left + right
  ensures NatBits(result) <=
    1 + (if NatBits(left) < NatBits(right)
         then NatBits(right) else NatBits(left))
  ensures counter == counter_in + CostAddNat(left, right)
{
  result := left + right;
  counter := counter_in + CostAddNat(left, right);
  nat_bits_add(left, right);
}

method MultiplyNat(left:nat, right:nat, ghost counter_in:nat)
    returns (result:nat, ghost counter:nat)
  ensures result == left * right
  ensures NatBits(result) <= NatBits(left) + NatBits(right)
  ensures counter == counter_in + CostMultiplyNat(left, right)
{
  result := left * right;
  counter := counter_in + CostMultiplyNat(left, right);
  nat_bits_multiply(left, right);
}

method SubtractNat(left:nat, right:nat, ghost counter_in:nat)
    returns (result:nat, ghost counter:nat)
  requires right <= left
  ensures result == left - right
  ensures NatBits(result) <= NatBits(left)
  ensures counter == counter_in + CostSubtractNat(left, right)
{
  result := left - right;
  counter := counter_in + CostSubtractNat(left, right);
  nat_bits_monotonic(result, left);
}

method LessEqualNat(left:nat, right:nat, ghost counter_in:nat)
    returns (result:bool, ghost counter:nat)
  ensures result == (left <= right)
  ensures counter == counter_in + CostLessEqualNat(left, right)
{
  result := left <= right;
  counter := counter_in + CostLessEqualNat(left, right);
}

// Compare value with total * threshold in both inclusive directions, using
// integer cross-products; equality makes both results true.
method CompareNatToRational(
    value:nat, total:nat, threshold:Rational, ghost counter_in:nat)
    returns (atMost:bool, atLeast:bool, ghost counter:nat)
  ensures atMost == (threshold.denominator * value <= threshold.numerator * total)
  ensures atLeast == (threshold.numerator * total <= threshold.denominator * value)
  ensures atMost == ((value as real) <= threshold.Model() * (total as real))
  ensures atLeast == (threshold.Model() * (total as real) <= (value as real))
  ensures counter == counter_in + CostCompareNatToRational(value, total, threshold)
{
  var left:nat;
  var right:nat;
  left, counter := MultiplyNat(threshold.denominator, value, counter_in);
  right, counter := MultiplyNat(threshold.numerator, total, counter);
  atMost, counter := LessEqualNat(left, right, counter);
  atLeast, counter := LessEqualNat(right, left, counter);
  cost_nat_arithmetic_commutative(left, right);
  nat_rational_comparison(value, total, threshold.numerator, threshold.denominator);
}

// Complexity bounds

ghost function {:opaque} CostAddNat(left:nat, right:nat):(cost:nat)
  ensures cost == 1 + NatBits(left) + NatBits(right)
{ 1 + NatBits(left) + NatBits(right) }

ghost function {:opaque} CostMultiplyNat(left:nat, right:nat):(cost:nat)
  ensures cost == 1 + NatBits(left) * NatBits(right)
{ 1 + NatBits(left) * NatBits(right) }

ghost function {:opaque} CostSubtractNat(left:nat, right:nat):(cost:nat)
  ensures cost == 1 + NatBits(left) + NatBits(right)
{ 1 + NatBits(left) + NatBits(right) }

ghost function {:opaque} CostLessEqualNat(left:nat, right:nat):(cost:nat)
  ensures cost == 1 + NatBits(left) + NatBits(right)
{ 1 + NatBits(left) + NatBits(right) }

ghost function CostCompareNatToRational(value:nat, total:nat, threshold:Rational):nat
{
  CostMultiplyNat(threshold.denominator, value) +
  CostMultiplyNat(threshold.numerator, total) +
  2 * CostLessEqualNat(threshold.denominator * value, threshold.numerator * total)
}

// A shared envelope when all numeric operands have a common value bound.
// Its dependence on that bound is through binary length only.

ghost function {:opaque} BudgetNatArithmetic(maximum:nat):(budget:nat)
  ensures budget == 1+2*NatBits(maximum)+NatBits(maximum)*NatBits(maximum)
{ 1 + 2*NatBits(maximum) + NatBits(maximum)*NatBits(maximum) }

// Independent length bounds for populations and the stored threshold fields.
lemma {:induction false} {:isolate_assertions} cost_compare_nat_to_rational_bound(
    value:nat, total:nat, threshold:Rational, populationBits:nat, thresholdBits:nat)
  requires NatBits(value) <= populationBits && NatBits(total) <= populationBits
  requires NatBits(threshold.numerator) <= thresholdBits
  requires NatBits(threshold.denominator) <= thresholdBits
  ensures CostCompareNatToRational(value, total, threshold) <=
    4 + 2 * populationBits * thresholdBits + 4 * (populationBits + thresholdBits)
{
  reveal CostAddNat(), CostSubtractNat(), CostLessEqualNat(), CostMultiplyNat();
  nat_bits_multiply(threshold.denominator, value);
  nat_bits_multiply(threshold.numerator, total);
  nonnegative_product_monotonic(
    NatBits(threshold.denominator), NatBits(value), thresholdBits, populationBits);
  nonnegative_product_monotonic(
    NatBits(threshold.numerator), NatBits(total), thresholdBits, populationBits);
  assert CostMultiplyNat(threshold.denominator, value) <= 1 + populationBits * thresholdBits;
  assert CostMultiplyNat(threshold.numerator, total) <= 1 + populationBits * thresholdBits;
  assert CostLessEqualNat(threshold.denominator * value, threshold.numerator * total) <=
    1 + 2 * (populationBits + thresholdBits);
  calc {
    CostCompareNatToRational(value, total, threshold);
    == CostMultiplyNat(threshold.denominator, value) +
       CostMultiplyNat(threshold.numerator, total) +
       2 * CostLessEqualNat(threshold.denominator * value, threshold.numerator * total);
    <= (1 + populationBits * thresholdBits) + (1 + populationBits * thresholdBits) +
       2 * (1 + 2 * (populationBits + thresholdBits));
    == 4 + 2 * populationBits * thresholdBits + 4 * (populationBits + thresholdBits);
  }
}

lemma nat_arithmetic_within_budget(left:nat, right:nat, maximum:nat)
  requires left <= maximum && right <= maximum
  ensures CostAddNat(left, right) <= BudgetNatArithmetic(maximum)
  ensures CostSubtractNat(left, right) <= BudgetNatArithmetic(maximum)
  ensures CostMultiplyNat(left, right) <= BudgetNatArithmetic(maximum)
  ensures CostLessEqualNat(left, right) <= BudgetNatArithmetic(maximum)
{
  reveal BudgetNatArithmetic();
  reveal CostAddNat(), CostSubtractNat(), CostLessEqualNat(), CostMultiplyNat();
  nat_bits_monotonic(left, maximum);
  nat_bits_monotonic(right, maximum);
  nonnegative_product_monotonic(NatBits(left), NatBits(right),
    NatBits(maximum), NatBits(maximum));

  assert CostAddNat(left, right) <= BudgetNatArithmetic(maximum);

  assert CostSubtractNat(left, right) <= BudgetNatArithmetic(maximum);

  assert CostMultiplyNat(left, right) <= BudgetNatArithmetic(maximum);

  assert CostLessEqualNat(left, right) <= BudgetNatArithmetic(maximum);
}

lemma cost_less_equal_nat_monotonic(left:nat, right:nat, leftBound:nat, rightBound:nat)
  requires NatBits(left) <= NatBits(leftBound) && NatBits(right) <= NatBits(rightBound)
  ensures CostLessEqualNat(left, right) <= CostLessEqualNat(leftBound, rightBound)
{
  reveal CostLessEqualNat();
}

lemma budget_nat_arithmetic_bits_bound(maximum:nat, bits:nat)
  requires NatBits(maximum) <= bits
  ensures BudgetNatArithmetic(maximum) <= 1+2*bits+bits*bits
{
  reveal BudgetNatArithmetic();
  nonnegative_product_monotonic(NatBits(maximum), NatBits(maximum), bits, bits);
}

lemma cost_nat_arithmetic_commutative(left:nat, right:nat)
  ensures CostAddNat(left, right) == CostAddNat(right, left)
  ensures CostSubtractNat(left, right) == CostSubtractNat(right, left)
  ensures CostLessEqualNat(left, right) == CostLessEqualNat(right, left)
  ensures CostMultiplyNat(left, right) == CostMultiplyNat(right, left)
{
  reveal CostAddNat(), CostSubtractNat(), CostLessEqualNat(), CostMultiplyNat();
}
