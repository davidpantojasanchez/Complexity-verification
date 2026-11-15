include "../Arithmetic/Arithmetic.dfy"

// The coefficient and degree are fixed before quantifying over the domain.
// A partial measured function is allowed, but must be defined throughout that domain.
ghost predicate HasPolynomialBound<X(!new)>(
    domain:X -> bool, size:X -> nat, value:X --> nat, coefficient:nat, degree:nat)
{
  coefficient > 0 &&
  forall x:X | domain(x) ::
    value.requires(x) && value(x) <= coefficient * NatPower(size(x)+1, degree)
}

ghost predicate IsPolynomial<X(!new)>(domain:X -> bool, size:X -> nat, value:X --> nat)
{
  exists coefficient:nat, degree:nat :: HasPolynomialBound(domain, size, value, coefficient, degree)
}

lemma polynomial_witness<X(!new)>(
    domain:X -> bool, size:X -> nat, value:X --> nat, coefficient:nat, degree:nat)
  requires HasPolynomialBound(domain, size, value, coefficient, degree)
  ensures IsPolynomial(domain, size, value)
{}

lemma apply_polynomial_bound<X(!new)>(
    domain:X -> bool, size:X -> nat, value:X --> nat, coefficient:nat, degree:nat, x:X)
  requires HasPolynomialBound(domain, size, value, coefficient, degree)
  requires domain(x)
  ensures value.requires(x)
  ensures value(x) <= coefficient * NatPower(size(x)+1, degree)
{}

// Every lower monomial fits the same envelope, including n=0 and degree=0.
lemma monomial_bound(n:nat, bound:nat, exponent:nat, degree:nat)
  requires n <= bound
  requires exponent <= degree
  ensures NatPower(n, exponent) <= NatPower(bound+1, degree)
  ensures 1 <= NatPower(bound+1, degree)
  decreases degree
{
  if degree > 0 {
    if exponent > 0 {
      monomial_bound(n, bound, exponent-1, degree-1);
      nonnegative_product_monotonic(n, NatPower(n, exponent-1), bound+1, NatPower(bound+1, degree-1));
    } else {
      monomial_bound(n, bound, 0, degree-1);
    }
  }
}

// Bound a complete term, keeping its coefficient explicit at the call site.
lemma weighted_monomial_bound(n:nat, bound:nat, exponent:nat, degree:nat, coefficient:nat)
  requires n <= bound
  requires exponent <= degree
  ensures coefficient * NatPower(n, exponent) <= coefficient * NatPower(bound+1, degree)
{
  monomial_bound(n, bound, exponent, degree);
  nat_multiplication_monotonic(coefficient, NatPower(n, exponent), NatPower(bound+1, degree));
}

lemma polynomial_product_bound(n:nat, x:nat, y:nat, cx:nat, cy:nat, dx:nat, dy:nat)
  requires x <= cx*NatPower(n+1, dx) && y <= cy*NatPower(n+1, dy)
  ensures x*y <= (cx*cy)*NatPower(n+1, dx+dy)
{
  var px := NatPower(n+1, dx);
  var py := NatPower(n+1, dy);
  nonnegative_product_monotonic(x, y, cx*px, cy*py);
  power_product(n+1, dx, dy);
  calc {
    (cx*px)*(cy*py);
    == { multiplication_associative(cx, px, cy*py); } cx*(px*(cy*py));
    == { multiplication_associative(px, cy, py); } cx*((px*cy)*py);
    == cx*((cy*px)*py);
    == { multiplication_associative(cy, px, py); } cx*(cy*(px*py));
    == { multiplication_associative(cx, cy, px*py); } (cx*cy)*(px*py);
    == (cx*cy)*NatPower(n+1, dx+dy);
  }
}

lemma polynomial_degree_weaken(n:nat, value:nat, coefficient:nat, degree:nat, larger:nat)
  requires value <= coefficient*NatPower(n+1, degree) && degree <= larger
  ensures value <= coefficient*NatPower(n+1, larger)
{
  power_product(n+1, degree, larger-degree);
  assert NatPower(n+1, degree) <= NatPower(n+1, larger);
  nat_multiplication_monotonic(coefficient, NatPower(n+1, degree), NatPower(n+1, larger));
}

lemma scaled_sum_bound(x:nat, y:nat, cx:nat, cy:nat, power:nat)
  requires 1 <= power && x <= cx*power && y <= cy*power
  ensures x+y+1 <= (cx+cy+1)*power
{}

lemma sum_two_scaled_bound(x:nat, y:nat, cx:nat, cy:nat, power:nat)
  requires x <= cx*power && y <= cy*power
  ensures x+y <= (cx+cy)*power
{}

lemma polynomial_base_monotonic(lower:nat, upper:nat, degree:nat)
  requires lower <= upper
  ensures NatPower(lower, degree) <= NatPower(upper, degree)
  decreases degree
{
  if degree > 0 {
    polynomial_base_monotonic(lower, upper, degree-1);
    nonnegative_product_monotonic(lower, NatPower(lower, degree-1), upper, NatPower(upper, degree-1));
  }
}

lemma polynomial_power_bound(n:nat, value:nat, coefficient:nat, degree:nat, exponent:nat)
  requires value <= coefficient*NatPower(n+1, degree)
  ensures NatPower(value, exponent) <= NatPower(coefficient, exponent)*NatPower(n+1, degree*exponent)
  decreases exponent
{
  if exponent > 0 {
    polynomial_power_bound(n, value, coefficient, degree, exponent-1);
    polynomial_product_bound(n, value, NatPower(value, exponent-1),
      coefficient, NatPower(coefficient, exponent-1), degree, degree*(exponent-1));
  }
}

// Connect a convenient phase-size envelope to the explicit input size without
// identifying either with an external encoded string.
lemma polynomial_size_substitution(inputSize:nat, phaseSize:nat, value:nat, phaseCoefficient:nat, phaseDegree:nat, valueCoefficient:nat, valueDegree:nat)
  requires phaseSize <= phaseCoefficient*NatPower(inputSize+1, phaseDegree)
  requires value <= valueCoefficient*NatPower(phaseSize+1, valueDegree)
  ensures value <= valueCoefficient*NatPower(phaseCoefficient+1, valueDegree)*NatPower(inputSize+1, phaseDegree*valueDegree)
{
  assert phaseSize+1 <= (phaseCoefficient+1)*NatPower(inputSize+1, phaseDegree);
  polynomial_power_bound(inputSize, phaseSize+1, phaseCoefficient+1, phaseDegree, valueDegree);
  nat_multiplication_monotonic(valueCoefficient, NatPower(phaseSize+1, valueDegree),
    NatPower(phaseCoefficient+1, valueDegree)*NatPower(inputSize+1, phaseDegree*valueDegree));
  multiplication_associative(valueCoefficient, NatPower(phaseCoefficient+1, valueDegree), NatPower(inputSize+1, phaseDegree*valueDegree));
}

// Compose scalar budgets of different degrees without expanding their formulas.
lemma polynomial_sum_bound(n:nat, x:nat, y:nat, cx:nat, cy:nat,
    dx:nat, dy:nat, degree:nat)
  requires x <= cx*NatPower(n+1, dx) && y <= cy*NatPower(n+1, dy)
  requires dx <= degree && dy <= degree
  ensures x+y <= (cx+cy)*NatPower(n+1, degree)
{
  polynomial_degree_weaken(n, x, cx, dx, degree);
  polynomial_degree_weaken(n, y, cy, dy, degree);
  sum_two_scaled_bound(x, y, cx, cy, NatPower(n+1, degree));
}
