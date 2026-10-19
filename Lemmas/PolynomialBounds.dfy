include "ArithmeticLemmas.dfy"

// The coefficient and degree are fixed before quantifying over the domain.
// A partial cost is allowed, but must be defined throughout that domain.
ghost predicate HasPolynomialBound<X(!new)>(
    domain:X -> bool, size:X -> nat, cost:X --> nat, coefficient:nat, degree:nat)
{
  coefficient > 0 &&
  forall x:X | domain(x) ::
    cost.requires(x) && cost(x) <= coefficient * NatPower(size(x)+1, degree)
}

ghost predicate IsPolynomial<X(!new)>(domain:X -> bool, size:X -> nat, cost:X --> nat)
{
  exists coefficient:nat, degree:nat :: HasPolynomialBound(domain, size, cost, coefficient, degree)
}

lemma polynomial_witness<X(!new)>(
    domain:X -> bool, size:X -> nat, cost:X --> nat, coefficient:nat, degree:nat)
  requires HasPolynomialBound(domain, size, cost, coefficient, degree)
  ensures IsPolynomial(domain, size, cost)
{}

lemma apply_polynomial_bound<X(!new)>(
    domain:X -> bool, size:X -> nat, cost:X --> nat, coefficient:nat, degree:nat, x:X)
  requires HasPolynomialBound(domain, size, cost, coefficient, degree)
  requires domain(x)
  ensures cost.requires(x)
  ensures cost(x) <= coefficient * NatPower(size(x)+1, degree)
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
