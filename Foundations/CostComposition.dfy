include "PolynomialBounds.dfy"

// Historical two-component composition for pilot clients. The coefficient is
// retained as a fixed algebraic normalization, not a cap on production source.
ghost function LegacyControlCostFactor():nat { 2*64*2048 }

ghost function TotalCostCoefficient(structural:nat, arithmetic:nat, size:nat):nat
{ (1+size)*(1+size)*(structural+LegacyControlCostFactor()*(structural+arithmetic+1))+arithmetic }

// Collection realization is the explicit hypothesis K_col*(1+size)^2.
// This composition does not assert native backend running time. Control is a
// separately justified fixed coefficient, not an arbitrary per-input factor.
// The size factor also covers routing/reference work between primitive calls;
// no constant-bit-cost assumption for handling arbitrary data is needed.
ghost function CostTotal(structural:nat, arithmetic:nat, operandSize:nat, control:nat):nat
{ (1+operandSize)*(1+operandSize)*(structural + control*(structural+arithmetic+1)) + arithmetic }

lemma cost_total_monotonic(structural:nat, arithmetic:nat, size:nat,
    structuralBound:nat, arithmeticBound:nat, sizeBound:nat, control:nat)
  requires structural <= structuralBound && arithmetic <= arithmeticBound && size <= sizeBound
  ensures CostTotal(structural, arithmetic, size, control) <=
    CostTotal(structuralBound, arithmeticBound, sizeBound, control)
{
  nonnegative_product_monotonic(1+size, 1+size, 1+sizeBound, 1+sizeBound);
  nat_multiplication_monotonic(control, structural+arithmetic+1, structuralBound+arithmeticBound+1);
  nonnegative_product_monotonic((1+size)*(1+size), structural+control*(structural+arithmetic+1),
    (1+sizeBound)*(1+sizeBound), structuralBound+control*(structuralBound+arithmeticBound+1));
}

lemma control_scaled_bound(structural:nat, arithmetic:nat, cs:nat, ca:nat, power:nat, control:nat)
  requires 1 <= power && structural <= cs*power && arithmetic <= ca*power
  ensures structural+control*(structural+arithmetic+1) <= (cs+control*(cs+ca+1))*power
{
  scaled_sum_bound(structural, arithmetic, cs, ca, power);
  nat_multiplication_monotonic(control, structural+arithmetic+1, (cs+ca+1)*power);
  multiplication_associative(control, cs+ca+1, power);
}

// Fixed coefficients and degrees compose without expanding algorithm polynomials.
lemma {:isolate_assertions} cost_total_polynomial_bound(n:nat, structural:nat, arithmetic:nat, size:nat,
    cs:nat, ds:nat, ca:nat, da:nat, cv:nat, dv:nat, control:nat)
  requires structural <= cs*NatPower(n+1, ds)
  requires arithmetic <= ca*NatPower(n+1, da)
  requires size <= cv*NatPower(n+1, dv)
  ensures CostTotal(structural, arithmetic, size, control) <=
    ((1+cv)*(1+cv)*(cs+control*(cs+ca+1)) + ca)*NatPower(n+1, 2*dv+ds+da)
{
  var degree := 2*dv+ds+da;
  var innerDegree := ds+da;
  assert 1+size <= (1+cv)*NatPower(n+1, dv);
  polynomial_product_bound(n, 1+size, 1+size, 1+cv, 1+cv, dv, dv);
  polynomial_degree_weaken(n, arithmetic, ca, da, innerDegree);
  polynomial_degree_weaken(n, structural, cs, ds, innerDegree);
  control_scaled_bound(structural, arithmetic, cs, ca, NatPower(n+1, innerDegree), control);
  polynomial_product_bound(n, (1+size)*(1+size), structural+control*(structural+arithmetic+1),
    (1+cv)*(1+cv), cs+control*(cs+ca+1), 2*dv, innerDegree);
  polynomial_degree_weaken(n, arithmetic, ca, da, degree);
  sum_two_scaled_bound((1+size)*(1+size)*(structural+control*(structural+arithmetic+1)), arithmetic,
    (1+cv)*(1+cv)*(cs+control*(cs+ca+1)), ca, NatPower(n+1, degree));
}
