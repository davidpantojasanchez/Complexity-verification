include "../Arithmetic/PolynomialBounds.dfy"

// The bound is a proof scale. The weights alone determine representation sizes.
datatype SetContext<!E> = BitSetCost(ghost weight:E -> nat, ghost bound:nat := 0)

datatype MapContext<!K,!V> = BitMapCost(ghost keyWeight:K -> nat, ghost valueWeight:V -> nat, ghost bound:nat := 0)

// Three leaf types: atomic key, inner value and outer value. Both nested map
// shapes project the first two weights to their child map.
datatype NestedMapContext<!K,!V,!W> = BitNestedMapCost(ghost keyWeight:K -> nat, ghost innerValueWeight:V -> nat, ghost valueWeight:W -> nat, ghost bound:nat := 0)

// A compound key inherits exactly its leaf interpretation; scalar keys have
// no child context to project. Both nested-map shapes share this projection.
ghost function MapKeyContext<K,V>(context:MapContext<K,V>):SetContext<K>
{ BitSetCost(context.keyWeight, context.bound) }

ghost function NestedMapKeyContext<K,V,W>(context:NestedMapContext<K,V,W>):MapContext<K,V>
{ BitMapCost(context.keyWeight, context.innerValueWeight, context.bound) }

// Weighted tariff for traversal, equality and materialization.
ghost function {:opaque} CostRepresentation(work:nat, size:nat, operandSize:nat):(cost:nat)
  ensures work <= cost
  ensures work > 0 ==> size+operandSize < cost
{
  var width := 1+size+operandSize;
  nat_multiplication_monotonic(work, 1, width);
  nat_multiplication_monotonic(work*width, 1, width);
  if work > 0 then
    nonnegative_product_monotonic(1, 1, work, width);
    nat_multiplication_monotonic(width, 1, work*width);
    work*width*width
  else 0
}

// Common budget for a collection step, a fixed factory charge or linear arithmetic.
ghost function {:opaque} BudgetPrimitiveStep(n:nat):(budget:nat)
  ensures CostRepresentation(n+1, n, n) <= budget
  ensures CostRepresentation(1, 1, 0) <= budget
  ensures 4*n+3 <= budget
{
  var collectionBudget := CostRepresentation(n+1, n, n);
  var factoryCost := CostRepresentation(1, 1, 0);
  var maximum := if factoryCost <= collectionBudget then collectionBudget else factoryCost;
  assert 4*n+3 <= maximum by {
    if n == 0 {
      reveal CostRepresentation();
      assert collectionBudget == 1 && factoryCost == 4;
    } else {
      cost_representation_monotonic(n+1, 1, 1, n+1, n, n);
      assert CostRepresentation(n+1, 1, 1) == 9*(n+1) by { reveal CostRepresentation(); }
    }
  }
  maximum
}

lemma cost_representation_monotonic(work:nat, size:nat, operandSize:nat,
    workBound:nat, sizeBound:nat, operandBound:nat)
  requires work <= workBound && size <= sizeBound && operandSize <= operandBound
  ensures CostRepresentation(work, size, operandSize) <= CostRepresentation(workBound, sizeBound, operandBound)
{
  reveal CostRepresentation();
  nonnegative_product_monotonic(work, 1+size+operandSize, workBound, 1+sizeBound+operandBound);
  nonnegative_product_monotonic(work*(1+size+operandSize), 1+size+operandSize,
    workBound*(1+sizeBound+operandBound), 1+sizeBound+operandBound);
}

lemma collection_step_bound(work:nat, size:nat, operandSize:nat, bound:nat)
  ensures work <= bound+1 && size <= bound && operandSize <= bound
    ==> CostRepresentation(work, size, operandSize) <= BudgetPrimitiveStep(bound)
{
  if work <= bound+1 && size <= bound && operandSize <= bound {
    cost_representation_monotonic(work, size, operandSize, bound+1, bound, bound);
  }
}

lemma cost_representation_polynomial(work:nat, size:nat, operandSize:nat,
    n:nat, coefficient:nat, degree:nat)
  requires work <= coefficient*NatPower(n+1, degree)
  requires size <= n && operandSize <= n
  ensures CostRepresentation(work, size, operandSize) <=
          4*coefficient*NatPower(n+1, degree+2)
{
  reveal CostRepresentation();
  var width := 1+size+operandSize;
  polynomial_product_bound(n, width, width, 2, 2, 1, 1);
  polynomial_product_bound(n, work, width*width, coefficient, 4, degree, 2);
}

// Bound the shared primitive budget by a cubic in the same phase scale.
lemma budget_primitive_step_polynomial(n:nat)
  ensures BudgetPrimitiveStep(n) <= 4*NatPower(n+1, 3)
{
  reveal BudgetPrimitiveStep();
  cost_representation_polynomial(n+1, n, n, n, 1, 1);
  assert CostRepresentation(1, 1, 0) == 4 by { reveal CostRepresentation(); }
}

// Bound all charges with independent limits on work, receiver size and total operand size.
// Ordinary collection steps use the conditional bound exported by Cost.
lemma cost_representation_uniform_bound(workBound:nat, sizeBound:nat, operandBound:nat)
  ensures forall work:nat, size:nat, operand:nat |
    work <= workBound && size <= sizeBound && operand <= operandBound ::
      CostRepresentation(work, size, operand) <= CostRepresentation(workBound, sizeBound, operandBound)
{
  forall work:nat, size:nat, operand:nat |
    work <= workBound && size <= sizeBound && operand <= operandBound
    ensures CostRepresentation(work, size, operand) <= CostRepresentation(workBound, sizeBound, operandBound)
  { cost_representation_monotonic(work, size, operand, workBound, sizeBound, operandBound); }
}
