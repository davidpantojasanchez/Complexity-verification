include "ArithmeticLemmas.dfy"

// Representation of the budget that is helpful for loops.
ghost function {:opaque} LinearLoopBudget(
    base:nat, step:nat, processed:nat):nat
{
  base + processed * step
}

// Initialize the budget before the first iteration.
lemma linear_loop_budget_zero(base:nat, step:nat)
  ensures LinearLoopBudget(base, step, 0) == base
{
  reveal LinearLoopBudget();
}

// Expose exactly one iteration of an otherwise opaque budget.
lemma linear_loop_budget_step(base:nat, step:nat, processed:nat)
  ensures LinearLoopBudget(base, step, processed + 1) ==
          LinearLoopBudget(base, step, processed) + step
{ reveal LinearLoopBudget(); }

// Bound an accumulated budget by a maximum iteration count.
lemma linear_loop_budget_bound(base:nat, step:nat, processed:nat, bound:nat)
  requires processed <= bound
  ensures LinearLoopBudget(base, step, processed) <=
          base + bound * step
{
  reveal LinearLoopBudget();
  nonnegative_product_monotonic(processed, step, bound, step);
}

// Transfer an upper budget, including tail costs, to the observed counter.
lemma linear_loop_budget_transfer(spent:nat, budget:nat, upper:nat, tail:nat, total:nat)
  requires spent <= budget <= upper
  requires upper + tail <= total
  ensures budget + tail <= total
  ensures spent + tail <= total
{}

