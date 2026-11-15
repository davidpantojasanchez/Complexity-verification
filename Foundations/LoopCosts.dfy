include "../Arithmetic/Arithmetic.dfy"

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

// Bound the iteration count and transfer the accumulated budget, including tail work.
// Used only when linear_loop_budget_bound is insufficient.
// base: budget before the first iteration.
// step: budget per iteration.
// processed: iterations performed.
// bound: upper bound on that iteration count.
// spent: observed accumulated cost, including the initial cost covered by base.
// tail: budget for subsequent work (zero if absent).
// total: target bound on spent + tail.
lemma linear_loop_budget_transfer(base:nat, step:nat, processed:nat, bound:nat, spent:nat, tail:nat, total:nat)
  requires processed <= bound
  requires spent <= LinearLoopBudget(base, step, processed)
  requires base + bound * step + tail <= total
  ensures LinearLoopBudget(base, step, processed) + tail <= total
  ensures spent + tail <= total
{
  linear_loop_budget_bound(base, step, processed, bound);
}
