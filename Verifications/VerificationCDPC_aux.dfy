include "../Polynomial/PolynomialCDPC.dfy"
include "../Problems/CDPCRepresentation.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"
include "../Problems/CDPCLemmas.dfy"
include "../Collections/Set.dfy"
include "../Collections/Map.dfy"
include "../Arithmetic/CostedArithmetic.dfy"

// Methods

// Classification and privacy checks

method CheckClassification<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    fitnessLower:Rational,
    fitnessUpper:Rational,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Representation in
  requires candidates.Keys() != {}
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  // State in
  requires fitness.SizeBound(weight, BoolBits, BoolBits) <= n
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() :: multiplicity.Model()[candidate] <= maximum
  requires RationalBits(fitnessLower) <= n && RationalBits(fitnessUpper) <= n
  // State out
  ensures accepted == ClassificationDecided(
    candidates.Keys(), fitness.Model(), multiplicity.Model(),
    fitnessLower.Model(), fitnessUpper.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCClassification(n)
{
  var totalSum:nat;
  totalSum, counter := ComputeMultiplicitySum(
    candidates, multiplicity, maximum, n, weight, counter_in);
  var fitSum:nat;
  fitSum, counter := ComputeFitSum(
    candidates, fitness, multiplicity, maximum, n, weight, counter);
  var below, above, unused:bool;
  below, unused, counter := CompareCDPCThreshold(fitSum, totalSum, fitnessLower, n, counter);
  unused, above, counter := CompareCDPCThreshold(fitSum, totalSum, fitnessUpper, n, counter);
  accepted := below || above;

  assert accepted == ClassificationDecided(candidates.Keys(), fitness.Model(), multiplicity.Model(),
    fitnessLower.Model(), fitnessUpper.Model()) by {
    classification_from_sums(candidates.Keys(), fitness.Model(), multiplicity.Model(),
      totalSum, fitSum, fitnessLower.Model(), fitnessUpper.Model());
  }
}

method {:isolate_assertions} CheckPrivateSafe<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    privateQuestions:Set<Q>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateLower:Rational,
    privateUpper:Rational,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Progress in
  requires candidates.Keys() != {}
  // Representation in
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  requires privateQuestions.Init()
  // State in
  requires privateQuestions.SizeBound(weight) <= n
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() :: multiplicity.Model()[candidate] <= maximum
  requires RationalBits(privateLower) <= n && RationalBits(privateUpper) <= n
  // State out
  ensures accepted == PrivateSafe(
    candidates.Keys(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCPrivacy(n)
{
  ghost var context := BitSetCost(weight, n);
  var totalSum:nat;
  totalSum, counter := ComputeMultiplicitySum(
    candidates, multiplicity, maximum, n, weight, counter_in);
  var remaining:Set<Q>;
  remaining := privateQuestions;
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter, context);
  accepted := true;

  ghost var baseBudget := BudgetCDPCSum(n) + BudgetPrimitiveStep(n);
  ghost var stepBudget := BudgetCDPCPrivateQuestion(n) + 3*BudgetPrimitiveStep(n);
  assert counter <= counter_in + baseBudget;
  linear_loop_budget_zero(baseBudget, stepBudget);
  while !empty
    // Progress
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == {})
    // Representation
    invariant remaining.UniverseWithin(privateQuestions)
    // State
    invariant accepted ==
      (forall question | question in
        privateQuestions.Model() - remaining.Model() ::
        exists privateSum:nat |
            PrivateSum(
            candidates.Keys(), question, multiplicity.Model(), privateSum) ::
          privateLower.Model() * (totalSum as real) <= (privateSum as real) <=
            privateUpper.Model() * (totalSum as real))
    // Cost
    invariant counter_in < counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseBudget, stepBudget,
      privateQuestions.Cardinality() - remaining.Cardinality())
  {
    remaining.universe_within_bound(privateQuestions, context);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    var question:Q;
    question, counter := remaining.Pick(counter, context);
    var questionAccepted:bool;
    questionAccepted, counter := CheckPrivateQuestion(
      candidates, question, multiplicity, totalSum,
      privateLower, privateUpper, maximum, n, weight, counter);
    accepted := accepted && questionAccepted;
    remaining, counter := remaining.Remove(question, counter, context);
    empty, counter := remaining.IsEmpty(counter, context);

    assert counter <= iterationCounter + stepBudget;
    linear_loop_budget_step(baseBudget, stepBudget, privateQuestions.Cardinality() - previousRemaining.Cardinality());

    assert privateQuestions.Model() - remaining.Model() ==
      (privateQuestions.Model() - previousRemaining.Model()) + {question};
  }
  difference_empty_set(privateQuestions.Model(), remaining.Model());
  private_safe_from_total(
    candidates.Keys(), multiplicity.Model(), privateQuestions.Model(),
    totalSum, privateLower.Model(), privateUpper.Model());
  linear_loop_budget_bound(
    baseBudget, stepBudget,
    privateQuestions.Cardinality(), n);
}

method CheckPrivateQuestion<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    multiplicity:Map_Map_T<Q, bool, nat>,
    totalSum:nat,
    privateLower:Rational,
    privateUpper:Rational,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Representation in
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  requires MultiplicitySum(
    candidates.Keys(), multiplicity.Model(), totalSum)
  // State in
  requires weight(question) <= n
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() :: multiplicity.Model()[candidate] <= maximum
  requires RationalBits(privateLower) <= n && RationalBits(privateUpper) <= n
  requires NatBits(totalSum) <= 2*n+1
  // State out
  ensures accepted ==
    (exists privateSum:nat |
      PrivateSum(
        candidates.Keys(), question, multiplicity.Model(), privateSum) ::
      privateLower.Model() * (totalSum as real) <= (privateSum as real) <=
        privateUpper.Model() * (totalSum as real))
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCPrivateQuestion(n)
{
  var privateSum:nat;
  privateSum, counter := ComputePrivateSum(
    candidates, question, multiplicity, maximum, n, weight, counter_in);
  var aboveLower, belowUpper, unused:bool;
  unused, aboveLower, counter := CompareCDPCThreshold(privateSum, totalSum, privateLower, n, counter);
  belowUpper, unused, counter := CompareCDPCThreshold(privateSum, totalSum, privateUpper, n, counter);
  accepted := aboveLower && belowUpper;
  assert accepted == (privateLower.Model() * (totalSum as real) <= (privateSum as real) <=
    privateUpper.Model() * (totalSum as real));

  private_question_from_sum(
    candidates.Keys(), question, multiplicity.Model(),
    totalSum, privateSum, privateLower.Model(), privateUpper.Model());

}

// Population filtering and multiplicity-based sums

method {:isolate_assertions} FilterCandidateMap<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    answer:bool,
    ghost n:nat, ghost weight:Q -> nat, ghost counter_in:nat)
    returns (filtered:Map_Map_T<Q, bool, bool>, ghost counter:nat)
  // Representation in
  requires candidates.Valid()
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires weight(question) <= n
  // Representation out
  ensures filtered.Valid()
  ensures filtered.UniverseWithin(candidates)
  // State out
  ensures filtered.Keys() ==
    FilterCandidates(candidates.Keys(), question, answer)
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in +
    BudgetCDPCFilter(n)
{
  ghost var context := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  // A filtered input need not be initialized; Copy narrows Universe() to Model().
  remaining, counter := candidates.Copy(counter, context);
  // Keep the original map values; only incompatible candidate keys are removed.
  filtered, counter := candidates.Copy(counter, context);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter, context);
  ghost var baseBudget := 3*BudgetPrimitiveStep(n);
  ghost var stepBudget := 6*BudgetPrimitiveStep(n);
  assert counter <= counter_in + baseBudget;
  linear_loop_budget_zero(baseBudget, stepBudget);
  while !empty
    // Progress
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Representation
    invariant remaining.UniverseWithin(candidates)
    invariant filtered.UniverseWithin(candidates)
    // State
    invariant filtered.Keys() ==
      FilterCandidates(candidates.Keys() - remaining.Keys(), question, answer) +
      remaining.Keys()
    // Cost
    invariant counter_in < counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseBudget, stepBudget, candidates.Cardinality() - remaining.Cardinality())
  {
    linear_loop_budget_step(baseBudget, stepBudget, candidates.Cardinality() - remaining.Cardinality());
    remaining, filtered, empty, counter :=
      FilterCandidateMapLoop(candidates, remaining, filtered, question, answer, n, weight, counter);
  }
  assert remaining.Cardinality() == 0;
  assert counter <= counter_in + LinearLoopBudget(baseBudget, stepBudget, candidates.Cardinality());
  filtered.universe_within_bound(candidates, context);
  linear_loop_budget_bound(
    baseBudget, stepBudget, candidates.Cardinality(), n);
}

// Filter one candidate and advance the traversal.
method {:isolate_assertions} FilterCandidateMapLoop<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    remaining_in:Map_Map_T<Q, bool, bool>,
    filtered_in:Map_Map_T<Q, bool, bool>,
    question:Q,
    answer:bool,
    ghost n:nat, ghost weight:Q -> nat, ghost counter_in:nat)
    returns (remaining:Map_Map_T<Q, bool, bool>,
             filtered:Map_Map_T<Q, bool, bool>,
             empty:bool, ghost counter:nat)
  // Progress in
  requires remaining_in.Model() != map[]
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires weight(question) <= n
  // Representation in
  requires remaining_in.UniverseWithin(candidates)
  requires filtered_in.UniverseWithin(candidates)
  // State in
  requires filtered_in.Keys() ==
    FilterCandidates(candidates.Keys() - remaining_in.Keys(), question, answer) +
    remaining_in.Keys()
  // Progress out
  ensures remaining.Cardinality() == remaining_in.Cardinality() - 1
  ensures empty == (remaining.Model() == map[])
  // Representation out
  ensures remaining.UniverseWithin(candidates)
  ensures filtered.UniverseWithin(candidates)
  // State out
  ensures filtered.Keys() ==
    FilterCandidates(candidates.Keys() - remaining.Keys(), question, answer) +
    remaining.Keys()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + 6*BudgetPrimitiveStep(n)
{
  ghost var context := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var keyContext := NestedMapKeyContext(context);
  remaining_in.universe_within_bound(candidates, context);
  filtered_in.universe_within_bound(candidates, context);
  remaining := remaining_in;
  filtered := filtered_in;
  counter := counter_in;
  var candidate:Map<Q, bool>;
  candidate, counter := remaining.PickKey(counter, context);
  remaining, counter := remaining.Remove(candidate, counter, context);

  var keep:bool;
  keep, counter := candidate.ContainsKey(question, counter, keyContext);
  if keep {
    var candidateAnswer:bool;
    candidateAnswer, counter := candidate.Get(question, counter, keyContext);
    keep := candidateAnswer == answer;
  }
  if !keep {
    filtered, counter := filtered.Remove(candidate, counter, context);
  }
  empty, counter := remaining.IsEmpty(counter, context);
  assert candidates.Keys() - remaining.Keys() ==
    (candidates.Keys() - remaining_in.Keys()) + {candidate.Model()};
  assert FilterCandidates(
    candidates.Keys() - remaining.Keys(), question, answer) ==
    if keep then
      FilterCandidates(
        candidates.Keys() - remaining_in.Keys(), question, answer) +
      {candidate.Model()}
    else
      FilterCandidates(
        candidates.Keys() - remaining_in.Keys(), question, answer);
}

// One accumulator covers map operations and length-sensitive additions.
method ComputeMultiplicitySum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (sum:nat, ghost counter:nat)
  // Representation in
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  // State in
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() ::
    multiplicity.Model()[candidate] <= maximum
  // State out
  ensures MultiplicitySum(candidates.Keys(), multiplicity.Model(), sum)
  ensures sum <= candidates.Cardinality() * maximum
  ensures NatBits(sum) <= NatBits(candidates.Cardinality()) + NatBits(maximum)
  ensures NatBits(sum) <= 2*n+1
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCSum(n)
{
  counter := counter_in;
  ghost var context := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  nat_bits_linear_bound(candidates.Cardinality());
  var remaining:Map_Map_T<Q, bool, bool>;
  // A recursive candidate map may have a wider universe than its current model.
  remaining, counter := candidates.Copy(counter, context);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter, context);
  sum := 0;
  counter := counter + 1;
  ghost var populationBits := NatBits(candidates.Cardinality()) + NatBits(maximum);
  nat_multiplication_monotonic(candidates.Cardinality(), 0, maximum);
  cdpc_sum_bits_from_count(0, candidates.Cardinality(), maximum);
  linear_loop_budget_zero(0, maximum);
  multiplicity_sum_empty(multiplicity.Model());
  ghost var baseBudget := 3*primitiveBudget;
  ghost var stepBudget := 7*primitiveBudget;
  assert counter <= counter_in + baseBudget;
  linear_loop_budget_zero(baseBudget, stepBudget);
  remaining.universe_within_bound(candidates, context);
  assert remaining.UniverseWithin(candidates);
  assert candidates.Keys() - remaining.Keys() == {};
  assert MultiplicitySum(
    candidates.Keys() - remaining.Keys(), multiplicity.Model(), sum);

  ghost var processed:nat := 0;
  while !empty
    // Progress
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Representation
    invariant remaining.USizeBound(weight, BoolBits, BoolBits) <= n
    invariant remaining.UniverseWithin(candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    // State
    invariant processed + remaining.Cardinality() == candidates.Cardinality()
    invariant remaining.Cardinality() <= candidates.Cardinality()
    invariant sum <= LinearLoopBudget(0, maximum, processed)
    invariant NatBits(sum) <= populationBits
    invariant MultiplicitySum(
      candidates.Keys() - remaining.Keys(), multiplicity.Model(), sum)
    // Cost
    invariant populationBits <= 2*n+1
    invariant counter_in < counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseBudget, stepBudget,
      processed)
  {
    remaining.universe_within_bound(candidates, context);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    ghost var previousSum := sum;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter, context);
    var candidateMultiplicity:nat;
    candidateMultiplicity, counter := multiplicity.Get(candidate, counter, multiplicityContext);
    assert counter <= iterationCounter + 2*primitiveBudget;
    assert candidateMultiplicity <= maximum;
    nat_bits_monotonic(candidateMultiplicity, maximum);
    assert CostAddNat(sum, candidateMultiplicity) <= primitiveBudget;
    sum, counter := AddNat(sum, candidateMultiplicity, counter);
    assert counter <= iterationCounter + 3*primitiveBudget;
    remaining, counter := remaining.Remove(candidate, counter, context);
    assert counter <= iterationCounter + 4*primitiveBudget;
    empty, counter := remaining.IsEmpty(counter, context);
    assert counter <= iterationCounter + 5*primitiveBudget;

    assert candidates.Cardinality() - remaining.Cardinality() == processed + 1;
    cdpc_sum_step_bound(sum, previousSum, processed, candidates.Cardinality(), maximum);

    assert counter <= iterationCounter + stepBudget;
    linear_loop_budget_step(baseBudget, stepBudget, processed);
    assert counter <= counter_in + LinearLoopBudget(baseBudget, stepBudget, processed+1);
    processed := processed+1;

    multiplicity_sum_progress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), multiplicity.Model(), previousSum, sum);
  }
  assert remaining.Cardinality() == 0;
  linear_loop_budget_bound(0, maximum, processed, candidates.Cardinality());
  assert sum <= candidates.Cardinality()*maximum;
  linear_loop_budget_bound(baseBudget, stepBudget, processed, n);
  assert counter <= counter_in+BudgetCDPCSum(n);
  difference_empty_set(candidates.Keys(), remaining.Keys());
}

method {:isolate_assertions} ComputeFitSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (sum:nat, ghost counter:nat)
  // Representation in
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  // State in
  requires fitness.SizeBound(weight, BoolBits, BoolBits) <= n
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() ::
    multiplicity.Model()[candidate] <= maximum
  // State out
  ensures FitSum(
    candidates.Keys(), fitness.Model(), multiplicity.Model(), sum)
  ensures sum <= candidates.Cardinality() * maximum
  ensures NatBits(sum) <= NatBits(candidates.Cardinality()) + NatBits(maximum)
  ensures NatBits(sum) <= 2*n+1
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCSum(n)
{
  counter := counter_in;
  ghost var context := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  nat_bits_linear_bound(candidates.Cardinality());
  var remaining:Map_Map_T<Q, bool, bool>;
  // A recursive candidate map may have a wider universe than its current model.
  remaining, counter := candidates.Copy(counter, context);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter, context);
  sum := 0;
  counter := counter + 1;
  ghost var populationBits := NatBits(candidates.Cardinality()) + NatBits(maximum);
  nat_multiplication_monotonic(candidates.Cardinality(), 0, maximum);
  cdpc_sum_bits_from_count(0, candidates.Cardinality(), maximum);
  linear_loop_budget_zero(0, maximum);
  multiplicity_sum_empty(multiplicity.Model());
  ghost var baseBudget := 3*primitiveBudget;
  ghost var stepBudget := 7*primitiveBudget;
  assert counter <= counter_in+baseBudget;
  linear_loop_budget_zero(baseBudget, stepBudget);
  assert (set candidate | candidate in
            candidates.Keys() - remaining.Keys() &&
            candidate in fitness.Model() && fitness.Model()[candidate] :: candidate) == {};

  ghost var processed:nat := 0;
  while !empty
    // Progress
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Representation
    invariant remaining.USizeBound(weight, BoolBits, BoolBits) <= n
    invariant remaining.UniverseWithin(candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= fitness.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    // State
    invariant processed + remaining.Cardinality() == candidates.Cardinality()
    invariant remaining.Cardinality() <= candidates.Cardinality()
    invariant sum <= LinearLoopBudget(0, maximum, processed)
    invariant NatBits(sum) <= populationBits
    invariant MultiplicitySum(
      set candidate | candidate in
        candidates.Keys() - remaining.Keys() &&
        candidate in fitness.Model() && fitness.Model()[candidate] :: candidate,
      multiplicity.Model(), sum)
    // Cost
    invariant populationBits <= 2*n+1
    invariant counter_in < counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseBudget, stepBudget,
      processed)
  {
    remaining.universe_within_bound(candidates, context);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    ghost var previousSum := sum;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter, context);
    var isFit:bool;
    isFit, counter := fitness.Get(candidate, counter, context);
    if isFit {
      var candidateMultiplicity:nat;
      candidateMultiplicity, counter := multiplicity.Get(candidate, counter, multiplicityContext);
      assert counter <= iterationCounter+3*primitiveBudget;
      assert candidateMultiplicity <= maximum;
      nat_bits_monotonic(candidateMultiplicity, maximum);
      assert CostAddNat(sum, candidateMultiplicity) <= primitiveBudget;
      sum, counter := AddNat(sum, candidateMultiplicity, counter);
    }
    assert counter <= iterationCounter+4*primitiveBudget;
    remaining, counter := remaining.Remove(candidate, counter, context);
    assert counter <= iterationCounter+5*primitiveBudget;
    empty, counter := remaining.IsEmpty(counter, context);
    assert counter <= iterationCounter+6*primitiveBudget;

    assert candidates.Cardinality() - remaining.Cardinality() == processed + 1;
    cdpc_sum_step_bound(sum, previousSum, processed, candidates.Cardinality(), maximum);

    assert counter <= iterationCounter + stepBudget;
    linear_loop_budget_step(baseBudget, stepBudget, processed);
    assert counter <= counter_in + LinearLoopBudget(baseBudget, stepBudget, processed+1);
    processed := processed+1;

    fit_sum_progress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), fitness.Model(), multiplicity.Model(),
      previousSum, sum, isFit);
  }
  assert remaining.Cardinality() == 0;
  linear_loop_budget_bound(0, maximum, processed, candidates.Cardinality());
  assert sum <= candidates.Cardinality()*maximum;
  linear_loop_budget_bound(baseBudget, stepBudget, processed, n);
  assert counter <= counter_in+BudgetCDPCSum(n);
  difference_empty_set(candidates.Keys(), remaining.Keys());
  fit_sum_definition(
    candidates.Keys(), fitness.Model(), multiplicity.Model(), sum,
    set candidate | candidate in candidates.Keys() &&
                    candidate in fitness.Model() &&
                    fitness.Model()[candidate] :: candidate);
}

method {:isolate_assertions} ComputePrivateSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (sum:nat, ghost counter:nat)
  // Representation in
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  // State in
  requires weight(question) <= n
  requires candidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() ::
    multiplicity.Model()[candidate] <= maximum
  // State out
  ensures PrivateSum(
    candidates.Keys(), question, multiplicity.Model(), sum)
  ensures sum <= candidates.Cardinality() * maximum
  ensures NatBits(sum) <= NatBits(candidates.Cardinality()) + NatBits(maximum)
  ensures NatBits(sum) <= 2*n+1
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCSum(n)
{
  counter := counter_in;
  ghost var context := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, n);
  ghost var keyContext := NestedMapKeyContext(context);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  nat_bits_linear_bound(candidates.Cardinality());
  var remaining:Map_Map_T<Q, bool, bool>;
  // A recursive candidate map may have a wider universe than its current model.
  remaining, counter := candidates.Copy(counter, context);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter, context);
  sum := 0;
  counter := counter + 1;
  ghost var populationBits := NatBits(candidates.Cardinality()) + NatBits(maximum);
  nat_multiplication_monotonic(candidates.Cardinality(), 0, maximum);
  cdpc_sum_bits_from_count(0, candidates.Cardinality(), maximum);
  linear_loop_budget_zero(0, maximum);
  multiplicity_sum_empty(multiplicity.Model());
  ghost var baseBudget := 3*primitiveBudget;
  ghost var stepBudget := 7*primitiveBudget;
  assert counter <= counter_in+baseBudget;
  linear_loop_budget_zero(baseBudget, stepBudget);
  assert (set candidate | candidate in
            candidates.Keys() - remaining.Keys() &&
            question in candidate && candidate[question] :: candidate) == {};

  ghost var processed:nat := 0;
  while !empty
    // Progress
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Representation
    invariant remaining.USizeBound(weight, BoolBits, BoolBits) <= n
    invariant remaining.UniverseWithin(candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    // State
    invariant processed + remaining.Cardinality() == candidates.Cardinality()
    invariant remaining.Cardinality() <= candidates.Cardinality()
    invariant sum <= LinearLoopBudget(0, maximum, processed)
    invariant NatBits(sum) <= populationBits
    invariant MultiplicitySum(
      set candidate | candidate in
        candidates.Keys() - remaining.Keys() &&
        question in candidate && candidate[question] :: candidate,
      multiplicity.Model(), sum)
    // Cost
    invariant populationBits <= 2*n+1
    invariant counter_in < counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseBudget, stepBudget,
      processed)
  {
    remaining.universe_within_bound(candidates, context);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    ghost var previousSum := sum;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter, context);
    var selected:bool;
    selected, counter := candidate.ContainsKey(question, counter, keyContext);
    if selected {
      selected, counter := candidate.Get(question, counter, keyContext);
    }
    if selected {
      var candidateMultiplicity:nat;
      candidateMultiplicity, counter := multiplicity.Get(candidate, counter, multiplicityContext);
      assert counter <= iterationCounter+4*primitiveBudget;
      assert candidateMultiplicity <= maximum;
      nat_bits_monotonic(candidateMultiplicity, maximum);
      assert CostAddNat(sum, candidateMultiplicity) <= primitiveBudget;
      sum, counter := AddNat(sum, candidateMultiplicity, counter);
    }
    assert counter <= iterationCounter+5*primitiveBudget;
    remaining, counter := remaining.Remove(candidate, counter, context);
    assert counter <= iterationCounter+6*primitiveBudget;
    empty, counter := remaining.IsEmpty(counter, context);
    assert counter <= iterationCounter+7*primitiveBudget;

    assert candidates.Cardinality() - remaining.Cardinality() == processed + 1;
    cdpc_sum_step_bound(sum, previousSum, processed, candidates.Cardinality(), maximum);

    assert counter <= iterationCounter + stepBudget;
    linear_loop_budget_step(baseBudget, stepBudget, processed);
    assert counter <= counter_in + LinearLoopBudget(baseBudget, stepBudget, processed+1);
    processed := processed+1;

    private_sum_progress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), question, multiplicity.Model(),
      previousSum, sum, selected);
  }
  assert remaining.Cardinality() == 0;
  linear_loop_budget_bound(0, maximum, processed, candidates.Cardinality());
  assert sum <= candidates.Cardinality()*maximum;
  linear_loop_budget_bound(baseBudget, stepBudget, processed, n);
  assert counter <= counter_in+BudgetCDPCSum(n);
  difference_empty_set(candidates.Keys(), remaining.Keys());
  private_sum_definition(
    candidates.Keys(), question, multiplicity.Model(), sum,
    set candidate | candidate in candidates.Keys() &&
                    question in candidate && candidate[question] :: candidate);
}

method CompareCDPCThreshold(value:nat, total:nat, threshold:Rational, ghost n:nat, ghost counter_in:nat)
    returns (atMost:bool, atLeast:bool, ghost counter:nat)
  requires NatBits(value) <= 2*n+1 && NatBits(total) <= 2*n+1
  requires RationalBits(threshold) <= n
  ensures atMost == ((value as real) <= threshold.Model() * (total as real))
  ensures atLeast == (threshold.Model() * (total as real) <= (value as real))
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCComparisonArithmetic(n)
{
  atMost, atLeast, counter := CompareNatToRational(value, total, threshold, counter_in);
  cost_compare_nat_to_rational_bound(value, total, threshold, 2*n+1, n);
}

// Supporting functional lemmas

// Relational specifications can be checked using the unique computed sums.

lemma classification_from_sums<Q(!new)>(
    candidates:set<Candidate<Q>>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, totalSum:nat, fitSum:nat,
    lower:real, upper:real)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires MultiplicitySum(candidates, multiplicity, totalSum)
  requires FitSum(candidates, fitness, multiplicity, fitSum)
  ensures ClassificationDecided(candidates, fitness, multiplicity, lower, upper) ==
    ((fitSum as real) <= lower * (totalSum as real) ||
     upper * (totalSum as real) <= (fitSum as real))
{
  reveal ClassificationDecided();
  if ClassificationDecided(candidates, fitness, multiplicity, lower, upper) {
    var semanticTotal:nat, semanticFit:nat :|
      MultiplicitySum(candidates, multiplicity, semanticTotal) &&
      FitSum(candidates, fitness, multiplicity, semanticFit) &&
      ((semanticFit as real) <= lower * (semanticTotal as real) ||
       upper * (semanticTotal as real) <= (semanticFit as real));
    multiplicity_sum_unique(candidates, multiplicity, totalSum, semanticTotal);
    fit_sum_unique(candidates, fitness, multiplicity, fitSum, semanticFit);
  }
}

lemma private_safe_from_total<Q(!new)>(
    candidates:set<Candidate<Q>>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, totalSum:nat, lower:real, upper:real)
  requires candidates != {}
  requires candidates <= multiplicity.Keys
  requires MultiplicitySum(candidates, multiplicity, totalSum)
  ensures PrivateSafe(candidates, multiplicity, privateQuestions, lower, upper) ==
    (forall question | question in privateQuestions ::
      exists sum:nat | PrivateSum(candidates, question, multiplicity, sum) ::
        lower * (totalSum as real) <= (sum as real) <= upper * (totalSum as real))
{
  reveal PrivateSafe();
  if PrivateSafe(candidates, multiplicity, privateQuestions, lower, upper) {
    var semanticTotal:nat :| MultiplicitySum(candidates, multiplicity, semanticTotal) &&
      (forall question | question in privateQuestions ::
        exists sum:nat | PrivateSum(candidates, question, multiplicity, sum) ::
          lower * (semanticTotal as real) <= (sum as real) <= upper * (semanticTotal as real));
    multiplicity_sum_unique(candidates, multiplicity, totalSum, semanticTotal);
  }
}

lemma private_question_from_sum<Q(!new)>(
    candidates:set<Candidate<Q>>, question:Q, multiplicity:map<Candidate<Q>, nat>,
    totalSum:nat, privateSum:nat, lower:real, upper:real)
  requires candidates <= multiplicity.Keys
  requires PrivateSum(candidates, question, multiplicity, privateSum)
  ensures forall sum:nat | PrivateSum(candidates, question, multiplicity, sum) :: sum == privateSum
  ensures (exists sum:nat | PrivateSum(candidates, question, multiplicity, sum) ::
    lower * (totalSum as real) <= (sum as real) <= upper * (totalSum as real)) ==
    (lower * (totalSum as real) <= (privateSum as real) <= upper * (totalSum as real))
{
  forall sum:nat | PrivateSum(candidates, question, multiplicity, sum)
    ensures sum == privateSum
  {
    private_sum_unique(candidates, question, multiplicity, privateSum, sum);
  }
}

lemma multiplicity_sum_progress<Q(!new)>(
    allCandidates:set<Candidate<Q>>,
    previousRemaining:set<Candidate<Q>>,
    remaining:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    multiplicity:map<Candidate<Q>, nat>,
    previousSum:nat,
    sum:nat)
  requires previousRemaining <= allCandidates
  requires allCandidates <= multiplicity.Keys
  requires candidate in previousRemaining
  requires remaining == previousRemaining - {candidate}
  requires MultiplicitySum(
    allCandidates - previousRemaining, multiplicity, previousSum)
  requires sum == previousSum + multiplicity[candidate]
  ensures MultiplicitySum(allCandidates - remaining, multiplicity, sum)
{
  assert candidate !in allCandidates - previousRemaining;
  multiplicity_sum_add(
    allCandidates - previousRemaining, candidate,
    multiplicity, previousSum);
  assert allCandidates - remaining ==
    (allCandidates - previousRemaining) + {candidate};
}

lemma fit_sum_progress<Q(!new)>(
    allCandidates:set<Candidate<Q>>,
    previousRemaining:set<Candidate<Q>>,
    remaining:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    previousSum:nat,
    sum:nat,
    isFit:bool)
  requires previousRemaining <= allCandidates
  requires allCandidates <= fitness.Keys
  requires allCandidates <= multiplicity.Keys
  requires candidate in previousRemaining
  requires remaining == previousRemaining - {candidate}
  requires isFit == fitness[candidate]
  requires sum == if isFit
                   then previousSum + multiplicity[candidate]
                   else previousSum
  requires MultiplicitySum(
    set element | element in allCandidates - previousRemaining &&
      element in fitness && fitness[element] :: element,
    multiplicity, previousSum)
  ensures MultiplicitySum(
    set element | element in allCandidates - remaining &&
      element in fitness && fitness[element] :: element,
    multiplicity, sum)
{
  ghost var previousFit :=
    set element | element in allCandidates - previousRemaining &&
      element in fitness && fitness[element] :: element;
  ghost var currentFit :=
    set element | element in allCandidates - remaining &&
      element in fitness && fitness[element] :: element;
  if isFit {
    assert candidate !in previousFit;
    multiplicity_sum_add(previousFit, candidate, multiplicity, previousSum);
    assert currentFit == previousFit + {candidate};
  } else {
    assert currentFit == previousFit;
  }
}

lemma private_sum_progress<Q(!new)>(
    allCandidates:set<Candidate<Q>>,
    previousRemaining:set<Candidate<Q>>,
    remaining:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    question:Q,
    multiplicity:map<Candidate<Q>, nat>,
    previousSum:nat,
    sum:nat,
    selected:bool)
  requires previousRemaining <= allCandidates
  requires allCandidates <= multiplicity.Keys
  requires candidate in previousRemaining
  requires remaining == previousRemaining - {candidate}
  requires selected ==
    (question in candidate && candidate[question])
  requires sum == if selected
                   then previousSum + multiplicity[candidate]
                   else previousSum
  requires MultiplicitySum(
    set element | element in allCandidates - previousRemaining &&
      question in element && element[question] :: element,
    multiplicity, previousSum)
  ensures MultiplicitySum(
    set element | element in allCandidates - remaining &&
      question in element && element[question] :: element,
    multiplicity, sum)
{
  ghost var previousPrivate :=
    set element | element in allCandidates - previousRemaining &&
      question in element && element[question] :: element;
  ghost var currentPrivate :=
    set element | element in allCandidates - remaining &&
      question in element && element[question] :: element;
  if selected {
    assert candidate !in previousPrivate;
    multiplicity_sum_add(
      previousPrivate, candidate, multiplicity, previousSum);
    assert currentPrivate == previousPrivate + {candidate};
  } else {
    assert currentPrivate == previousPrivate;
  }
}
