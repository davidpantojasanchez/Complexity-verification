include "../Lemmas/PolynomialBounds.dfy"
include "../Problems/CDPCLemmas.dfy"
include "../Collections/Set.dfy"
include "../Collections/Map.dfy"
include "../Lemmas/Lemmas.dfy"

/*
Proof support for VerificationCDPC.dfy
*/


// Classification and privacy checks

method CheckClassification<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    fitnessLower:real,
    fitnessUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires candidates.Keys() != {}
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  ensures accepted == ClassificationDecided(
    candidates.Keys(), fitness.Model(), multiplicity.Model(),
    fitnessLower, fitnessUpper)
  ensures counter <= counter_in +
    CostCheckClassification(candidates, fitness, multiplicity)
{
  var totalSum:nat;
  totalSum, counter := ComputeMultiplicitySum(
    candidates, multiplicity, counter_in);
  var fitSum:nat;
  fitSum, counter := ComputeFitSum(
    candidates, fitness, multiplicity, counter);
  accepted :=
    (fitSum as real) <= fitnessLower * (totalSum as real) ||
    fitnessUpper * (totalSum as real) <= (fitSum as real);
  counter := counter + 1;

  classification_from_sums(
    candidates.Keys(), fitness.Model(), multiplicity.Model(),
    totalSum, fitSum, fitnessLower, fitnessUpper);
}


method {:isolate_assertions} CheckPrivateSafe<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    privateQuestions:Set<Q>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateLower:real,
    privateUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Termination in
  requires candidates.Keys() != {}
  // Types in
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  requires privateQuestions.Init()
  // Invariant out
  ensures accepted == PrivateSafe(
    candidates.Keys(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper)
  // Counter
  ensures counter <= counter_in +
    CostCheckPrivateSafe(candidates, privateQuestions, multiplicity)
{
  var totalSum:nat;
  totalSum, counter := ComputeMultiplicitySum(
    candidates, multiplicity, counter_in);
  var remaining:Set<Q>;
  remaining := privateQuestions;
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter);
  accepted := true;

  ghost var baseCost :=
    CostComputeMultiplicitySum(candidates, multiplicity) +
    privateQuestions.CostIsEmpty();
  ghost var stepCost :=
    privateQuestions.CostPick() +
    CostCheckPrivateQuestion(candidates, multiplicity) +
    privateQuestions.UCostRemove() +
    privateQuestions.CostIsEmpty();
  linear_loop_budget_zero(baseCost, stepCost);
  while !empty
    // Termination
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == {})
    // Types
    invariant remaining.UniverseWithin(privateQuestions)
    // Regular invariants
    invariant accepted ==
      (forall question | question in
        privateQuestions.Model() - remaining.Model() ::
        exists privateSum:nat |
            PrivateSum(
            candidates.Keys(), question, multiplicity.Model(), privateSum) ::
          privateLower * (totalSum as real) <= (privateSum as real) <=
            privateUpper * (totalSum as real))
    // Counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      privateQuestions.Cardinality() - remaining.Cardinality())
  {
    remaining.universe_within_bound(privateQuestions);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    var question:Q;
    question, counter := remaining.Pick(counter);
    var questionAccepted:bool;
    questionAccepted, counter := CheckPrivateQuestion(
      candidates, question, multiplicity, totalSum,
      privateLower, privateUpper, counter);
    accepted := accepted && questionAccepted;
    remaining, counter := remaining.Remove(question, counter);
    empty, counter := remaining.IsEmpty(counter);

    assert counter <= iterationCounter + stepCost;
    linear_loop_budget_step(baseCost, stepCost, privateQuestions.Cardinality() - previousRemaining.Cardinality());

    assert privateQuestions.Model() - remaining.Model() ==
      (privateQuestions.Model() - previousRemaining.Model()) + {question};
  }
  set_difference_empty(privateQuestions.Model(), remaining.Model());
  private_safe_from_total(
    candidates.Keys(), multiplicity.Model(), privateQuestions.Model(),
    totalSum, privateLower, privateUpper);
  linear_loop_budget_bound(
    baseCost, stepCost,
    privateQuestions.Cardinality(), privateQuestions.UCardinality());
}


method CheckPrivateQuestion<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    multiplicity:Map_Map_T<Q, bool, nat>,
    totalSum:nat,
    privateLower:real,
    privateUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  requires MultiplicitySum(
    candidates.Keys(), multiplicity.Model(), totalSum)
  ensures accepted ==
    (exists privateSum:nat |
      PrivateSum(
        candidates.Keys(), question, multiplicity.Model(), privateSum) ::
      privateLower * (totalSum as real) <= (privateSum as real) <=
        privateUpper * (totalSum as real))
  ensures counter <= counter_in +
    CostCheckPrivateQuestion(candidates, multiplicity)
{
  var privateSum:nat;
  privateSum, counter := ComputePrivateSum(
    candidates, question, multiplicity, counter_in);
  accepted :=
    privateLower * (totalSum as real) <= (privateSum as real) <=
    privateUpper * (totalSum as real);
  counter := counter + 1;

  private_question_from_sum(
    candidates.Keys(), question, multiplicity.Model(),
    totalSum, privateSum, privateLower, privateUpper);
}


// Population filtering and multiplicity-based sums

method {:isolate_assertions} FilterCandidateMap<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    answer:bool,
    ghost counter_in:nat)
    returns (filtered:Map_Map_T<Q, bool, bool>, ghost counter:nat)
  // Types in
  requires candidates.Valid()
  // Types out
  ensures filtered.Valid()
  ensures filtered.UniverseWithin(candidates)
  // Invariant out
  ensures filtered.Keys() ==
    FilterCandidates(candidates.Keys(), question, answer)
  // Counter
  ensures counter <= counter_in +
    CostFilterCandidateMap(candidates)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  // A filtered input need not be initialized; Copy narrows Universe() to Model().
  remaining, counter := candidates.Copy(counter);
  // Keep the original map values; only incompatible candidate keys are removed.
  filtered, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter);
  ghost var baseCost :=
    2 * candidates.UCostCopy() + candidates.CostIsEmpty();
  ghost var stepCost :=
    candidates.UCostPickKey() +
    2 * (candidates.UCardinalityKeys() + 1) +
    2 * candidates.UCostRemove() + candidates.CostIsEmpty();
  linear_loop_budget_zero(baseCost, stepCost);
  while !empty
    // Termination
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Types
    invariant remaining.UniverseWithin(candidates)
    invariant filtered.UniverseWithin(candidates)
    // Regular invariants
    invariant filtered.Keys() ==
      FilterCandidates(candidates.Keys() - remaining.Keys(), question, answer) +
      remaining.Keys()
    // Counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost, candidates.Cardinality() - remaining.Cardinality())
  {
    linear_loop_budget_step(baseCost, stepCost, candidates.Cardinality() - remaining.Cardinality());
    remaining, filtered, empty, counter :=
      FilterCandidateMapLoop(candidates, remaining, filtered, question, answer, counter);
  }
  filtered.universe_within_bound(candidates);
  linear_loop_budget_bound(
    baseCost, stepCost, candidates.Cardinality(), candidates.UCardinality());
}


// Filter one candidate and advance the traversal.
method FilterCandidateMapLoop<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    remaining_in:Map_Map_T<Q, bool, bool>,
    filtered_in:Map_Map_T<Q, bool, bool>,
    question:Q,
    answer:bool,
    ghost counter_in:nat)
    returns (remaining:Map_Map_T<Q, bool, bool>,
             filtered:Map_Map_T<Q, bool, bool>,
             empty:bool, ghost counter:nat)
  // Termination in
  requires remaining_in.Model() != map[]
  // Types in
  requires remaining_in.UniverseWithin(candidates)
  requires filtered_in.UniverseWithin(candidates)
  // Invariant in
  requires filtered_in.Keys() ==
    FilterCandidates(candidates.Keys() - remaining_in.Keys(), question, answer) +
    remaining_in.Keys()
  // Termination out
  ensures remaining.Cardinality() == remaining_in.Cardinality() - 1
  ensures empty == (remaining.Model() == map[])
  // Types out
  ensures remaining.UniverseWithin(candidates)
  ensures filtered.UniverseWithin(candidates)
  // Invariant out
  ensures filtered.Keys() ==
    FilterCandidates(candidates.Keys() - remaining.Keys(), question, answer) +
    remaining.Keys()
  // Counter
  ensures counter <= counter_in + (
    candidates.UCostPickKey() +
    2 * (candidates.UCardinalityKeys() + 1) +
    2 * candidates.UCostRemove() + candidates.CostIsEmpty())
{
  remaining_in.universe_within_bound(candidates);
  filtered_in.universe_within_bound(candidates);
  remaining := remaining_in;
  filtered := filtered_in;
  counter := counter_in;
  var candidate:Map<Q, bool>;
  candidate, counter := remaining.PickKey(counter);
  remaining, counter := remaining.Remove(candidate, counter);

  var keep:bool;
  keep, counter := candidate.ContainsKey(question, counter);
  if keep {
    var candidateAnswer:bool;
    candidateAnswer, counter := candidate.Get(question, counter);
    keep := candidateAnswer == answer;
  }
  if !keep {
    filtered, counter := filtered.Remove(candidate, counter);
  }
  empty, counter := remaining.IsEmpty(counter);
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


method ComputeMultiplicitySum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost counter_in:nat)
    returns (sum:nat, ghost counter:nat)
  // Types in
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  // Invariant out
  ensures MultiplicitySum(candidates.Keys(), multiplicity.Model(), sum)
  // Counter
  ensures counter <= counter_in +
    CostComputeMultiplicitySum(candidates, multiplicity)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  // A recursive candidate map may have a wider universe than its current model.
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter);
  sum := 0;
  multiplicity_sum_empty(multiplicity.Model());
  ghost var baseCost :=
    candidates.UCostCopy() + candidates.CostIsEmpty();
  ghost var stepCost :=
    candidates.UCostPickKey() +
    multiplicity.UCostGet() +
    candidates.UCostRemove() +
    candidates.CostIsEmpty();
  linear_loop_budget_zero(baseCost, stepCost);
  assert remaining.UniverseWithin(candidates);
  assert candidates.Keys() - remaining.Keys() == {};
  assert MultiplicitySum(
    candidates.Keys() - remaining.Keys(), multiplicity.Model(), sum);

  assert {:split_here} true;
  while !empty
    // Termination
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Types
    invariant remaining.UniverseWithin(candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    // Regular invariants
    invariant MultiplicitySum(
      candidates.Keys() - remaining.Keys(), multiplicity.Model(), sum)
    // Counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    remaining.universe_within_bound(candidates);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    ghost var previousSum := sum;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter);
    var candidateMultiplicity:nat;
    candidateMultiplicity, counter := multiplicity.Get(candidate, counter);
    sum := sum + candidateMultiplicity;
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.IsEmpty(counter);

    assert counter <= iterationCounter + stepCost;
    linear_loop_budget_step(baseCost, stepCost, candidates.Cardinality() - previousRemaining.Cardinality());

    multiplicity_sum_progress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), multiplicity.Model(), previousSum, sum);
  }
  assert {:split_here} true;
  set_difference_empty(candidates.Keys(), remaining.Keys());
  linear_loop_budget_bound(
    baseCost, stepCost,
    candidates.Cardinality(), candidates.UCardinality());
}


method ComputeFitSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost counter_in:nat)
    returns (sum:nat, ghost counter:nat)
  // Types in
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  // Invariant out
  ensures FitSum(
    candidates.Keys(), fitness.Model(), multiplicity.Model(), sum)
  // Counter
  ensures counter <= counter_in +
    CostComputeFitSum(candidates, fitness, multiplicity)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  // A recursive candidate map may have a wider universe than its current model.
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter);
  sum := 0;
  multiplicity_sum_empty(multiplicity.Model());
  ghost var baseCost :=
    candidates.UCostCopy() + candidates.CostIsEmpty();
  ghost var stepCost :=
    candidates.UCostPickKey() +
    fitness.UCostGet() +
    multiplicity.UCostGet() +
    candidates.UCostRemove() +
    candidates.CostIsEmpty();
  linear_loop_budget_zero(baseCost, stepCost);
  assert (set candidate | candidate in
            candidates.Keys() - remaining.Keys() &&
            candidate in fitness.Model() && fitness.Model()[candidate] :: candidate) == {};

  assert {:split_here} true;
  while !empty
    // Termination
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Types
    invariant remaining.UniverseWithin(candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= fitness.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    // Regular invariants
    invariant MultiplicitySum(
      set candidate | candidate in
        candidates.Keys() - remaining.Keys() &&
        candidate in fitness.Model() && fitness.Model()[candidate] :: candidate,
      multiplicity.Model(), sum)
    // Counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    remaining.universe_within_bound(candidates);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    ghost var previousSum := sum;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter);
    var isFit:bool;
    isFit, counter := fitness.Get(candidate, counter);
    if isFit {
      var candidateMultiplicity:nat;
      candidateMultiplicity, counter := multiplicity.Get(candidate, counter);
      sum := sum + candidateMultiplicity;
    }
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.IsEmpty(counter);

    assert counter <= iterationCounter + stepCost;
    linear_loop_budget_step(baseCost, stepCost, candidates.Cardinality() - previousRemaining.Cardinality());

    fit_sum_progress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), fitness.Model(), multiplicity.Model(),
      previousSum, sum, isFit);
  }
  assert {:split_here} true;
  set_difference_empty(candidates.Keys(), remaining.Keys());
  fit_sum_definition(
    candidates.Keys(), fitness.Model(), multiplicity.Model(), sum,
    set candidate | candidate in candidates.Keys() &&
                    candidate in fitness.Model() &&
                    fitness.Model()[candidate] :: candidate);
  linear_loop_budget_bound(
    baseCost, stepCost,
    candidates.Cardinality(), candidates.UCardinality());
}


method {:isolate_assertions} ComputePrivateSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost counter_in:nat)
    returns (sum:nat, ghost counter:nat)
  // Types in
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  // Invariant out
  ensures PrivateSum(
    candidates.Keys(), question, multiplicity.Model(), sum)
  // Counter
  ensures counter <= counter_in +
    CostComputePrivateSum(candidates, multiplicity)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  // A recursive candidate map may have a wider universe than its current model.
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter);
  sum := 0;
  multiplicity_sum_empty(multiplicity.Model());
  ghost var baseCost :=
    candidates.UCostCopy() + candidates.CostIsEmpty();
  ghost var stepCost :=
    candidates.UCostPickKey() +
    2 * (candidates.UCardinalityKeys() + 1) +
    multiplicity.UCostGet() +
    candidates.UCostRemove() +
    candidates.CostIsEmpty();
  linear_loop_budget_zero(baseCost, stepCost);
  assert (set candidate | candidate in
            candidates.Keys() - remaining.Keys() &&
            question in candidate && candidate[question] :: candidate) == {};

  while !empty
    // Termination
    decreases remaining.Cardinality()
    invariant empty == (remaining.Model() == map[])
    // Types
    invariant remaining.UniverseWithin(candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    // Regular invariants
    invariant MultiplicitySum(
      set candidate | candidate in
        candidates.Keys() - remaining.Keys() &&
        question in candidate && candidate[question] :: candidate,
      multiplicity.Model(), sum)
    // Counter
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    remaining.universe_within_bound(candidates);
    ghost var iterationCounter := counter;
    ghost var previousRemaining := remaining;
    ghost var previousSum := sum;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter);
    var selected:bool;
    selected, counter := candidate.ContainsKey(question, counter);
    if selected {
      selected, counter := candidate.Get(question, counter);
    }
    if selected {
      var candidateMultiplicity:nat;
      candidateMultiplicity, counter := multiplicity.Get(candidate, counter);
      sum := sum + candidateMultiplicity;
    }
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.IsEmpty(counter);

    assert counter <= iterationCounter + stepCost;
    linear_loop_budget_step(baseCost, stepCost, candidates.Cardinality() - previousRemaining.Cardinality());

    private_sum_progress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), question, multiplicity.Model(),
      previousSum, sum, selected);
  }
  set_difference_empty(candidates.Keys(), remaining.Keys());
  private_sum_definition(
    candidates.Keys(), question, multiplicity.Model(), sum,
    set candidate | candidate in candidates.Keys() &&
                    question in candidate && candidate[question] :: candidate);
  linear_loop_budget_bound(
    baseCost, stepCost,
    candidates.Cardinality(), candidates.UCardinality());
}


// Input-dependent ghost cost budgets

ghost function CostFilterCandidateMap<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>):nat
{
  2 * candidates.UCostCopy() +
  candidates.CostIsEmpty() +
  candidates.UCardinality() *
    (candidates.UCostPickKey() +
     2 * (candidates.UCardinalityKeys() + 1) +
     2 * candidates.UCostRemove() +
     candidates.CostIsEmpty())
}


ghost function CostComputeMultiplicitySum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  candidates.UCostCopy() + candidates.CostIsEmpty() +
  candidates.UCardinality() *
    (candidates.UCostPickKey() +
     multiplicity.UCostGet() +
     candidates.UCostRemove() +
     candidates.CostIsEmpty())
}


ghost function CostComputeFitSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  candidates.UCostCopy() + candidates.CostIsEmpty() +
  candidates.UCardinality() *
    (candidates.UCostPickKey() +
     fitness.UCostGet() +
     multiplicity.UCostGet() +
     candidates.UCostRemove() +
     candidates.CostIsEmpty())
}


ghost function CostComputePrivateSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  candidates.UCostCopy() + candidates.CostIsEmpty() +
  candidates.UCardinality() *
    (candidates.UCostPickKey() +
     2 * (candidates.UCardinalityKeys() + 1) +
     multiplicity.UCostGet() +
     candidates.UCostRemove() +
     candidates.CostIsEmpty())
}


ghost function CostCheckClassification<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  CostComputeMultiplicitySum(candidates, multiplicity) +
  CostComputeFitSum(candidates, fitness, multiplicity) + 1
}


ghost function CostCheckPrivateQuestion<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  CostComputePrivateSum(candidates, multiplicity) + 1
}


ghost function CostCheckPrivateSafe<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    privateQuestions:Set<Q>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  CostComputeMultiplicitySum(candidates, multiplicity) +
  privateQuestions.CostIsEmpty() +
  privateQuestions.UCardinality() *
    (privateQuestions.CostPick() +
     CostCheckPrivateQuestion(candidates, multiplicity) +
     privateQuestions.UCostRemove() +
     privateQuestions.CostIsEmpty())
}


ghost function CostCountInterviewNode<Q(!new)>(interview:Interview<Q>):nat
{
  interview.CostIsEnd() + 2*interview.CostBranch()
}


ghost function CostCheckInterviewFitsNode<Q(!new)>(rootQuestions:Set<Q>, interview:Interview<Q>):nat
{
  interview.CostIsEnd() + interview.CostQuestion() +
  rootQuestions.UCostContains() +
  rootQuestions.UCostRemove() +
  2 * interview.CostBranch()
}


ghost function CostVerifyCDPCCertificateNode<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, interview:Interview<Q>):nat
{
  interview.CostIsEnd() + interview.CostQuestion() +
  2 * CostFilterCandidateMap(rootCandidates) +
  2 * interview.CostBranch() + rootCandidates.CostIsEmpty() +
  CostCheckClassification(rootCandidates, fitness, multiplicity) +
  CostCheckPrivateSafe(rootCandidates, privateQuestions, multiplicity) + 1
}


ghost function CostVerifyCDPCCertificate<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
{
  if interview.NodeCount() == 0 then 0
  else
    nat_multiplication_monotonic(2 * interview.NodeCount() - 1, 0,
      CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview));
    (2 * interview.NodeCount() - 1) * CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview)
}


ghost function CostCheckCDPCBranch<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
{
  2 * interview.NodeCount() * CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview)
}


// Final polynomial ghost cost function with respect to the problem's inputs

ghost function {:opaque} {:isolate_assertions} CostVerifyCDPC<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>, questions:Set<Q>, interview:Interview<Q>):(cost:nat)
  ensures fitness.CostCount() + questions.CostCount() + (2*fitness.Cardinality()*questions.USize()+2)*CostCountInterviewNode(interview) <= cost

{
  var b := 2*fitness.Cardinality()*questions.USize()+1;
  fitness.CostCount() + questions.CostCount() + (b+1)*CostCountInterviewNode(interview) +
  b*CostCheckInterviewFitsNode(questions, interview) + 2*b*CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions, interview)
}


// Fixed scalar polynomials for the final complexity bound

ghost function PolynomialVerifyCDPCNode(n:nat):nat
{
  var c := n*n+1;
  var d := n+1;
  var sum := c+1+n*(d+2*c+1);
  var filter := 2*c+1+n*(3*d+2*c+1);
  var fit := c+1+n*(d+3*c+1);
  var privateSum := c+1+n*(3*d+2*c+1);
  6+2*filter+(sum+fit+1)+(sum+1+n*(privateSum+n+4))
}


ghost function PolynomialVerifyCDPC(n:nat):nat
{
  var nodes := 2*n*n+1;
  2 + (nodes+1)*3 + nodes*(2*n+6) + 2*nodes*PolynomialVerifyCDPCNode(n)
}


// Enumeration laws used to make multiplicity sums independent of sequence order.

lemma multiset_cancellation<T>(common:multiset<T>, first:multiset<T>, second:multiset<T>)
  requires common + first == common + second
  ensures first == second
{
  forall element
    ensures first[element] == second[element]
  {
    assert (common + first)[element] == common[element] + first[element];
    assert (common + second)[element] == common[element] + second[element];
  }
}


lemma sequence_multiplicity_sum_concat<Q(!new)>(
    left:seq<Candidate<Q>>,
    right:seq<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>)
  decreases |left|
  requires forall candidate | candidate in left + right ::
    candidate in multiplicity.Keys
  ensures SequenceMultiplicitySum(left + right, multiplicity) ==
          SequenceMultiplicitySum(left, multiplicity) +
          SequenceMultiplicitySum(right, multiplicity)
{
  if left == [] {
    assert left + right == right;
    reveal SequenceMultiplicitySum();
  } else {
    assert (left + right)[0] == left[0];
    assert (left + right)[1..] == left[1..] + right;
    sequence_multiplicity_sum_concat(left[1..], right, multiplicity);
    calc {
      SequenceMultiplicitySum(left + right, multiplicity);
      == {
        reveal SequenceMultiplicitySum();
      }
      multiplicity[left[0]] +
        SequenceMultiplicitySum(left[1..] + right, multiplicity);
      ==
      multiplicity[left[0]] +
         SequenceMultiplicitySum(left[1..], multiplicity) +
         SequenceMultiplicitySum(right, multiplicity);
      == {
        reveal SequenceMultiplicitySum();
      }
      SequenceMultiplicitySum(left, multiplicity) +
        SequenceMultiplicitySum(right, multiplicity);
    }
  }
}


lemma sequence_multiplicity_sum_remove_at<Q(!new)>(
    values:seq<Candidate<Q>>,
    index:nat,
    multiplicity:map<Candidate<Q>, nat>)
  requires index < |values|
  requires forall candidate | candidate in values ::
    candidate in multiplicity.Keys
  ensures SequenceMultiplicitySum(values, multiplicity) ==
          multiplicity[values[index]] +
          SequenceMultiplicitySum(values[..index] + values[index + 1..], multiplicity)
{
  var prefix := values[..index];
  var suffix := values[index + 1..];
  assert values == prefix + ([values[index]] + suffix);
  sequence_multiplicity_sum_concat(prefix, [values[index]] + suffix, multiplicity);
  sequence_multiplicity_sum_concat(prefix, suffix, multiplicity);
}


lemma sequence_multiplicity_sum_permutation<Q(!new)>(
    first:seq<Candidate<Q>>,
    second:seq<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>)
  decreases |first|
  requires multiset(first) == multiset(second)
  requires forall candidate | candidate in first + second ::
    candidate in multiplicity.Keys
  ensures SequenceMultiplicitySum(first, multiplicity) ==
          SequenceMultiplicitySum(second, multiplicity)
{
  if first != [] {
    var candidate := first[0];
    assert candidate in first;
    assert multiset(first)[candidate] > 0;
    assert multiset(second)[candidate] > 0;
    assert candidate in second;
    var index :| 0 <= index < |second| && second[index] == candidate;
    var secondWithout := second[..index] + second[index + 1..];

    assert second == second[..index] + [candidate] + second[index + 1..];
    assert first == [candidate] + first[1..];
    assert multiset(first) == multiset{candidate} + multiset(first[1..]);
    assert multiset(second) == multiset{candidate} + multiset(secondWithout);
    assert multiset{candidate} + multiset(first[1..]) ==
           multiset{candidate} + multiset(secondWithout);
    multiset_cancellation(
      multiset{candidate}, multiset(first[1..]), multiset(secondWithout));
    assert forall element | element in first[1..] + secondWithout ::
      element in multiplicity.Keys;
    sequence_multiplicity_sum_permutation(first[1..], secondWithout, multiplicity);
    sequence_multiplicity_sum_remove_at(second, index, multiplicity);
    assert SequenceMultiplicitySum(first, multiplicity) ==
           multiplicity[candidate] +
           SequenceMultiplicitySum(first[1..], multiplicity) by {
      reveal SequenceMultiplicitySum();
    }
    calc {
      SequenceMultiplicitySum(first, multiplicity);
      == multiplicity[candidate] +
         SequenceMultiplicitySum(first[1..], multiplicity);
      == multiplicity[candidate] +
         SequenceMultiplicitySum(secondWithout, multiplicity);
      == SequenceMultiplicitySum(second, multiplicity);
    }
  }
}


// Uniqueness of total, fitness and private-answer sums for semantic comparisons.

lemma multiplicity_sum_unique<Q(!new)>(
    candidates:set<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>,
    first:nat,
    second:nat)
  requires candidates <= multiplicity.Keys
  requires MultiplicitySum(candidates, multiplicity, first)
  requires MultiplicitySum(candidates, multiplicity, second)
  ensures first == second
{
  reveal MultiplicitySum();
  var firstEnumeration :| multiset(firstEnumeration) == multiset(candidates) &&
    (forall candidate | candidate in firstEnumeration :: candidate in multiplicity.Keys) &&
    first == SequenceMultiplicitySum(firstEnumeration, multiplicity);
  var secondEnumeration :| multiset(secondEnumeration) == multiset(candidates) &&
    (forall candidate | candidate in secondEnumeration :: candidate in multiplicity.Keys) &&
    second == SequenceMultiplicitySum(secondEnumeration, multiplicity);
  sequence_multiplicity_sum_permutation(firstEnumeration, secondEnumeration, multiplicity);
}


lemma fit_sum_unique<Q(!new)>(
    candidates:set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    first:nat,
    second:nat)
  requires candidates <= multiplicity.Keys
  requires FitSum(candidates, fitness, multiplicity, first)
  requires FitSum(candidates, fitness, multiplicity, second)
  ensures first == second
{
  reveal FitSum();
  multiplicity_sum_unique(
    set candidate | candidate in candidates &&
                    candidate in fitness && fitness[candidate] :: candidate,
    multiplicity, first, second);
}


lemma private_sum_unique<Q(!new)>(
    candidates:set<Candidate<Q>>,
    question:Q,
    multiplicity:map<Candidate<Q>, nat>,
    first:nat,
    second:nat)
  requires candidates <= multiplicity.Keys
  requires PrivateSum(candidates, question, multiplicity, first)
  requires PrivateSum(candidates, question, multiplicity, second)
  ensures first == second
{
  reveal PrivateSum();
  multiplicity_sum_unique(
    set candidate | candidate in candidates &&
                    question in candidate && candidate[question] :: candidate,
    multiplicity, first, second);
}


// Sum extension and iteration progress used by the executable counting loops.

lemma multiplicity_sum_add<Q(!new)>(
    candidates:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    multiplicity:map<Candidate<Q>, nat>,
    sum:nat)
  requires candidates <= multiplicity.Keys
  requires candidate in multiplicity.Keys
  requires candidate !in candidates
  requires MultiplicitySum(candidates, multiplicity, sum)
  ensures MultiplicitySum(
    candidates + {candidate}, multiplicity, sum + multiplicity[candidate])
{
  reveal MultiplicitySum();
  var enumeration :| multiset(enumeration) == multiset(candidates) &&
    (forall element | element in enumeration :: element in multiplicity.Keys) &&
    sum == SequenceMultiplicitySum(enumeration, multiplicity);
  sequence_multiplicity_sum_concat(enumeration, [candidate], multiplicity);
  assert multiset(enumeration + [candidate]) ==
         multiset(candidates + {candidate});
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


lemma private_question_from_sum<Q(!new)>(
    candidates:set<Candidate<Q>>, question:Q, multiplicity:map<Candidate<Q>, nat>,
    totalSum:nat, privateSum:nat, lower:real, upper:real)
  requires candidates <= multiplicity.Keys
  requires PrivateSum(candidates, question, multiplicity, privateSum)
  ensures (exists sum:nat | PrivateSum(candidates, question, multiplicity, sum) ::
    lower * (totalSum as real) <= (sum as real) <= upper * (totalSum as real)) ==
    (lower * (totalSum as real) <= (privateSum as real) <= upper * (totalSum as real))
{
  if exists sum:nat | PrivateSum(candidates, question, multiplicity, sum) ::
      lower * (totalSum as real) <= (sum as real) <= upper * (totalSum as real) {
    var sum:nat :| PrivateSum(candidates, question, multiplicity, sum) &&
      lower * (totalSum as real) <= (sum as real) <= upper * (totalSum as real);
    private_sum_unique(candidates, question, multiplicity, privateSum, sum);
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


// Cost functions are monotonic for the candidate populations

lemma cost_cdpc_candidate_monotonic<Q(!new)>(
    smaller:Map_Map_T<Q, bool, bool>,
    larger:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>)
  requires smaller.UniverseWithin(larger)
  ensures CostComputeMultiplicitySum(smaller, multiplicity) <=
          CostComputeMultiplicitySum(larger, multiplicity)
  ensures CostComputeFitSum(smaller, fitness, multiplicity) <=
          CostComputeFitSum(larger, fitness, multiplicity)
  ensures CostComputePrivateSum(smaller, multiplicity) <=
          CostComputePrivateSum(larger, multiplicity)
  ensures CostFilterCandidateMap(smaller) <=
          CostFilterCandidateMap(larger)
  ensures CostCheckClassification(smaller, fitness, multiplicity) <=
          CostCheckClassification(larger, fitness, multiplicity)
  ensures CostCheckPrivateQuestion(smaller, multiplicity) <=
          CostCheckPrivateQuestion(larger, multiplicity)
  ensures CostCheckPrivateSafe(smaller, privateQuestions, multiplicity) <=
          CostCheckPrivateSafe(larger, privateQuestions, multiplicity)
{
  smaller.universe_within_bound(larger);
  assert smaller.UCostCopy() <=
         larger.UCostCopy();
  assert smaller.UCostRemove() <=
         larger.UCostRemove();
  assert smaller.UCostPickKey() <=
         larger.UCostPickKey();

  nonnegative_product_monotonic(
    smaller.UCardinality(),
    smaller.UCostPickKey() + multiplicity.UCostGet() + smaller.UCostRemove() + smaller.CostIsEmpty(),
    larger.UCardinality(),
    larger.UCostPickKey() + multiplicity.UCostGet() + larger.UCostRemove() + larger.CostIsEmpty());
  nonnegative_product_monotonic(
    smaller.UCardinality(),
    smaller.UCostPickKey() + fitness.UCostGet() + multiplicity.UCostGet() + smaller.UCostRemove() + smaller.CostIsEmpty(),
    larger.UCardinality(),
    larger.UCostPickKey() + fitness.UCostGet() + multiplicity.UCostGet() + larger.UCostRemove() + larger.CostIsEmpty());
  nonnegative_product_monotonic(
    smaller.UCardinality(),
    smaller.UCostPickKey() + 2 * (smaller.UCardinalityKeys() + 1) + multiplicity.UCostGet() + smaller.UCostRemove() + smaller.CostIsEmpty(),
    larger.UCardinality(),
    larger.UCostPickKey() + 2 * (larger.UCardinalityKeys() + 1) + multiplicity.UCostGet() + larger.UCostRemove() + larger.CostIsEmpty());
  nonnegative_product_monotonic(
    smaller.UCardinality(),
    smaller.UCostPickKey() + 2 * (smaller.UCardinalityKeys() + 1) + 2 * smaller.UCostRemove() + smaller.CostIsEmpty(),
    larger.UCardinality(),
    larger.UCostPickKey() + 2 * (larger.UCardinalityKeys() + 1) + 2 * larger.UCostRemove() + larger.CostIsEmpty());

  assert CostComputeMultiplicitySum(smaller, multiplicity) <=
         CostComputeMultiplicitySum(larger, multiplicity);
  assert CostComputeFitSum(smaller, fitness, multiplicity) <=
         CostComputeFitSum(larger, fitness, multiplicity);
  assert CostComputePrivateSum(smaller, multiplicity) <=
         CostComputePrivateSum(larger, multiplicity);
  assert CostFilterCandidateMap(smaller) <= CostFilterCandidateMap(larger);
  assert CostCheckClassification(smaller, fitness, multiplicity) <=
         CostCheckClassification(larger, fitness, multiplicity);
  assert CostCheckPrivateQuestion(smaller, multiplicity) <=
         CostCheckPrivateQuestion(larger, multiplicity);
  nonnegative_product_monotonic(
    privateQuestions.UCardinality(),
    privateQuestions.CostPick() +
      CostCheckPrivateQuestion(smaller, multiplicity) +
      privateQuestions.UCostRemove() +
      privateQuestions.CostIsEmpty(),
    privateQuestions.UCardinality(),
    privateQuestions.CostPick() +
      CostCheckPrivateQuestion(larger, multiplicity) +
      privateQuestions.UCostRemove() +
      privateQuestions.CostIsEmpty());
}


// Tree-cost arithmetic for recursive proofs, independent of quantified population facts.

lemma cost_tree_combine(
    nodes:nat, trueNodes:nat, falseNodes:nat, nodeCost:nat, branchFactor:nat,
    counterBase:nat, setupCounter:nat, afterTrueCounter:nat, counter:nat)
  requires afterTrueCounter <= setupCounter + branchFactor * trueNodes * nodeCost
  requires nodes == 1 + trueNodes + falseNodes
  requires setupCounter <= counterBase + nodeCost
  requires counter <= afterTrueCounter + branchFactor * falseNodes * nodeCost
  ensures counter <= counterBase + (branchFactor * (nodes - 1) + 1) * nodeCost
{}


lemma cost_branch_combine(nodes:nat, nodeCost:nat, counterBase:nat, setupCounter:nat, counter:nat)
  requires 1 <= nodes
  requires setupCounter <= counterBase + nodeCost
  requires counter <= setupCounter + (2 * nodes - 1) * nodeCost
  ensures counter <= counterBase + 2 * nodes * nodeCost
{}


lemma cost_branch_own_fits(nodes:nat, nodeCost:nat, counterBase:nat, counter:nat)
  requires 1 <= nodes
  requires counter <= counterBase + nodeCost
  ensures counter <= counterBase + 2 * nodes * nodeCost
{}


// Instance node bounds control structure and certificate checking before composing the total budget.

lemma cost_cdpc_structure_bound<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>, questions:Set<Q>, interview:Interview<Q>)
  requires questions.Valid()
  requires interview.NodeCount() <= 2*fitness.Cardinality()*questions.Cardinality()+1
  ensures interview.NodeCount()*CostCheckInterviewFitsNode(questions, interview) <=
    (2*fitness.Cardinality()*questions.USize()+1)*CostCheckInterviewFitsNode(questions, interview)
{
  nonnegative_product_monotonic(fitness.Cardinality(), questions.Cardinality(),
    fitness.Cardinality(), questions.USize());
  assert interview.NodeCount() <= 2*fitness.Cardinality()*questions.USize()+1;
  nonnegative_product_monotonic(interview.NodeCount(), CostCheckInterviewFitsNode(questions, interview),
    2*fitness.Cardinality()*questions.USize()+1,
    CostCheckInterviewFitsNode(questions, interview));
}


lemma cost_cdpc_checking_bound<Q(!new)>(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>, interview:Interview<Q>)
  requires interview.NodeCount() <= 2*fitness.Cardinality()*questions.USize()+1
  ensures CostVerifyCDPCCertificate(fitness, fitness, multiplicity, privateQuestions, interview) <=
    2*(2*fitness.Cardinality()*questions.USize()+1)*
      CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions, interview)
{
  if interview.NodeCount() > 0 {
    nonnegative_product_monotonic(2*interview.NodeCount()-1,
      CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions, interview),
      2*(2*fitness.Cardinality()*questions.USize()+1),
      CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions, interview));
  }
}


// Keep scalar arithmetic separate from the quantified instance properties.
lemma {:isolate_assertions} cost_verify_cdpc_bound<Q(!new)>(
    fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, questions:Set<Q>, interview:Interview<Q>, n:nat)
  requires questions.Init() && fitness.Init() && multiplicity.Init() && privateQuestions.Init()
  requires fitness.Cardinality() <= n && multiplicity.Cardinality() <= n
  requires privateQuestions.Cardinality() <= n
  requires fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  requires questions.Cardinality() <= n
  ensures CostVerifyCDPC(fitness, multiplicity, privateQuestions, questions, interview) <= PolynomialVerifyCDPC(n)
{
  reveal CostVerifyCDPC();
  assert questions.USize() == questions.Cardinality();
  nonnegative_product_monotonic(fitness.Cardinality(), fitness.UCardinalityKeys(), n, n);
  nonnegative_product_monotonic(fitness.Cardinality(), questions.USize(), n, n);
  nonnegative_product_monotonic(multiplicity.Cardinality(), multiplicity.UCardinalityKeys(), n, n);
  var c := n*n+1;
  var d := n+1;
  var sum := c+1+n*(d+2*c+1);
  var filter := 2*c+1+n*(3*d+2*c+1);
  var fit := c+1+n*(d+3*c+1);
  var privateSum := c+1+n*(3*d+2*c+1);
  nonnegative_product_monotonic(fitness.UCardinality(),
    fitness.UCostPickKey()+multiplicity.UCostGet()+
      fitness.UCostRemove()+1, n, d+2*c+1);
  assert CostComputeMultiplicitySum(fitness, multiplicity) <= sum;
  nonnegative_product_monotonic(fitness.UCardinality(),
    fitness.UCostPickKey()+2*(fitness.UCardinalityKeys()+1)+
      2*fitness.UCostRemove()+1, n, 3*d+2*c+1);
  assert CostFilterCandidateMap(fitness) <= filter;
  nonnegative_product_monotonic(fitness.UCardinality(),
    fitness.UCostPickKey()+fitness.UCostGet()+
      multiplicity.UCostGet()+fitness.UCostRemove()+1,
    n, d+3*c+1);
  assert CostComputeFitSum(fitness, fitness, multiplicity) <= fit;
  nonnegative_product_monotonic(fitness.UCardinality(),
    fitness.UCostPickKey()+2*(fitness.UCardinalityKeys()+1)+
      multiplicity.UCostGet()+fitness.UCostRemove()+1,
    n, 3*d+2*c+1);
  assert CostComputePrivateSum(fitness, multiplicity) <= privateSum;
  nonnegative_product_monotonic(privateQuestions.UCardinality(),
    CostComputePrivateSum(fitness, multiplicity)+privateQuestions.USize()+4,
    n, privateSum+n+4);
  assert CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions, interview) <=
    PolynomialVerifyCDPCNode(n);
  multiplication_associative(2, fitness.Cardinality(), questions.USize());
  multiplication_associative(2, n, n);
  assert 2*fitness.Cardinality()*questions.USize()+1 <= 2*n*n+1;
  nonnegative_product_monotonic(2*fitness.Cardinality()*questions.USize()+1,
    CostCheckInterviewFitsNode(questions, interview),
    2*n*n+1, 2*n+6);
  nonnegative_product_monotonic(2*(2*fitness.Cardinality()*questions.USize()+1),
    CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions, interview),
    2*(2*n*n+1), PolynomialVerifyCDPCNode(n));
}
