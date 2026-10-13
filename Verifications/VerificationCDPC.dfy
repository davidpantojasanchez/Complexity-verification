include "VerificationCDPC_aux.dfy"
include "../Problems/CDPCLemmas.dfy"


method VerifyCDPC<Q(!new)>(
    questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, interview:Interview<Q>)
    returns (accepted:bool, ghost counter:nat)
  // Types in
  requires CDPCValidInstance(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires Init_Set(questions) && Init_Map_Map_T(fitness) && Init_Map_Map_T(multiplicity) && Init_Set(privateQuestions)
  // Invariant out
  ensures accepted == CDPCCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper, interview.Model())
  ensures accepted ==> CDPC(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  // Counter
  ensures counter <= PolynomialVerifyCDPC(fitness.Cardinality() + questions.Cardinality() + 1)
{
  SubsetCardinalityBound(privateQuestions.Model(), questions.Model());
  fitness.UCardinalityKeysBound(questions.Cardinality());
  multiplicity.UCardinalityKeysBound(questions.Cardinality());
  CostVerifyCDPCToPolynomial(fitness, multiplicity, privateQuestions, questions, fitness.Cardinality() + questions.Cardinality() + 1);
  var population, questionCount, size:nat;
  population, counter := fitness.Count(0);
  questionCount, counter := questions.Count(counter);
  var limit := 2*population*questionCount+1;
  size, counter := CountInterviewBounded(interview, limit, counter);
  assert {:split_here} counter <= fitness.CostCount() + questions.CostCount() + (limit+1)*CostCountInterviewNode();
  if size > limit {
    CDPCOversizedNotCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      privateLower, privateUpper, fitnessLower, fitnessUpper, interview.Model());
    NatMultiplicationMonotonic(limit, 0, CostCheckInterviewFitsNode(questions));
    NatMultiplicationMonotonic(2*limit, 0, CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions));
    return false, counter;
  }
  assert {:split_here} interview.NodeCount() <= limit;
  accepted, counter := CheckInterviewFits(questions, questions, interview, counter);
  CostCDPCStructureBound(fitness, questions, interview);
  if !accepted { return false, counter; }
  CostCDPCCheckingBound(questions, fitness, multiplicity, privateQuestions, interview);
  accepted, counter := VerifyCDPCCore(fitness, fitness, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, interview, counter);
}

// Stop counting as soon as the tree exceeds the budget.
method CountInterviewBounded<Q(!new)>(interview:Interview<Q>, limit:nat, ghost counter_in:nat)
    returns (size:nat, ghost counter:nat)
  // Termination in
  decreases limit
  // Invariant out
  ensures size == if interview.NodeCount() <= limit then interview.NodeCount() else limit+1
  // Counter
  ensures counter <= counter_in + size*CostCountInterviewNode()
{
  reveal InterviewNodes();
  if limit == 0 { return 1, counter_in; }
  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd { return 1, counter; }
  var left:Interview<Q>;
  left, counter := interview.Branch(true, counter);
  var leftSize:nat;
  leftSize, counter := CountInterviewBounded(left, limit-1, counter);
  if leftSize > limit-1 { return limit+1, counter; }
  var right:Interview<Q>;
  right, counter := interview.Branch(false, counter);
  var rightSize:nat;
  rightSize, counter := CountInterviewBounded(right, limit-1-leftSize, counter);
  return 1+leftSize+rightSize, counter;
}

// Check question availability on every path after the bounded size scan.
method CheckInterviewFits<Q(!new)>(
    questions:Set<Q>, remaining:Set<Q>, interview:Interview<Q>,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Termination in
  decreases interview.NodeCount()
  // Types in
  requires questions.Valid()
  requires remaining.UniverseWithin(questions)
  // Invariant out
  ensures accepted == InterviewFits(interview.Model(), remaining.Model())
  // Counter
  ensures counter <= counter_in + interview.NodeCount()*CostCheckInterviewFitsNode(questions)
{
  remaining.UniverseWithinBound(questions);
  reveal InterviewFits(), InterviewNodes();
  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd { return true, counter; }

  var question:Q;
  question, counter := interview.Question(counter);
  var available:bool;
  available, counter := remaining.Contains(question, counter);
  if !available { return false, counter; }

  var childRemaining:Set<Q>;
  childRemaining, counter := remaining.Remove(question, counter);
  var trueBranch:Interview<Q>;
  trueBranch, counter := interview.Branch(true, counter);
  var falseBranch:Interview<Q>;
  falseBranch, counter := interview.Branch(false, counter);
  ghost var setupCounter := counter;

  var trueAccepted:bool;
  trueAccepted, counter := CheckInterviewFits(questions, childRemaining, trueBranch, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckInterviewFits(questions, childRemaining, falseBranch, counter);
  accepted := trueAccepted && falseAccepted;
  CostTreeCombine(interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    CostCheckInterviewFitsNode(questions), 1, counter_in, setupCounter, afterTrueCounter, counter);
}

// Recursive certificate validation

// Leaves must classify the remaining population while preserving privacy.
// Internal nodes partition that population and validate both answer branches.
method VerifyCDPCCore<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    interview:Interview<Q>,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Termination in
  requires candidates.Keys() != {}
  decreases interview.NodeCount(), 0
  // Types in
  requires rootCandidates.Valid()
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires Init_Set(privateQuestions)
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires candidates.UniverseWithin(rootCandidates)
  // Invariant out
  ensures accepted == CDPCInterviewSemantics(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates.Keys(), interview.Model())
  // Counter
  ensures counter <= counter_in + CostVerifyCDPCCertificate(
    rootCandidates, fitness, multiplicity, privateQuestions, interview)
{
  reveal interview.NodeCount();
  reveal InterviewNodes();
  CostCDPCCandidateMonotonic(candidates, rootCandidates, fitness, multiplicity, privateQuestions);

  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd {
    var classificationAccepted:bool;
    classificationAccepted, counter := CheckClassification(candidates, fitness, multiplicity, fitnessLower, fitnessUpper, counter);
    var privacyAccepted:bool;
    privacyAccepted, counter := CheckPrivateSafe(candidates, privateQuestions, multiplicity, privateLower, privateUpper, counter);
    reveal CDPCInterviewSemantics();
    assert counter <= counter_in + CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions);
    return classificationAccepted && privacyAccepted, counter;
  }

  var question:Q;
  question, counter := interview.Question(counter);
  var trueCandidates:Map_Map_T<Q, bool, bool>;
  trueCandidates, counter := FilterCandidateMap(candidates, question, true, counter);
  var falseCandidates:Map_Map_T<Q, bool, bool>;
  falseCandidates, counter := FilterCandidateMap(candidates, question, false, counter);
  var trueBranch:Interview<Q>;
  trueBranch, counter := interview.Branch(true, counter);
  var falseBranch:Interview<Q>;
  falseBranch, counter := interview.Branch(false, counter);

  trueCandidates.UniverseWithinTransitive(candidates, rootCandidates);
  falseCandidates.UniverseWithinTransitive(candidates, rootCandidates);
  assert counter <= counter_in + CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions);

  ghost var setupCounter := counter;
  var trueAccepted:bool;
  trueAccepted, counter := CheckCDPCBranch(
    rootCandidates, trueCandidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, trueBranch, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckCDPCBranch(
    rootCandidates, falseCandidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, falseBranch, counter);
  accepted := trueAccepted && falseAccepted;
  reveal CDPCInterviewSemantics();

  reveal trueBranch.NodeCount();
  reveal falseBranch.NodeCount();
  CostTreeCombine(
    interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions), 2,
    counter_in, setupCounter, afterTrueCounter, counter);
}

// An impossible answer must lead to End
// Otherwise privacy is checked before continuing the interview, including when the next node is already a leaf.
method {:isolate_assertions} CheckCDPCBranch<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    interview:Interview<Q>,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Termination in
  decreases interview.NodeCount(), 1
  // Types in
  requires rootCandidates.Valid()
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires Init_Set(privateQuestions)
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires candidates.UniverseWithin(rootCandidates)
  // Invariant out
  ensures accepted == CDPCBranch(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates.Keys(), interview.Model())
  // Counter
  ensures counter <= counter_in + CostCheckCDPCBranch(
    rootCandidates, fitness, multiplicity, privateQuestions, interview)
{
  reveal interview.NodeCount();
  reveal InterviewNodes();
  CostCDPCCandidateMonotonic(candidates, rootCandidates, fitness, multiplicity, privateQuestions);

  var empty:bool;
  empty, counter := candidates.IsEmpty(counter_in);
  if empty {
    accepted, counter := interview.IsEnd(counter);
    reveal CDPCBranch();
    CostBranchOwnFits(interview.NodeCount(),
      CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions),
      counter_in, counter);
    return accepted, counter;
  }

  var privacyAccepted:bool;
  privacyAccepted, counter := CheckPrivateSafe(
    candidates, privateQuestions, multiplicity,
    privateLower, privateUpper, counter);
  ghost var setupCounter := counter;
  if !privacyAccepted {
    reveal CDPCBranch();
    CostBranchOwnFits(interview.NodeCount(),
      CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions),
      counter_in, counter);
    return false, counter;
  }

  accepted, counter := VerifyCDPCCore(
    rootCandidates, candidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, interview, counter);
  reveal CDPCBranch();
  CostBranchCombine(interview.NodeCount(),
    CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions),
    counter_in, setupCounter, counter);
}

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

  ClassificationFromSums(
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
  requires Init_Set(privateQuestions)
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
  LinearLoopBudgetZero(baseCost, stepCost);
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
    remaining.UniverseWithinBound(privateQuestions);
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
    LinearLoopBudgetStep(baseCost, stepCost, privateQuestions.Cardinality() - previousRemaining.Cardinality());

    assert privateQuestions.Model() - remaining.Model() ==
      (privateQuestions.Model() - previousRemaining.Model()) + {question};
  }
  SubtractionIdentity(privateQuestions.Model(), remaining.Model());
  PrivateSafeFromTotal(
    candidates.Keys(), multiplicity.Model(), privateQuestions.Model(),
    totalSum, privateLower, privateUpper);
  LinearLoopBudgetBound(
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

  PrivateQuestionFromSum(
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
    CostFilterCandidates(candidates)
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
  LinearLoopBudgetZero(baseCost, stepCost);
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
    LinearLoopBudgetStep(baseCost, stepCost, candidates.Cardinality() - remaining.Cardinality());
    remaining, filtered, empty, counter :=
      FilterCandidateMapLoop(candidates, remaining, filtered, question, answer, counter);
  }
  filtered.UniverseWithinBound(candidates);
  LinearLoopBudgetBound(
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
  remaining_in.UniverseWithinBound(candidates);
  filtered_in.UniverseWithinBound(candidates);
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
  MultiplicitySumEmpty(multiplicity.Model());
  ghost var baseCost :=
    candidates.UCostCopy() + candidates.CostIsEmpty();
  ghost var stepCost :=
    candidates.UCostPickKey() +
    multiplicity.UCostGet() +
    candidates.UCostRemove() +
    candidates.CostIsEmpty();
  LinearLoopBudgetZero(baseCost, stepCost);
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
    remaining.UniverseWithinBound(candidates);
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
    LinearLoopBudgetStep(baseCost, stepCost, candidates.Cardinality() - previousRemaining.Cardinality());

    MultiplicitySumProgress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), multiplicity.Model(), previousSum, sum);
  }
  assert {:split_here} true;
  SubtractionIdentity(candidates.Keys(), remaining.Keys());
  LinearLoopBudgetBound(
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
  MultiplicitySumEmpty(multiplicity.Model());
  ghost var baseCost :=
    candidates.UCostCopy() + candidates.CostIsEmpty();
  ghost var stepCost :=
    candidates.UCostPickKey() +
    fitness.UCostGet() +
    multiplicity.UCostGet() +
    candidates.UCostRemove() +
    candidates.CostIsEmpty();
  LinearLoopBudgetZero(baseCost, stepCost);
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
    remaining.UniverseWithinBound(candidates);
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
    LinearLoopBudgetStep(baseCost, stepCost, candidates.Cardinality() - previousRemaining.Cardinality());

    FitSumProgress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), fitness.Model(), multiplicity.Model(),
      previousSum, sum, isFit);
  }
  assert {:split_here} true;
  SubtractionIdentity(candidates.Keys(), remaining.Keys());
  FitSumDefinition(
    candidates.Keys(), fitness.Model(), multiplicity.Model(), sum,
    set candidate | candidate in candidates.Keys() &&
                    candidate in fitness.Model() &&
                    fitness.Model()[candidate] :: candidate);
  LinearLoopBudgetBound(
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
  MultiplicitySumEmpty(multiplicity.Model());
  ghost var baseCost :=
    candidates.UCostCopy() + candidates.CostIsEmpty();
  ghost var stepCost :=
    candidates.UCostPickKey() +
    2 * (candidates.UCardinalityKeys() + 1) +
    multiplicity.UCostGet() +
    candidates.UCostRemove() +
    candidates.CostIsEmpty();
  LinearLoopBudgetZero(baseCost, stepCost);
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
    remaining.UniverseWithinBound(candidates);
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
    LinearLoopBudgetStep(baseCost, stepCost, candidates.Cardinality() - previousRemaining.Cardinality());

    PrivateSumProgress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), question, multiplicity.Model(),
      previousSum, sum, selected);
  }
  SubtractionIdentity(candidates.Keys(), remaining.Keys());
  PrivateSumDefinition(
    candidates.Keys(), question, multiplicity.Model(), sum,
    set candidate | candidate in candidates.Keys() &&
                    question in candidate && candidate[question] :: candidate);
  LinearLoopBudgetBound(
    baseCost, stepCost,
    candidates.Cardinality(), candidates.UCardinality());
}
