include "../Polynomial/PolynomialCDPC.dfy"
include "../Collections/ConcreteInterview.dfy"
include "VerificationCDPC_aux.dfy"

// Every positive instance has an initialized, correct certificate of linear size.
ghost method CDPCHasShortCertificate<Q(!new)>(
    instance:CDPCInstance<Q>) returns (certificate:Interview<Q>)
  requires instance.questions.Init() && instance.fitness.Init() && instance.multiplicity.Init() && instance.privateQuestions.Init()
  requires CDPCValidInstance(instance.Model())
  requires CDPC(instance.Model())
  ensures fresh(certificate)
  ensures CDPCCertificate(instance.Model(), certificate.Model())
  ensures forall weight:Q -> nat ::
    certificate.Size(weight) <= BudgetCDPCCertificateSize(instance.Size(weight))
{
  var questions, fitness := instance.questions, instance.fitness;
  var tree :| CDPCCertificate(instance.Model(), tree);
  certificate := new ConcreteInterview<Q>(tree);
  cdpc_certificate_node_count_bound(instance.Model(), tree);
  var n := fitness.Cardinality() + questions.Cardinality() + 1;
  nonnegative_product_monotonic(fitness.Cardinality(), questions.Cardinality(), n, n);
  multiplication_associative(2, fitness.Cardinality(), questions.Cardinality());
  multiplication_associative(2, n, n);
  assert 2*fitness.Cardinality()*questions.Cardinality()+1 <= 2*n*n+1;
  forall weight:Q -> nat
    ensures certificate.Size(weight) <= BudgetCDPCCertificateSize(instance.Size(weight))
  {
    cdpc_certificate_instance_size_bound(instance, certificate, weight);
  }
}

// Exact rational verification with one additive weighted counter.
method VerifyCDPC<Q(!new)>(
    instance:CDPCInstance<Q>, interview:Interview<Q>, ghost weight:Q -> nat)
    returns (accepted:bool, ghost counter:nat)
  requires instance.questions.Init() && instance.fitness.Init() && instance.multiplicity.Init() && instance.privateQuestions.Init()
  requires CDPCValidInstance(instance.Model())
  ensures accepted == CDPCCertificate(instance.Model(), interview.Model())
  ensures accepted ==> CDPC(instance.Model())
  ensures 0 < counter <= BudgetVerifyCDPC(CDPCInputSize(instance, interview, weight))
{
  var questions, fitness, multiplicity, privateQuestions, thresholds :=
    instance.questions, instance.fitness, instance.multiplicity, instance.privateQuestions, instance.thresholds;
  budget_verify_cdpc_input_bound(instance, interview, weight);
  ghost var maximum := MultiplicityMaximum(multiplicity.Model());
  multiplicity_maximum_bound(multiplicity.Model());
  ghost var n := CDPCInputSizeBound(instance, interview, weight);
  ghost var context := BitSetCost(weight, n);
  ghost var mapContext := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  var population, questionCount, countedNodes:nat;
  population, counter := fitness.Count(0, mapContext);
  questionCount, counter := questions.Count(counter, context);
  ghost var beforeScan := counter;
  assert population <= n && questionCount <= n && beforeScan <= 2*primitiveBudget;
  assert {:split_here} true;
  var doubled, product, limit:nat;
  doubled, counter := MultiplyNat(2, population, counter);
  product, counter := MultiplyNat(doubled, questionCount, counter);
  limit, counter := AddNat(product, 1, counter);
  ghost var beforeCount := counter;
  countedNodes, counter := CountInterviewBounded(interview, limit, limit+1, n, weight, counter);
  ghost var afterCount := counter;
  nat_bits_monotonic(countedNodes, limit+1);
  var fits:bool;
  fits, counter := LessEqualNat(countedNodes, limit, counter);
  cdpc_admissibility_counter_bound(population, questionCount, n, countedNodes, beforeScan, beforeCount, afterCount, counter);
  assert {:split_here} true;
  if !fits {
    assert counter <= BudgetVerifyCDPCPhase(n);
    cdpc_over_limit_not_certificate(instance.Model(), interview.Model());
    return false, counter;
  }
  accepted, counter := CheckInterviewFits(questions, questions, interview, n, weight, counter);
  nonnegative_product_monotonic(interview.NodeCount(), 6*primitiveBudget, 2*n*n+1, 6*primitiveBudget);
  if !accepted {
    assert counter <= BudgetVerifyCDPCPhase(n);
    return false, counter;
  }
  accepted, counter := VerifyCDPCCore(fitness, fitness, fitness, multiplicity, privateQuestions,
    thresholds, interview, maximum, n, weight, counter);
  budget_cdpc_tree_bound(interview.NodeCount(), 2*n*n+1, n);
  assert counter <= BudgetVerifyCDPCPhase(n);
}

// Stop counting as soon as the tree exceeds the budget.
method CountInterviewBounded<Q(!new)>(
    interview:Interview<Q>, limit:nat, ghost bound:nat, ghost n:nat,
    ghost weight:Q -> nat, ghost counter_in:nat)
    returns (countedNodes:nat, ghost counter:nat)
  // Progress in
  decreases limit
  // State in
  requires limit < bound
  requires interview.SizeBound(weight) <= n
  // State out
  ensures countedNodes == if interview.NodeCount() <= limit then interview.NodeCount() else limit+1
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + countedNodes*BudgetCountInterviewNode(bound, n)
{
  reveal InterviewNodes();
  ghost var context := BitSetCost(weight, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  ghost var arithmetic := 1+2*NatBits(bound);
  ghost var nodeBudget := BudgetCountInterviewNode(bound, n);
  nat_bits_monotonic(0, bound);
  nat_bits_monotonic(1, bound);
  nat_bits_monotonic(limit, bound);
  // The unit charge covers construction of a returned literal.
  counter := counter_in+1;
  var zero:bool;
  zero, counter := LessEqualNat(limit, 0, counter);
  if zero { return 1, counter; }
  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter, context);
  if isEnd { return 1, counter; }
  var remaining:nat;
  remaining, counter := SubtractNat(limit, 1, counter);
  var left:Interview<Q>;
  left, counter := interview.Branch(true, counter, context);
  assert counter <= counter_in+1+2*arithmetic+2*primitiveBudget;
  var leftCount:nat;
  leftCount, counter := CountInterviewBounded(left, remaining, bound, n, weight, counter);
  ghost var afterLeft := counter;
  nat_bits_monotonic(leftCount, bound);
  var fits:bool;
  fits, counter := LessEqualNat(leftCount, remaining, counter);
  if !fits {
    countedNodes, counter := AddNat(limit, 1, counter);
    assert countedNodes == 1+leftCount;
    assert counter <= counter_in+nodeBudget+leftCount*nodeBudget;
    tree_budget_combine(countedNodes, leftCount, 0, nodeBudget, 1,
      counter_in, counter_in+nodeBudget, counter, counter);
    return countedNodes, counter;
  }
  var right:Interview<Q>;
  right, counter := interview.Branch(false, counter, context);
  var rightLimit:nat;
  rightLimit, counter := SubtractNat(remaining, leftCount, counter);
  assert counter <= afterLeft+2*arithmetic+primitiveBudget;
  var rightCount:nat;
  rightCount, counter := CountInterviewBounded(right, rightLimit, bound, n, weight, counter);
  ghost var afterRight := counter;
  nat_bits_monotonic(rightCount, bound);
  countedNodes, counter := AddNat(1, leftCount, counter);
  nat_bits_monotonic(countedNodes, bound);
  countedNodes, counter := AddNat(countedNodes, rightCount, counter);
  assert counter <= afterRight+2*arithmetic;
  assert counter <= counter_in+nodeBudget+leftCount*nodeBudget+rightCount*nodeBudget;
  tree_budget_combine(countedNodes, leftCount, rightCount, nodeBudget, 1,
    counter_in, counter_in+nodeBudget, counter_in+nodeBudget+leftCount*nodeBudget, counter);
}

// Check question availability on every path after the bounded node count.
method CheckInterviewFits<Q(!new)>(
    questions:Set<Q>, remaining:Set<Q>, interview:Interview<Q>,
    ghost n:nat, ghost weight:Q -> nat, ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Progress in
  decreases interview.NodeCount()
  // Representation in
  requires questions.Valid()
  requires questions.SizeBound(weight) <= n && interview.SizeBound(weight) <= n
  requires remaining.UniverseWithin(questions)
  // State out
  ensures accepted == InterviewFits(interview.Model(), remaining.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + interview.NodeCount()*(6*BudgetPrimitiveStep(n))
{
  ghost var context := BitSetCost(weight, n);
  remaining.universe_within_bound(questions, context);
  reveal InterviewFits(), InterviewNodes();
  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in, context);
  if isEnd {
    assert interview.NodeCount() == 1;
    return true, counter;
  }

  var question:Q;
  question, counter := interview.Question(counter, context);
  var available:bool;
  available, counter := remaining.Contains(question, counter, context);
  if !available {
    nat_multiplication_monotonic(6*BudgetPrimitiveStep(n), 1, interview.NodeCount());
    return false, counter;
  }

  var childRemaining:Set<Q>;
  childRemaining, counter := remaining.Remove(question, counter, context);
  var trueBranch:Interview<Q>;
  trueBranch, counter := interview.Branch(true, counter, context);
  var falseBranch:Interview<Q>;
  falseBranch, counter := interview.Branch(false, counter, context);
  ghost var setupCounter := counter;

  var trueAccepted:bool;
  trueAccepted, counter := CheckInterviewFits(questions, childRemaining, trueBranch, n, weight, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckInterviewFits(questions, childRemaining, falseBranch, n, weight, counter);
  accepted := trueAccepted && falseAccepted;
  tree_budget_combine(interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(), (6*BudgetPrimitiveStep(n)), 1, counter_in, setupCounter, afterTrueCounter, counter);
}

// Leaves must classify the remaining population while preserving privacy.
// Internal nodes partition that population and validate both answer branches.
method {:isolate_assertions} VerifyCDPCCore<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    thresholds:CDPCThresholds<Rational>,
    interview:Interview<Q>,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Progress in
  requires candidates.Keys() != {}
  decreases interview.NodeCount(), 0
  // Representation in
  requires rootCandidates.Valid()
  requires rootCandidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires fitness.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires privateQuestions.SizeBound(weight) <= n && interview.SizeBound(weight) <= n
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires privateQuestions.Init()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires candidates.UniverseWithin(rootCandidates)
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() :: multiplicity.Model()[candidate] <= maximum
  requires RationalBits(thresholds.privateLower) <= n && RationalBits(thresholds.privateUpper) <= n
  requires RationalBits(thresholds.fitnessLower) <= n && RationalBits(thresholds.fitnessUpper) <= n
  // State out
  ensures accepted == CDPCInterviewSemantics(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    CDPCThresholdsModel(thresholds),
    candidates.Keys(), interview.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCTree(interview.NodeCount(), n)
{
  ghost var mapContext := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var context := BitSetCost(weight, n);
  candidates.universe_within_bound(rootCandidates, mapContext);
  reveal interview.NodeCount();
  reveal InterviewNodes();

  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in, context);
  if isEnd {
    assert interview.NodeCount() == 1;
    var classificationAccepted:bool;
    classificationAccepted, counter := CheckClassification(
      candidates, fitness, multiplicity, thresholds.fitnessLower, thresholds.fitnessUpper, maximum, n, weight, counter);
    var privacyAccepted:bool;
    privacyAccepted, counter := CheckPrivateSafe(
      candidates, privateQuestions, multiplicity, thresholds.privateLower, thresholds.privateUpper, maximum, n, weight, counter);
    assert counter <= counter_in + BudgetCDPCNode(n);
    tree_budget_combine(interview.NodeCount(), 0, 0, BudgetCDPCNode(n), 2, counter_in, counter, counter, counter);
    assert CDPCInterviewSemantics(
      fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      CDPCThresholdsModel(thresholds),
      candidates.Keys(), interview.Model()) == (classificationAccepted && privacyAccepted) by {
      reveal CDPCInterviewSemantics();
    }
    return classificationAccepted && privacyAccepted, counter;
  }

  var question:Q;
  question, counter := interview.Question(counter, context);
  var trueCandidates:Map_Map_T<Q, bool, bool>;
  trueCandidates, counter := FilterCandidateMap(candidates, question, true, n, weight, counter);
  var falseCandidates:Map_Map_T<Q, bool, bool>;
  falseCandidates, counter := FilterCandidateMap(candidates, question, false, n, weight, counter);
  var trueBranch:Interview<Q>;
  trueBranch, counter := interview.Branch(true, counter, context);
  var falseBranch:Interview<Q>;
  falseBranch, counter := interview.Branch(false, counter, context);

  trueCandidates.universe_within_transitive(candidates, rootCandidates);
  falseCandidates.universe_within_transitive(candidates, rootCandidates);
  assert counter <= counter_in + BudgetCDPCNode(n);

  ghost var setupCounter := counter;
  var trueAccepted:bool;
  trueAccepted, counter := CheckCDPCBranch(
    rootCandidates, trueCandidates, fitness, multiplicity,
    privateQuestions, thresholds, trueBranch, maximum, n, weight, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckCDPCBranch(
    rootCandidates, falseCandidates, fitness, multiplicity,
    privateQuestions, thresholds, falseBranch, maximum, n, weight, counter);
  accepted := trueAccepted && falseAccepted;

  reveal trueBranch.NodeCount();
  reveal falseBranch.NodeCount();
  assert interview.NodeCount() == 1+trueBranch.NodeCount()+falseBranch.NodeCount();
  tree_budget_combine(
    interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    BudgetCDPCNode(n), 2,
    counter_in, setupCounter, afterTrueCounter, counter);
  assert CDPCInterviewSemantics(
      fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      CDPCThresholdsModel(thresholds),
      candidates.Keys(), interview.Model()) == accepted by {
    reveal CDPCInterviewSemantics();
  }
}

// An impossible answer must lead to End. Otherwise, check privacy before
// continuing, even if the next node is a leaf.
method CheckCDPCBranch<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    thresholds:CDPCThresholds<Rational>,
    interview:Interview<Q>,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Progress in
  decreases interview.NodeCount(), 1
  // Representation in
  requires rootCandidates.Valid()
  requires rootCandidates.SizeBound(weight, BoolBits, BoolBits) <= n
  requires fitness.SizeBound(weight, BoolBits, BoolBits) <= n
  requires multiplicity.SizeBound(weight, BoolBits, NatBits) <= n
  requires privateQuestions.SizeBound(weight) <= n && interview.SizeBound(weight) <= n
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires privateQuestions.Init()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires candidates.UniverseWithin(rootCandidates)
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() :: multiplicity.Model()[candidate] <= maximum
  requires RationalBits(thresholds.privateLower) <= n && RationalBits(thresholds.privateUpper) <= n
  requires RationalBits(thresholds.fitnessLower) <= n && RationalBits(thresholds.fitnessUpper) <= n
  // State out
  ensures accepted == CDPCBranch(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    CDPCThresholdsModel(thresholds),
    candidates.Keys(), interview.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + 2*interview.NodeCount()*BudgetCDPCNode(n)
{
  ghost var mapContext := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var context := BitSetCost(weight, n);
  candidates.universe_within_bound(rootCandidates, mapContext);
  reveal interview.NodeCount();
  reveal InterviewNodes();
  assert BudgetCDPCNode(n) + BudgetCDPCTree(interview.NodeCount(), n) ==
    2*interview.NodeCount()*BudgetCDPCNode(n);

  var empty:bool;
  empty, counter := candidates.IsEmpty(counter_in, mapContext);
  if empty {
    accepted, counter := interview.IsEnd(counter, context);
    reveal CDPCBranch();
    return accepted, counter;
  }

  var privacyAccepted:bool;
  privacyAccepted, counter := CheckPrivateSafe(
    candidates, privateQuestions, multiplicity,
    thresholds.privateLower, thresholds.privateUpper, maximum, n, weight, counter);
  assert counter <= counter_in + BudgetCDPCNode(n);
  if !privacyAccepted {
    reveal CDPCBranch();
    return false, counter;
  }

  accepted, counter := VerifyCDPCCore(
    rootCandidates, candidates, fitness, multiplicity,
    privateQuestions, thresholds, interview, maximum, n, weight, counter);
  reveal CDPCBranch();
}
