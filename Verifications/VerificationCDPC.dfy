include "../Polynomial/PolynomialCDPC.dfy"
include "../Collections/ConcreteInterview.dfy"
include "VerificationCDPC_aux.dfy"

// Positive instances also have a concrete certificate in the verifier's representation.
ghost method CDPCHasShortCertificate<Q(!new)>(
    questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, privateLower:Rational, privateUpper:Rational,
    fitnessLower:Rational, fitnessUpper:Rational) returns (certificate:Interview<Q>)
  requires questions.Init() && fitness.Init() && multiplicity.Init() && privateQuestions.Init()
  requires CDPCValidInstance(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), privateLower.Model(),
      privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model())
  requires CDPC(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), privateLower.Model(), privateUpper.Model(),
      fitnessLower.Model(), fitnessUpper.Model())
  ensures fresh(certificate)
  ensures CDPCCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), privateLower.Model(),
      privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model(), certificate.Model())
  ensures forall weight:Q -> nat ::
    (CDPCCertificateSize(certificate.Model(), weight) <=
    BoundCDPCCertificateSize(CDPCInstanceSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), (privateLower,
        privateUpper, fitnessLower, fitnessUpper), weight)))
{
  var tree :| CDPCCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model(), tree);
  certificate := new ConcreteInterview<Q>(tree);
  cdpc_certificate_volume_bound(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model(), tree);
  var n := fitness.Cardinality() + questions.Cardinality() + 1;
  nonnegative_product_monotonic(fitness.Cardinality(), questions.Cardinality(), n, n);
  multiplication_associative(2, fitness.Cardinality(), questions.Cardinality());
  multiplication_associative(2, n, n);
  assert 2*fitness.Cardinality()*questions.Cardinality()+1 <= 2*n*n+1;
  forall weight:Q -> nat
    ensures CDPCCertificateSize(certificate.Model(), weight) <= BoundCDPCCertificateSize(CDPCInstanceSize(
      questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      (privateLower, privateUpper, fitnessLower, fitnessUpper), weight))
  {
    cdpc_certificate_instance_size_bound(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      (privateLower, privateUpper, fitnessLower, fitnessUpper), certificate.Model(), weight);
  }
}

// Exact rational verification with one additive weighted counter.
method {:isolate_assertions} VerifyCDPC<Q(!new)>(
    questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, privateLower:Rational, privateUpper:Rational,
    fitnessLower:Rational, fitnessUpper:Rational, interview:Interview<Q>, ghost weight:Q -> nat)
    returns (accepted:bool, ghost counter:nat)
  requires questions.Init() && fitness.Init() && multiplicity.Init() && privateQuestions.Init()
  requires CDPCValidInstance(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model())
  ensures accepted == CDPCCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model(), interview.Model())
  ensures accepted ==> CDPC(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model())
  ensures 0 < counter <= BudgetVerifyCDPC(CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    (privateLower, privateUpper, fitnessLower, fitnessUpper), interview.Model(), weight))
{
  budget_verify_cdpc_input_bound(questions, fitness, multiplicity, privateQuestions, (privateLower, privateUpper, fitnessLower, fitnessUpper), interview, weight);
  ghost var maximum := MultiplicityMaximum(multiplicity.Model());
  multiplicity_maximum_bound(multiplicity.Model());
  ghost var n := CDPCOperandSizeBound(questions, fitness, multiplicity, privateQuestions, (privateLower, privateUpper, fitnessLower, fitnessUpper), interview, weight);
  ghost var context := BitSetCost(weight, n);
  ghost var mapContext := BitNestedMapCost(weight, BoolBits, BoolBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  var population, questionCount, volume:nat;
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
  volume, counter := CountInterviewBounded(interview, limit, limit+1, n, weight, counter);
  ghost var afterCount := counter;
  nat_bits_monotonic(volume, limit+1);
  var fits:bool;
  fits, counter := LessEqualNat(volume, limit, counter);
  cdpc_admissibility_counter_bound(population, questionCount, n, volume, beforeScan, beforeCount, afterCount, counter);
  assert {:split_here} true;
  if !fits {
    assert counter <= BudgetVerifyCDPCPhase(n);
    cdpc_over_limit_not_certificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      privateLower.Model(), privateUpper.Model(), fitnessLower.Model(), fitnessUpper.Model(), interview.Model());
    return false, counter;
  }
  accepted, counter := CheckInterviewFits(questions, questions, interview, n, weight, counter);
  nonnegative_product_monotonic(interview.NodeCount(), 6*primitiveBudget, 2*n*n+1, 6*primitiveBudget);
  if !accepted {
    assert counter <= BudgetVerifyCDPCPhase(n);
    return false, counter;
  }
  accepted, counter := VerifyCDPCCore(fitness, fitness, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, interview, maximum, n, weight, counter);
  budget_cdpc_tree_bound(interview.NodeCount(), 2*n*n+1, n);
  assert counter <= BudgetVerifyCDPCPhase(n);
}

// Stop counting as soon as the tree exceeds the budget.
method CountInterviewBounded<Q(!new)>(
    interview:Interview<Q>, limit:nat, ghost bound:nat, ghost n:nat,
    ghost weight:Q -> nat, ghost counter_in:nat)
    returns (volume:nat, ghost counter:nat)
  // Progress in
  decreases limit
  // State in
  requires limit < bound
  requires interview.Size(weight) <= n
  // State out
  ensures volume == if interview.NodeCount() <= limit then interview.NodeCount() else limit+1
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + volume*BudgetCountInterviewNode(bound, n)
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
  var leftVolume:nat;
  leftVolume, counter := CountInterviewBounded(left, remaining, bound, n, weight, counter);
  ghost var afterLeft := counter;
  nat_bits_monotonic(leftVolume, bound);
  var fits:bool;
  fits, counter := LessEqualNat(leftVolume, remaining, counter);
  if !fits {
    volume, counter := AddNat(limit, 1, counter);
    assert volume == 1+leftVolume;
    assert counter <= counter_in+nodeBudget+leftVolume*nodeBudget;
    tree_budget_combine(volume, leftVolume, 0, nodeBudget, 1,
      counter_in, counter_in+nodeBudget, counter, counter);
    return volume, counter;
  }
  var right:Interview<Q>;
  right, counter := interview.Branch(false, counter, context);
  var rightLimit:nat;
  rightLimit, counter := SubtractNat(remaining, leftVolume, counter);
  assert counter <= afterLeft+2*arithmetic+primitiveBudget;
  var rightVolume:nat;
  rightVolume, counter := CountInterviewBounded(right, rightLimit, bound, n, weight, counter);
  ghost var afterRight := counter;
  nat_bits_monotonic(rightVolume, bound);
  volume, counter := AddNat(1, leftVolume, counter);
  nat_bits_monotonic(volume, bound);
  volume, counter := AddNat(volume, rightVolume, counter);
  assert counter <= afterRight+2*arithmetic;
  assert counter <= counter_in+nodeBudget+leftVolume*nodeBudget+rightVolume*nodeBudget;
  tree_budget_combine(volume, leftVolume, rightVolume, nodeBudget, 1,
    counter_in, counter_in+nodeBudget, counter_in+nodeBudget+leftVolume*nodeBudget, counter);
}

// Check question availability on every path after the bounded volume scan.
method {:isolate_assertions} CheckInterviewFits<Q(!new)>(
    questions:Set<Q>, remaining:Set<Q>, interview:Interview<Q>,
    ghost n:nat, ghost weight:Q -> nat, ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Progress in
  decreases interview.NodeCount()
  // Representation in
  requires questions.Valid()
  requires questions.Size(weight) <= n && interview.Size(weight) <= n
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
    privateLower:Rational,
    privateUpper:Rational,
    fitnessLower:Rational,
    fitnessUpper:Rational,
    interview:Interview<Q>,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Progress in
  requires candidates.Keys() != {}
  decreases interview.NodeCount(), 0
  // Representation in
  requires rootCandidates.Valid()
  requires rootCandidates.Size(weight, BoolBits, BoolBits) <= n
  requires fitness.Size(weight, BoolBits, BoolBits) <= n
  requires multiplicity.Size(weight, BoolBits, NatBits) <= n
  requires privateQuestions.Size(weight) <= n && interview.Size(weight) <= n
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires privateQuestions.Init()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires candidates.UniverseWithin(rootCandidates)
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() :: multiplicity.Model()[candidate] <= maximum
  requires RationalBits(privateLower) <= n && RationalBits(privateUpper) <= n
  requires RationalBits(fitnessLower) <= n && RationalBits(fitnessUpper) <= n
  // State out
  ensures accepted == CDPCInterviewSemantics(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model(),
    fitnessLower.Model(), fitnessUpper.Model(),
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
      candidates, fitness, multiplicity, fitnessLower, fitnessUpper, maximum, n, weight, counter);
    var privacyAccepted:bool;
    privacyAccepted, counter := CheckPrivateSafe(
      candidates, privateQuestions, multiplicity, privateLower, privateUpper, maximum, n, weight, counter);
    assert counter <= counter_in + BudgetCDPCNode(n);
    tree_budget_combine(interview.NodeCount(), 0, 0, BudgetCDPCNode(n), 2, counter_in, counter, counter, counter);
    assert CDPCInterviewSemantics(
      fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      privateLower.Model(), privateUpper.Model(),
      fitnessLower.Model(), fitnessUpper.Model(),
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
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, trueBranch, maximum, n, weight, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckCDPCBranch(
    rootCandidates, falseCandidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, falseBranch, maximum, n, weight, counter);
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
      privateLower.Model(), privateUpper.Model(),
      fitnessLower.Model(), fitnessUpper.Model(),
      candidates.Keys(), interview.Model()) == accepted by {
    reveal CDPCInterviewSemantics();
  }
}

// An impossible answer must lead to End. Otherwise, check privacy before
// continuing, even if the next node is a leaf.
method {:isolate_assertions} CheckCDPCBranch<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    privateLower:Rational,
    privateUpper:Rational,
    fitnessLower:Rational,
    fitnessUpper:Rational,
    interview:Interview<Q>,
    ghost maximum:nat, ghost n:nat, ghost weight:Q -> nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Progress in
  decreases interview.NodeCount(), 1
  // Representation in
  requires rootCandidates.Valid()
  requires rootCandidates.Size(weight, BoolBits, BoolBits) <= n
  requires fitness.Size(weight, BoolBits, BoolBits) <= n
  requires multiplicity.Size(weight, BoolBits, NatBits) <= n
  requires privateQuestions.Size(weight) <= n && interview.Size(weight) <= n
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires privateQuestions.Init()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires candidates.UniverseWithin(rootCandidates)
  requires NatBits(maximum) <= n
  requires forall candidate | candidate in candidates.Keys() :: multiplicity.Model()[candidate] <= maximum
  requires RationalBits(privateLower) <= n && RationalBits(privateUpper) <= n
  requires RationalBits(fitnessLower) <= n && RationalBits(fitnessUpper) <= n
  // State out
  ensures accepted == CDPCBranch(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower.Model(), privateUpper.Model(),
    fitnessLower.Model(), fitnessUpper.Model(),
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

  var empty:bool;
  empty, counter := candidates.IsEmpty(counter_in, mapContext);
  if empty {
    accepted, counter := interview.IsEnd(counter, context);
    reveal CDPCBranch();
    branch_budget_own_fits(interview.NodeCount(),
      BudgetCDPCNode(n),
      counter_in, counter);
    return accepted, counter;
  }

  var privacyAccepted:bool;
  privacyAccepted, counter := CheckPrivateSafe(
    candidates, privateQuestions, multiplicity,
    privateLower, privateUpper, maximum, n, weight, counter);
  ghost var setupCounter := counter;
  if !privacyAccepted {
    reveal CDPCBranch();
    branch_budget_own_fits(interview.NodeCount(),
      BudgetCDPCNode(n),
      counter_in, counter);
    return false, counter;
  }

  accepted, counter := VerifyCDPCCore(
    rootCandidates, candidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, interview, maximum, n, weight, counter);
  reveal CDPCBranch();
  branch_budget_combine(interview.NodeCount(),
    BudgetCDPCNode(n),
    counter_in, setupCounter, counter);
}
