include "../Collections/ConcreteInterview.dfy"
include "VerificationCDPC_aux.dfy"
include "../Problems/CDPCLemmas.dfy"

// SHORT-CERTIFICATE COMPLETENESS
// Every positive CDPC instance has a correct, polynomially short interview.
ghost method CDPCHasShortCertificate<Q(!new)>(
    questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real) returns (certificate:Interview<Q>)
  requires questions.Init() && fitness.Init() && multiplicity.Init() && privateQuestions.Init()
  requires CDPCValidInstance(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires CDPC(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures fresh(certificate)
  ensures CDPCCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper, certificate.Model())
  ensures certificate.NodeCount() <= PolynomialCDPCCertificateSize(fitness.Cardinality() + questions.Cardinality() + 1)
{
  var tree :| CDPCCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper, tree);
  certificate := new ConcreteInterview<Q>(tree);
  cdpc_certificate_size_bound(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper, tree);
  var n := fitness.Cardinality() + questions.Cardinality() + 1;
  nonnegative_product_monotonic(fitness.Cardinality(), questions.Cardinality(), n, n);
  multiplication_associative(2, fitness.Cardinality(), questions.Cardinality());
  multiplication_associative(2, n, n);
  assert 2*fitness.Cardinality()*questions.Cardinality()+1 <= 2*n*n+1;
}

// POLYNOMIAL VERIFICATION

// Determines that PolynomialVerifyCDPC is polynomial with respect to the scalar input,
// which is a measure of the size of the instance (unlike for Set Cover, where it also
// depended on the size of the certificate).
// Note that this does not directly depend on the instance of the problem; the relationship
// between PolynomialVerifySetCover and the verification of Set Cover is defined later.
// The admissibility criteria of certificates of CDPC is simpler than Set Cover's and
// straightforward to demonstrate that it can be done in polynomial time with respect
// to the size of the instance, even if the certificate itself is arbitrarily large.
lemma {:isolate_assertions} polynomial_verify_cdpc_bound()
  ensures HasPolynomialBound(
    (n:nat) => true,
    (n:nat) => n,
    PolynomialVerifyCDPC, 620, 6)
  ensures IsPolynomial(
    (n:nat) => true,
    (n:nat) => n,
    PolynomialVerifyCDPC)
{
  forall n:nat
    ensures PolynomialVerifyCDPC(n) <= 620 * NatPower(n+1, 6)
  {
    assert {:fuel NatPower, 7} PolynomialVerifyCDPC(n) ==
      54*NatPower(n, 0) + 64*NatPower(n, 1) + 144*NatPower(n, 2) +
      158*NatPower(n, 3) + 96*NatPower(n, 4) + 60*NatPower(n, 5) + 8*NatPower(n, 6);
    weighted_monomial_bound(n, n, 0, 6, 54);
    weighted_monomial_bound(n, n, 1, 6, 64);
    weighted_monomial_bound(n, n, 2, 6, 144);
    weighted_monomial_bound(n, n, 3, 6, 158);
    weighted_monomial_bound(n, n, 4, 6, 96);
    weighted_monomial_bound(n, n, 5, 6, 60);
    weighted_monomial_bound(n, n, 6, 6, 8);
  }
  polynomial_witness(
    (n:nat) => true,
    (n:nat) => n,
    PolynomialVerifyCDPC,
    620, 6);
}

// Using the previous lemma, concludes that the verification of CDPC (including admissibility) runs in polynomial time
// with respect to the size of the instance.
lemma {:isolate_assertions} cost_verify_cdpc_is_polynomial<Q(!new)>(
    fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, questions:Set<Q>, interview:Interview<Q>)
  requires questions.Init() && fitness.Init() && multiplicity.Init() && privateQuestions.Init()
  requires fitness.Model().Keys == multiplicity.Model().Keys
  requires privateQuestions.Model() <= questions.Model()
  requires forall candidate | candidate in fitness.Model() :: candidate.Keys == questions.Model()
  ensures CostVerifyCDPC(fitness, multiplicity, privateQuestions, questions, interview) <=
    PolynomialVerifyCDPC(fitness.Cardinality() + questions.Cardinality() + 1)
  ensures CostVerifyCDPC(fitness, multiplicity, privateQuestions, questions, interview) <=
    620 * NatPower(fitness.Cardinality() + questions.Cardinality() + 2, 6)
{
  polynomial_verify_cdpc_bound();
  var n := fitness.Cardinality() + questions.Cardinality() + 1;
  subset_cardinality_bound(privateQuestions.Model(), questions.Model());
  fitness.u_cardinality_keys_bound(questions.Cardinality());
  multiplicity.u_cardinality_keys_bound(questions.Cardinality());
  cost_verify_cdpc_bound(fitness, multiplicity, privateQuestions, questions, interview, n);
}


// ABSENCE OF FALSE POSITIVES

// Main verification method for CDPC.
// Demonstrates that no admissable certificate accepts a negative instance.
// Additionally, ensures that the verification runs in the time defined by the functions used before.
method VerifyCDPC<Q(!new)>(
    questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, interview:Interview<Q>)
    returns (accepted:bool, ghost counter:nat)
  requires questions.Init() && fitness.Init() && multiplicity.Init() && privateQuestions.Init()
  requires CDPCValidInstance(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures accepted == CDPCCertificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper, interview.Model())
  ensures accepted ==> CDPC(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures counter <= CostVerifyCDPC(fitness, multiplicity, privateQuestions, questions, interview)
{
  reveal CostVerifyCDPC();
  subset_cardinality_bound(privateQuestions.Model(), questions.Model());
  fitness.u_cardinality_keys_bound(questions.Cardinality());
  multiplicity.u_cardinality_keys_bound(questions.Cardinality());
  var population, questionCount, size:nat;
  population, counter := fitness.Count(0);
  questionCount, counter := questions.Count(counter);
  var limit := 2*population*questionCount+1;
  size, counter := CountInterviewBounded(interview, limit, counter);
  assert {:split_here} counter <= fitness.CostCount() + questions.CostCount() + (limit+1)*CostCountInterviewNode(interview);
  if size > limit {
    cdpc_oversized_not_certificate(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
      privateLower, privateUpper, fitnessLower, fitnessUpper, interview.Model());
    nat_multiplication_monotonic(limit, 0, CostCheckInterviewFitsNode(questions, interview));
    nat_multiplication_monotonic(2*limit, 0, CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions, interview));
    return false, counter;
  }
  assert {:split_here} interview.NodeCount() <= limit;
  accepted, counter := CheckInterviewFits(questions, questions, interview, counter);
  cost_cdpc_structure_bound(fitness, questions, interview);
  if !accepted { return false, counter; }
  cost_cdpc_checking_bound(questions, fitness, multiplicity, privateQuestions, interview);
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
  ensures counter <= counter_in + size*CostCountInterviewNode(interview)
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
  ensures counter <= counter_in + interview.NodeCount()*CostCheckInterviewFitsNode(questions, interview)
{
  remaining.universe_within_bound(questions);
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
  cost_tree_combine(interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    CostCheckInterviewFitsNode(questions, interview), 1, counter_in, setupCounter, afterTrueCounter, counter);
}


// Recursive certificate validation

// Leaves must classify the remaining population while preserving privacy.
// Internal nodes partition that population and validate both answer branches.
method {:isolate_assertions} VerifyCDPCCore<Q(!new)>(
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
  requires privateQuestions.Init()
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
  cost_cdpc_candidate_monotonic(candidates, rootCandidates, fitness, multiplicity, privateQuestions);

  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd {
    var classificationAccepted:bool;
    classificationAccepted, counter := CheckClassification(candidates, fitness, multiplicity, fitnessLower, fitnessUpper, counter);
    var privacyAccepted:bool;
    privacyAccepted, counter := CheckPrivateSafe(candidates, privateQuestions, multiplicity, privateLower, privateUpper, counter);
    reveal CDPCInterviewSemantics();
    assert counter <= counter_in + CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview);
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

  trueCandidates.universe_within_transitive(candidates, rootCandidates);
  falseCandidates.universe_within_transitive(candidates, rootCandidates);
  assert counter <= counter_in + CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview);

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
  cost_tree_combine(
    interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview), 2,
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
  requires privateQuestions.Init()
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
  cost_cdpc_candidate_monotonic(candidates, rootCandidates, fitness, multiplicity, privateQuestions);

  var empty:bool;
  empty, counter := candidates.IsEmpty(counter_in);
  if empty {
    accepted, counter := interview.IsEnd(counter);
    reveal CDPCBranch();
    cost_branch_own_fits(interview.NodeCount(),
      CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview),
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
    cost_branch_own_fits(interview.NodeCount(),
      CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview),
      counter_in, counter);
    return false, counter;
  }

  accepted, counter := VerifyCDPCCore(
    rootCandidates, candidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, interview, counter);
  reveal CDPCBranch();
  cost_branch_combine(interview.NodeCount(),
    CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions, interview),
    counter_in, setupCounter, counter);
}


// Node count includes End leaves and counts both child positions, even when equal.
// Each Ask carries one atomic question label, so explicit structural size is O(nodes).
ghost function PolynomialCDPCCertificateSize(n:nat):nat
{ 2*n*n + 1 }
