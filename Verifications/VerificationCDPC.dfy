include "VerificationCDPC_aux.dfy"

/*
Interface-based verifier for weighted binary CDPC certificates.

The auxiliary file contains the cost bounds and mathematical proof machinery.
All executable collection operations use traits; Model() is ghost-only.
*/

method verifyCDPC<Q(!new)>(
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    interview:Interview<Q>)
    returns (accepted:bool, ghost counter:nat)
  requires init_Map_Map_T(fitness)
  requires init_Map_Map_T(multiplicity)
  requires init_Set(privateQuestions)
  requires CDPCValidInstance(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures accepted ==
    CDPCCorrectCertificate(
       fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
       privateLower, privateUpper, fitnessLower, fitnessUpper,
       interview.Model())
  ensures accepted ==> CDPC(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures counter <= poly_VerifyCDPC(fitness, multiplicity, privateQuestions, interview)
{
  // Pese a ser un mapa, los values dan igual
  var questions:Map<Q, bool>;
  questions, counter := fitness.PickKey(0);
  assert questions.Keys() == CDPCQuestions(fitness.Keys());

  var structureAccepted:bool;
  structureAccepted, counter := CheckInterviewFits(questions, questions, interview, counter);
  CDPCInterviewCostBound(fitness, questions, interview);
  if !structureAccepted {
    return false, counter;
  }

  accepted, counter := VerifyCDPC_rec(
    fitness, fitness, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    interview, counter);
}

// A question is removed along both paths. Even unreachable branches must be
// structurally valid; the representative's Boolean answers are not consulted.
method CheckInterviewFits<Q(!new)>(
    questions:Map<Q, bool>,
    remaining:Map<Q, bool>,
    interview:Interview<Q>,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires questions.Valid()
  requires in_universe_Map(remaining, questions)
  decreases interview.NodeCount()
  ensures accepted == InterviewFits(interview.Model(), remaining.Keys())
  ensures counter <= counter_in + poly_CheckInterviewFits(questions, interview)
{
  in_universe_lemma_Map(remaining, questions);
  reveal InterviewFits();
  reveal interview.NodeCount();
  reveal InterviewNodes();

  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd {
    return true, counter;
  }

  var question:Q;
  question, counter := interview.Question(counter);
  var available:bool;
  available, counter := remaining.ContainsKey(question, counter);
  if !available {
    return false, counter;
  }

  var childRemaining:Map<Q, bool>;
  childRemaining, counter := remaining.Remove(question, counter);
  var trueBranch:Interview<Q>;
  trueBranch, counter := interview.Branch(true, counter);
  var falseBranch:Interview<Q>;
  falseBranch, counter := interview.Branch(false, counter);
  assert counter <= counter_in + cost_CheckInterviewFitsNode(questions);

  ghost var setupCounter := counter;
  var trueAccepted:bool;
  trueAccepted, counter := CheckInterviewFits(questions, childRemaining, trueBranch, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckInterviewFits(questions, childRemaining, falseBranch, counter);
  accepted := trueAccepted && falseAccepted;

  reveal trueBranch.NodeCount();
  reveal falseBranch.NodeCount();
  TreeCostCombine(
    interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    cost_CheckInterviewFitsNode(questions), 1,
    counter_in, setupCounter, afterTrueCounter, counter);
}

// Recursive certificate validation

// Leaves must classify the remaining population while preserving privacy.
// Internal nodes partition that population and validate both answer branches.
method VerifyCDPC_rec<Q(!new)>(
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
  requires rootCandidates.Valid()
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires privateQuestions.Valid()
  requires candidates.Keys() != {}
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires in_universe_Map_Map_T(candidates, rootCandidates)
  decreases interview.NodeCount(), 0
  ensures accepted == CDPCCertificate(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates.Keys(), interview.Model())
  ensures counter <= counter_in + poly_VerifyCDPCCertificate(
    rootCandidates, fitness, multiplicity, privateQuestions, interview)
{
  reveal interview.NodeCount();
  reveal InterviewNodes();
  CDPCCandidateCostMonotonic(candidates, rootCandidates, fitness, multiplicity, privateQuestions);

  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd {
    var classificationAccepted:bool;
    classificationAccepted, counter := CheckClassification(candidates, fitness, multiplicity, fitnessLower, fitnessUpper, counter);
    var privacyAccepted:bool;
    privacyAccepted, counter := CheckPrivateSafe(candidates, privateQuestions, multiplicity, privateLower, privateUpper, counter);
    reveal CDPCCertificate();
    assert counter <= counter_in + cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions);
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

  in_universe_transitive_Map_Map_T(trueCandidates, candidates, rootCandidates);
  in_universe_transitive_Map_Map_T(falseCandidates, candidates, rootCandidates);
  assert counter <= counter_in + cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions);

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
  reveal CDPCCertificate();

  reveal trueBranch.NodeCount();
  reveal falseBranch.NodeCount();
  TreeCostCombine(
    interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions), 2,
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
  requires rootCandidates.Valid()
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires privateQuestions.Valid()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  requires in_universe_Map_Map_T(candidates, rootCandidates)
  decreases interview.NodeCount(), 1
  ensures accepted == CDPCBranch(
    fitness.Model(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates.Keys(), interview.Model())
  ensures counter <= counter_in + poly_CheckCDPCBranch(
    rootCandidates, fitness, multiplicity, privateQuestions, interview)
{
  reveal interview.NodeCount();
  reveal InterviewNodes();
  CDPCCandidateCostMonotonic(candidates, rootCandidates, fitness, multiplicity, privateQuestions);

  var empty:bool;
  empty, counter := candidates.Empty(counter_in);
  if empty {
    accepted, counter := interview.IsEnd(counter);
    reveal CDPCBranch();
    BranchOwnCostFits(interview.NodeCount(),
      cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions),
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
    BranchOwnCostFits(interview.NodeCount(),
      cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions),
      counter_in, counter);
    return false, counter;
  }

  accepted, counter := VerifyCDPC_rec(
    rootCandidates, candidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, interview, counter);
  reveal CDPCBranch();
  BranchCostCombine(interview.NodeCount(),
    cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions),
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
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() != {}
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  ensures accepted == ClassificationDecided(
    candidates.Keys(), fitness.Model(), multiplicity.Model(),
    fitnessLower, fitnessUpper)
  ensures counter <= counter_in +
    poly_CheckClassification(candidates, fitness, multiplicity)
{
  var totalMass:nat;
  totalMass, counter := ComputeWeightedMass(
    candidates, multiplicity, counter_in);
  var fitMass:nat;
  fitMass, counter := ComputeFitMass(
    candidates, fitness, multiplicity, counter);
  accepted :=
    (fitMass as real) <= fitnessLower * (totalMass as real) ||
    fitnessUpper * (totalMass as real) <= (fitMass as real);
  counter := counter + 1;

  ClassificationFromMasses(
    candidates.Keys(), fitness.Model(), multiplicity.Model(),
    totalMass, fitMass, fitnessLower, fitnessUpper);
}

method {:isolate_assertions} CheckPrivateSafe<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    privateQuestions:Set<Q>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateLower:real,
    privateUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() != {}
  requires candidates.Keys() <= multiplicity.Keys()
  requires privateQuestions.Valid()
  ensures accepted == PrivateSafe(
    candidates.Keys(), multiplicity.Model(), privateQuestions.Model(),
    privateLower, privateUpper)
  ensures counter <= counter_in +
    poly_CheckPrivateSafe(candidates, privateQuestions, multiplicity)
{
  var totalMass:nat;
  totalMass, counter := ComputeWeightedMass(
    candidates, multiplicity, counter_in);
  var remaining:Set<Q>;
  remaining, counter := privateQuestions.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  accepted := true;

  ghost var baseCost :=
    poly_ComputeWeightedMass(candidates, multiplicity) +
    cost_SetCopyUniverse(privateQuestions) + cost_SetEmpty(privateQuestions);
  ghost var stepCost :=
    cost_SetPick(privateQuestions) +
    poly_CheckPrivateQuestion(candidates, multiplicity) +
    cost_SetRemoveUniverse(privateQuestions) +
    cost_SetEmpty(privateQuestions);
  LinearLoopBudgetZero(baseCost, stepCost);
  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Set(remaining, privateQuestions)
    invariant empty == (remaining.Model() == {})
    invariant accepted ==
      (forall question | question in
        privateQuestions.Model() - remaining.Model() ::
        exists privateMass:nat |
            PrivateMass(
            candidates.Keys(), question, multiplicity.Model(), privateMass) ::
          privateLower * (totalMass as real) <= (privateMass as real) <=
            privateUpper * (totalMass as real))
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      privateQuestions.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Set(remaining, privateQuestions);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    var question:Q;
    question, counter := remaining.Pick(counter);
    var questionAccepted:bool;
    questionAccepted, counter := CheckPrivateQuestion(
      candidates, question, multiplicity, totalMass,
      privateLower, privateUpper, counter);
    accepted := accepted && questionAccepted;
    remaining, counter := remaining.Remove(question, counter);
    empty, counter := remaining.Empty(counter);

    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      privateQuestions.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);

    assert privateQuestions.Model() - remaining.Model() ==
      (privateQuestions.Model() - previousRemaining.Model()) + {question};
  }
  identity_substraction_lemma(privateQuestions.Model(), remaining.Model());
  PrivateSafeFromTotal(
    candidates.Keys(), multiplicity.Model(), privateQuestions.Model(),
    totalMass, privateLower, privateUpper);
  LinearLoopBudgetBound(
    baseCost, stepCost,
    privateQuestions.Cardinality(), privateQuestions.UBCardinality());
}

method CheckPrivateQuestion<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    multiplicity:Map_Map_T<Q, bool, nat>,
    totalMass:nat,
    privateLower:real,
    privateUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  requires WeightedMass(
    candidates.Keys(), multiplicity.Model(), totalMass)
  ensures accepted ==
    (exists privateMass:nat |
      PrivateMass(
        candidates.Keys(), question, multiplicity.Model(), privateMass) ::
      privateLower * (totalMass as real) <= (privateMass as real) <=
        privateUpper * (totalMass as real))
  ensures counter <= counter_in +
    poly_CheckPrivateQuestion(candidates, multiplicity)
{
  var privateMass:nat;
  privateMass, counter := ComputePrivateMass(
    candidates, question, multiplicity, counter_in);
  accepted :=
    privateLower * (totalMass as real) <= (privateMass as real) <=
    privateUpper * (totalMass as real);
  counter := counter + 1;

  PrivateQuestionFromMass(
    candidates.Keys(), question, multiplicity.Model(),
    totalMass, privateMass, privateLower, privateUpper);
}

// Population filtering and weighted sums

method {:isolate_assertions} FilterCandidateMap<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    answer:bool,
    ghost counter_in:nat)
    returns (filtered:Map_Map_T<Q, bool, bool>, ghost counter:nat)
  requires candidates.Valid()
  ensures filtered.Valid()
  ensures filtered.Keys() ==
    FilterCandidates(candidates.Keys(), question, answer)
  ensures in_universe_Map_Map_T(filtered, candidates)
  ensures counter <= counter_in +
    poly_FilterCandidates(candidates)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  remaining, counter := candidates.Copy(counter);
  // Keep the original map values; only incompatible candidate keys are removed.
  filtered, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  ghost var baseCost :=
    2 * cost_MapMapTCopyUniverse(candidates) + cost_MapMapTEmpty(candidates);
  ghost var stepCost :=
    cost_MapMapTPickKeyUniverse(candidates) +
    2 * (candidates.UBSize_Keys() + 1) +
    2 * cost_MapMapTRemoveUniverse(candidates) + cost_MapMapTEmpty(candidates);
  LinearLoopBudgetZero(baseCost, stepCost);
  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Map_Map_T(remaining, candidates)
    invariant in_universe_Map_Map_T(filtered, candidates)
    invariant empty == (remaining.Model() == map[])
    invariant filtered.Keys() ==
      FilterCandidates(candidates.Keys() - remaining.Keys(), question, answer) +
      remaining.Keys()
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost, candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Map_Map_T(remaining, candidates);
    in_universe_lemma_Map_Map_T(filtered, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
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
    empty, counter := remaining.Empty(counter);

    assert candidates.Cardinality() - remaining.Cardinality() ==
      candidates.Cardinality() - previousRemaining.Cardinality() + 1;
    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost, candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);
    assert counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost, candidates.Cardinality() - remaining.Cardinality());

    assert candidates.Keys() - remaining.Keys() ==
      (candidates.Keys() - previousRemaining.Keys()) + {candidate.Model()};
    assert FilterCandidates(
      candidates.Keys() - remaining.Keys(), question, answer) ==
      if keep then
        FilterCandidates(
          candidates.Keys() - previousRemaining.Keys(), question, answer) +
        {candidate.Model()}
      else
        FilterCandidates(
          candidates.Keys() - previousRemaining.Keys(), question, answer);
  }
  in_universe_lemma_Map_Map_T(filtered, candidates);
  LinearLoopBudgetBound(
    baseCost, stepCost, candidates.Cardinality(), candidates.UBCardinality());
}

method ComputeWeightedMass<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost counter_in:nat)
    returns (mass:nat, ghost counter:nat)
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  ensures WeightedMass(candidates.Keys(), multiplicity.Model(), mass)
  ensures counter <= counter_in +
    poly_ComputeWeightedMass(candidates, multiplicity)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  mass := 0;
  WeightedMassEmpty(multiplicity.Model());
  ghost var baseCost :=
    cost_MapMapTCopyUniverse(candidates) + cost_MapMapTEmpty(candidates);
  ghost var stepCost :=
    cost_MapMapTPickKeyUniverse(candidates) +
    cost_MapMapTGetUniverse(multiplicity) +
    cost_MapMapTRemoveUniverse(candidates) +
    cost_MapMapTEmpty(candidates);
  LinearLoopBudgetZero(baseCost, stepCost);
  assert in_universe_Map_Map_T(remaining, candidates);
  assert candidates.Keys() - remaining.Keys() == {};
  assert WeightedMass(
    candidates.Keys() - remaining.Keys(), multiplicity.Model(), mass);

  assert {:split_here} true;
  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Map_Map_T(remaining, candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    invariant empty == (remaining.Model() == map[])
    invariant WeightedMass(
      candidates.Keys() - remaining.Keys(), multiplicity.Model(), mass)
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Map_Map_T(remaining, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    ghost var previousMass := mass;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter);
    var candidateMultiplicity:nat;
    candidateMultiplicity, counter := multiplicity.Get(candidate, counter);
    mass := mass + candidateMultiplicity;
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.Empty(counter);

    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);

    WeightedMassProgress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), multiplicity.Model(), previousMass, mass);
  }
  assert {:split_here} true;
  identity_substraction_lemma(candidates.Keys(), remaining.Keys());
  LinearLoopBudgetBound(
    baseCost, stepCost,
    candidates.Cardinality(), candidates.UBCardinality());
}

method ComputeFitMass<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost counter_in:nat)
    returns (mass:nat, ghost counter:nat)
  requires candidates.Valid()
  requires fitness.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= fitness.Keys()
  requires candidates.Keys() <= multiplicity.Keys()
  ensures FitMass(
    candidates.Keys(), fitness.Model(), multiplicity.Model(), mass)
  ensures counter <= counter_in +
    poly_ComputeFitMass(candidates, fitness, multiplicity)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  mass := 0;
  WeightedMassEmpty(multiplicity.Model());
  ghost var baseCost :=
    cost_MapMapTCopyUniverse(candidates) + cost_MapMapTEmpty(candidates);
  ghost var stepCost :=
    cost_MapMapTPickKeyUniverse(candidates) +
    cost_MapMapTGetUniverse(fitness) +
    cost_MapMapTGetUniverse(multiplicity) +
    cost_MapMapTRemoveUniverse(candidates) +
    cost_MapMapTEmpty(candidates);
  LinearLoopBudgetZero(baseCost, stepCost);
  assert (set candidate | candidate in
            candidates.Keys() - remaining.Keys() &&
            candidate in fitness.Model() && fitness.Model()[candidate] :: candidate) == {};

  assert {:split_here} true;
  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Map_Map_T(remaining, candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= fitness.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    invariant empty == (remaining.Model() == map[])
    invariant WeightedMass(
      set candidate | candidate in
        candidates.Keys() - remaining.Keys() &&
        candidate in fitness.Model() && fitness.Model()[candidate] :: candidate,
      multiplicity.Model(), mass)
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Map_Map_T(remaining, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    ghost var previousMass := mass;
    var candidate:Map<Q, bool>;
    candidate, counter := remaining.PickKey(counter);
    var isFit:bool;
    isFit, counter := fitness.Get(candidate, counter);
    if isFit {
      var candidateMultiplicity:nat;
      candidateMultiplicity, counter := multiplicity.Get(candidate, counter);
      mass := mass + candidateMultiplicity;
    }
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.Empty(counter);

    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);

    FitMassProgress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), fitness.Model(), multiplicity.Model(),
      previousMass, mass, isFit);
  }
  assert {:split_here} true;
  identity_substraction_lemma(candidates.Keys(), remaining.Keys());
  FitMassDefinition(
    candidates.Keys(), fitness.Model(), multiplicity.Model(), mass,
    set candidate | candidate in candidates.Keys() &&
                    candidate in fitness.Model() &&
                    fitness.Model()[candidate] :: candidate);
  LinearLoopBudgetBound(
    baseCost, stepCost,
    candidates.Cardinality(), candidates.UBCardinality());
}

method {:isolate_assertions} ComputePrivateMass<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    question:Q,
    multiplicity:Map_Map_T<Q, bool, nat>,
    ghost counter_in:nat)
    returns (mass:nat, ghost counter:nat)
  requires candidates.Valid()
  requires multiplicity.Valid()
  requires candidates.Keys() <= multiplicity.Keys()
  ensures PrivateMass(
    candidates.Keys(), question, multiplicity.Model(), mass)
  ensures counter <= counter_in +
    poly_ComputePrivateMass(candidates, multiplicity)
{
  counter := counter_in;
  var remaining:Map_Map_T<Q, bool, bool>;
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  mass := 0;
  WeightedMassEmpty(multiplicity.Model());
  ghost var baseCost :=
    cost_MapMapTCopyUniverse(candidates) + cost_MapMapTEmpty(candidates);
  ghost var stepCost :=
    cost_MapMapTPickKeyUniverse(candidates) +
    2 * (candidates.UBSize_Keys() + 1) +
    cost_MapMapTGetUniverse(multiplicity) +
    cost_MapMapTRemoveUniverse(candidates) +
    cost_MapMapTEmpty(candidates);
  LinearLoopBudgetZero(baseCost, stepCost);
  assert (set candidate | candidate in
            candidates.Keys() - remaining.Keys() &&
            question in candidate && candidate[question] :: candidate) == {};

  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Map_Map_T(remaining, candidates)
    invariant remaining.Keys() <= candidates.Keys()
    invariant candidates.Keys() <= multiplicity.Keys()
    invariant empty == (remaining.Model() == map[])
    invariant WeightedMass(
      set candidate | candidate in
        candidates.Keys() - remaining.Keys() &&
        question in candidate && candidate[question] :: candidate,
      multiplicity.Model(), mass)
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Map_Map_T(remaining, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    ghost var previousMass := mass;
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
      mass := mass + candidateMultiplicity;
    }
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.Empty(counter);

    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);

    PrivateMassProgress(
      candidates.Keys(), previousRemaining.Keys(), remaining.Keys(),
      candidate.Model(), question, multiplicity.Model(),
      previousMass, mass, selected);
  }
  identity_substraction_lemma(candidates.Keys(), remaining.Keys());
  PrivateMassDefinition(
    candidates.Keys(), question, multiplicity.Model(), mass,
    set candidate | candidate in candidates.Keys() &&
                    question in candidate && candidate[question] :: candidate);
  LinearLoopBudgetBound(
    baseCost, stepCost,
    candidates.Cardinality(), candidates.UBCardinality());
}
