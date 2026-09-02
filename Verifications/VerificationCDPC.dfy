include "../Problems/CDPC.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Lemmas.dfy"

/*
Complete interface-based verifier for weighted binary CDPC certificates.

The verifier consumes the abstract Set and Interview interfaces.  Fitness and
multiplicity remain the mathematical maps used by Problems/CDPC.dfy; every map
access is protected by the valid-instance and compatible-population contracts.
*/

method verifyCDPC<Q(!new)>(
    questions:Set<Q>,
    candidates:Set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:Set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    interview:Interview<Q>)
    returns (accepted:bool, ghost counter:nat)
  requires init_Set(questions)
  requires init_Set(candidates)
  requires init_Set(privateQuestions)
  requires candidates.Model() == fitness.Keys
  requires interview.QuestionDomain() == questions.Model()
  requires interview.RemainingQuestions() == questions.Model()
  requires ValidCDPCInstance(
    questions.Model(), fitness, multiplicity, privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures accepted ==
    (InterviewFits(interview.Model(), questions.Model()) &&
     CertificateCDPC(
       fitness, multiplicity, privateQuestions.Model(),
       privateLower, privateUpper, fitnessLower, fitnessUpper,
       fitness.Keys, interview.Model()))
  ensures accepted ==> CDPC(
    questions.Model(), fitness, multiplicity, privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  ensures counter <= poly_VerifyCDPC(questions, candidates, privateQuestions, interview)
{
  assert questions.Valid();
  assert candidates.Valid();
  assert privateQuestions.Valid();
  assert questions.UBSize0() == questions.Cardinality();

  var structureAccepted:bool;
  structureAccepted, counter := CheckInterviewFits(
    questions, interview, questions.Cardinality(), 0);
  if !structureAccepted {
    accepted := false;
    return accepted, counter;
  }

  reveal ValidCDPCInstance();
  assert fitness.Keys == multiplicity.Keys;
  assert candidates.Model() != {};
  assert candidates.Model() <= fitness.Keys;
  assert candidates.Model() <= multiplicity.Keys;
  assert forall candidate | candidate in candidates.Model() ::
    |candidate.Keys| <= questions.Cardinality() by {
    forall candidate | candidate in candidates.Model()
      ensures |candidate.Keys| <= questions.Cardinality()
    {
      assert candidate.Keys == questions.Model();
    }
  }

  accepted, counter := VerifyCDPCCertificateRec(
    candidates, candidates, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    questions.Cardinality(), interview, counter);

  if accepted {
    reveal CDPC();
    assert exists certificate:InterviewModel<Q> |
      InterviewFits(certificate, questions.Model()) ::
      CertificateCDPC(
        fitness, multiplicity, privateQuestions.Model(),
        privateLower, privateUpper, fitnessLower, fitnessUpper,
        fitness.Keys, certificate) by {
      assert InterviewFits(interview.Model(), questions.Model());
    }
  }
}






// Weighted mass is independent of the sequence used to enumerate a candidate
// set.  These lemmas bridge the relational semantic definition to the concrete
// enumeration performed by the verifier.
lemma MultisetCancellation<T>(
    common:multiset<T>, first:multiset<T>, second:multiset<T>)
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

lemma SequenceWeightedMassConcat<Q(!new)>(
    left:seq<Candidate<Q>>,
    right:seq<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>)
  requires forall candidate | candidate in left + right ::
    candidate in multiplicity.Keys
  ensures SequenceWeightedMass(left + right, multiplicity) ==
          SequenceWeightedMass(left, multiplicity) +
          SequenceWeightedMass(right, multiplicity)
  decreases |left|
{
  if left == [] {
    assert left + right == right;
    reveal SequenceWeightedMass();
  } else {
    assert (left + right)[0] == left[0];
    assert (left + right)[1..] == left[1..] + right;
    SequenceWeightedMassConcat(left[1..], right, multiplicity);
    calc {
      SequenceWeightedMass(left + right, multiplicity);
      == {
        reveal SequenceWeightedMass();
      }
      multiplicity[left[0]] +
        SequenceWeightedMass(left[1..] + right, multiplicity);
      ==
      multiplicity[left[0]] +
         SequenceWeightedMass(left[1..], multiplicity) +
         SequenceWeightedMass(right, multiplicity);
      == {
        reveal SequenceWeightedMass();
      }
      SequenceWeightedMass(left, multiplicity) +
        SequenceWeightedMass(right, multiplicity);
    }
  }
}

lemma {:isolate_assertions} SequenceWeightedMassRemoveAt<Q(!new)>(
    values:seq<Candidate<Q>>,
    index:nat,
    multiplicity:map<Candidate<Q>, nat>)
  requires index < |values|
  requires forall candidate | candidate in values ::
    candidate in multiplicity.Keys
  ensures SequenceWeightedMass(values, multiplicity) ==
          multiplicity[values[index]] +
          SequenceWeightedMass(values[..index] + values[index + 1..], multiplicity)
{
  var prefix := values[..index];
  var suffix := values[index + 1..];
  assert values == prefix + [values[index]] + suffix;
  assert values == prefix + ([values[index]] + suffix);
  SequenceWeightedMassConcat(prefix, [values[index]] + suffix, multiplicity);
  SequenceWeightedMassConcat([values[index]], suffix, multiplicity);
  SequenceWeightedMassConcat(prefix, suffix, multiplicity);
  assert SequenceWeightedMass([values[index]], multiplicity) ==
         multiplicity[values[index]] by {
    reveal SequenceWeightedMass();
  }
  calc {
    SequenceWeightedMass(values, multiplicity);
    == SequenceWeightedMass(prefix, multiplicity) +
       SequenceWeightedMass([values[index]] + suffix, multiplicity);
    == SequenceWeightedMass(prefix, multiplicity) +
       multiplicity[values[index]] +
       SequenceWeightedMass(suffix, multiplicity);
    == multiplicity[values[index]] +
       (SequenceWeightedMass(prefix, multiplicity) +
        SequenceWeightedMass(suffix, multiplicity));
    == multiplicity[values[index]] +
       SequenceWeightedMass(prefix + suffix, multiplicity);
  }
}

lemma SequenceWeightedMassPermutation<Q(!new)>(
    first:seq<Candidate<Q>>,
    second:seq<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>)
  requires multiset(first) == multiset(second)
  requires forall candidate | candidate in first + second ::
    candidate in multiplicity.Keys
  ensures SequenceWeightedMass(first, multiplicity) ==
          SequenceWeightedMass(second, multiplicity)
  decreases |first|
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
    MultisetCancellation(
      multiset{candidate}, multiset(first[1..]), multiset(secondWithout));
    assert forall element | element in first[1..] + secondWithout ::
      element in multiplicity.Keys;
    SequenceWeightedMassPermutation(first[1..], secondWithout, multiplicity);
    SequenceWeightedMassRemoveAt(second, index, multiplicity);
    assert SequenceWeightedMass(first, multiplicity) ==
           multiplicity[candidate] +
           SequenceWeightedMass(first[1..], multiplicity) by {
      reveal SequenceWeightedMass();
    }
    calc {
      SequenceWeightedMass(first, multiplicity);
      == multiplicity[candidate] +
         SequenceWeightedMass(first[1..], multiplicity);
      == multiplicity[candidate] +
         SequenceWeightedMass(secondWithout, multiplicity);
      == SequenceWeightedMass(second, multiplicity);
    }
  }
}

lemma WeightedMassUnique<Q(!new)>(
    candidates:set<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>,
    first:nat,
    second:nat)
  requires candidates <= multiplicity.Keys
  requires WeightedMass(candidates, multiplicity, first)
  requires WeightedMass(candidates, multiplicity, second)
  ensures first == second
{
  reveal WeightedMass();
  var firstEnumeration :| multiset(firstEnumeration) == multiset(candidates) &&
    (forall candidate | candidate in firstEnumeration :: candidate in multiplicity.Keys) &&
    first == SequenceWeightedMass(firstEnumeration, multiplicity);
  var secondEnumeration :| multiset(secondEnumeration) == multiset(candidates) &&
    (forall candidate | candidate in secondEnumeration :: candidate in multiplicity.Keys) &&
    second == SequenceWeightedMass(secondEnumeration, multiplicity);
  SequenceWeightedMassPermutation(firstEnumeration, secondEnumeration, multiplicity);
}

lemma WeightedMassAdd<Q(!new)>(
    candidates:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    multiplicity:map<Candidate<Q>, nat>,
    mass:nat)
  requires candidates <= multiplicity.Keys
  requires candidate in multiplicity.Keys
  requires candidate !in candidates
  requires WeightedMass(candidates, multiplicity, mass)
  ensures WeightedMass(
    candidates + {candidate}, multiplicity, mass + multiplicity[candidate])
{
  reveal WeightedMass();
  var enumeration :| multiset(enumeration) == multiset(candidates) &&
    (forall element | element in enumeration :: element in multiplicity.Keys) &&
    mass == SequenceWeightedMass(enumeration, multiplicity);
  SequenceWeightedMassConcat(enumeration, [candidate], multiplicity);
  assert multiset(enumeration + [candidate]) ==
         multiset(candidates + {candidate});
}


ghost function cost_CDPCMapLookup(domainSize:nat):nat
{
  domainSize + 1
}

ghost function poly_ComputeWeightedMass<Q(!new)>(
    candidates:Set<Candidate<Q>>):nat
{
  cost_Copy(candidates.UBSize0()) + cost_Empty() +
  candidates.Cardinality() *
    (cost_Pick(0) + cost_CDPCMapLookup(candidates.Cardinality()) +
     cost_Remove(candidates.UBSize0()) + cost_Empty())
}

method ComputeWeightedMass<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>,
    ghost counter_in:nat)
    returns (mass:nat, ghost counter:nat)
  requires candidates.Valid()
  requires candidates.Model() <= multiplicity.Keys
  ensures WeightedMass(candidates.Model(), multiplicity, mass)
  ensures counter <= counter_in + poly_ComputeWeightedMass(candidates)
{
  counter := counter_in;
  var remaining:Set<Candidate<Q>>;
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  mass := 0;
  WeightedMassEmpty(multiplicity);
  ghost var baseCost :=
    cost_Copy(candidates.UBSize0()) + cost_Empty();
  ghost var stepCost :=
    cost_Pick(0) + cost_CDPCMapLookup(candidates.Cardinality()) +
    cost_Remove(candidates.UBSize0()) + cost_Empty();
  LinearLoopBudgetZero(baseCost, stepCost);
  assert candidates.Model() - remaining.Model() == {};
  assert WeightedMass(
    candidates.Model() - remaining.Model(), multiplicity, mass);

  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Set(remaining, candidates)
    invariant empty == (remaining.Model() == {})
    invariant WeightedMass(
      candidates.Model() - remaining.Model(), multiplicity, mass)
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Set(remaining, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    ghost var previousMass := mass;
    var candidate:Candidate<Q>;
    candidate, counter := remaining.Pick(counter);
    assert candidate in candidates.Model();
    mass := mass + multiplicity[candidate];
    counter := counter + cost_CDPCMapLookup(candidates.Cardinality());
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.Empty(counter);

    assert previousRemaining.Cardinality() == remaining.Cardinality() + 1;
    assert candidates.Cardinality() - remaining.Cardinality() ==
      (candidates.Cardinality() - previousRemaining.Cardinality()) + 1;
    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);
    assert counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality());

    assert candidate !in candidates.Model() - previousRemaining.Model();
    WeightedMassAdd(
      candidates.Model() - previousRemaining.Model(), candidate,
      multiplicity, previousMass);
    assert candidates.Model() - remaining.Model() ==
      (candidates.Model() - previousRemaining.Model()) + {candidate};
  }
  identity_substraction_lemma(candidates.Model(), remaining.Model());
  reveal LinearLoopBudget();
}

ghost function cost_CandidateMapOperation(questionCount:nat):nat
{
  questionCount + 1
}

ghost function poly_FilterCandidates<Q(!new)>(
    candidates:Set<Candidate<Q>>, questionCount:nat):nat
{
  2 * cost_Copy(candidates.UBSize0()) + cost_Empty() +
  candidates.Cardinality() *
    (cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
     2 * cost_Remove(candidates.UBSize0()) + cost_Empty())
}

ghost function {:opaque} FilterCandidateBudget<Q(!new)>(
    candidates:Set<Candidate<Q>>, questionCount:nat, processed:nat):nat
{
  2 * cost_Copy(candidates.UBSize0()) + cost_Empty() +
  processed *
    (cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
     2 * cost_Remove(candidates.UBSize0()) + cost_Empty())
}

lemma FilterCandidateBudgetZero<Q(!new)>(
    candidates:Set<Candidate<Q>>, questionCount:nat)
  ensures FilterCandidateBudget(candidates, questionCount, 0) ==
    2 * cost_Copy(candidates.UBSize0()) + cost_Empty()
{
  reveal FilterCandidateBudget();
}

lemma FilterCandidateBudgetStep<Q(!new)>(
    candidates:Set<Candidate<Q>>, questionCount:nat, processed:nat)
  ensures FilterCandidateBudget(candidates, questionCount, processed + 1) ==
    FilterCandidateBudget(candidates, questionCount, processed) +
    cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
    2 * cost_Remove(candidates.UBSize0()) + cost_Empty()
{
  reveal FilterCandidateBudget();
}

lemma FilterCandidateBudgetFinish<Q(!new)>(
    candidates:Set<Candidate<Q>>, questionCount:nat)
  ensures FilterCandidateBudget(
    candidates, questionCount, candidates.Cardinality()) ==
    poly_FilterCandidates(candidates, questionCount)
{
  reveal FilterCandidateBudget();
}

lemma FilterCandidateCounterAdvance<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    questionCount:nat,
    processed:nat,
    counterBase:nat,
    counterBefore:nat,
    counterAfter:nat)
  requires counterBefore <= counterBase +
    FilterCandidateBudget(candidates, questionCount, processed)
  requires counterAfter <= counterBefore +
    cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
    2 * cost_Remove(candidates.UBSize0()) + cost_Empty()
  ensures counterAfter <= counterBase +
    FilterCandidateBudget(candidates, questionCount, processed + 1)
{
  FilterCandidateBudgetStep(candidates, questionCount, processed);
}

method {:isolate_assertions} FilterCandidateSet<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    question:Q,
    answer:bool,
    ghost questionCount:nat,
    ghost counter_in:nat)
    returns (filtered:Set<Candidate<Q>>, ghost counter:nat)
  requires candidates.Valid()
  requires forall candidate | candidate in candidates.Model() ::
    |candidate.Keys| <= questionCount
  ensures filtered.Valid()
  ensures filtered.Model() ==
    FilterCandidates(candidates.Model(), question, answer)
  ensures filtered.Model() <= candidates.Model()
  ensures filtered.UBSize0() <= candidates.UBSize0()
  ensures counter <= counter_in +
    poly_FilterCandidates(candidates, questionCount)
{
  counter := counter_in;
  var remaining:Set<Candidate<Q>>;
  remaining, counter := candidates.Copy(counter);
  filtered, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  FilterCandidateBudgetZero(candidates, questionCount);

  assert FilterCandidates({}, question, answer) == {};
  assert filtered.Model() ==
    FilterCandidates(candidates.Model() - remaining.Model(), question, answer) +
    remaining.Model();

  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Set(remaining, candidates)
    invariant in_universe_Set(filtered, candidates)
    invariant empty == (remaining.Model() == {})
    invariant filtered.Model() ==
      FilterCandidates(candidates.Model() - remaining.Model(), question, answer) +
      remaining.Model()
    invariant counter <= counter_in + FilterCandidateBudget(
      candidates, questionCount,
      candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Set(remaining, candidates);
    in_universe_lemma_Set(filtered, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    var candidate:Candidate<Q>;
    candidate, counter := remaining.Pick(counter);
    remaining, counter := remaining.Remove(candidate, counter);

    var keep:bool := question in candidate;
    counter := counter + cost_CandidateMapOperation(questionCount);
    if keep {
      keep := candidate[question] == answer;
      counter := counter + cost_CandidateMapOperation(questionCount);
    }
    if !keep {
      filtered, counter := filtered.Remove(candidate, counter);
    }
    empty, counter := remaining.Empty(counter);

    assert previousRemaining.Cardinality() == remaining.Cardinality() + 1;
    assert candidates.Cardinality() - remaining.Cardinality() ==
      (candidates.Cardinality() - previousRemaining.Cardinality()) + 1;
    assert counter <= iterationCounter +
      cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
      2 * cost_Remove(candidates.UBSize0()) + cost_Empty();
    FilterCandidateCounterAdvance(
      candidates, questionCount,
      candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);
    assert counter <= counter_in + FilterCandidateBudget(
      candidates, questionCount,
      (candidates.Cardinality() - previousRemaining.Cardinality()) + 1);
    assert FilterCandidateBudget(
      candidates, questionCount,
      (candidates.Cardinality() - previousRemaining.Cardinality()) + 1) ==
      FilterCandidateBudget(
        candidates, questionCount,
        candidates.Cardinality() - remaining.Cardinality());
    assert counter <= counter_in + FilterCandidateBudget(
      candidates, questionCount,
      candidates.Cardinality() - remaining.Cardinality());

    assert candidates.Model() - remaining.Model() ==
      (candidates.Model() - previousRemaining.Model()) + {candidate};
    assert FilterCandidates(
      candidates.Model() - remaining.Model(), question, answer) ==
      if keep then
        FilterCandidates(
          candidates.Model() - previousRemaining.Model(), question, answer) +
        {candidate}
      else
        FilterCandidates(
          candidates.Model() - previousRemaining.Model(), question, answer);
  }
  identity_substraction_lemma(candidates.Model(), remaining.Model());
  in_universe_lemma_Set(filtered, candidates);
  FilterCandidateBudgetFinish(candidates, questionCount);
}


lemma FitMassUnique<Q(!new)>(
    candidates:set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    first:nat,
    second:nat)
  requires candidates <= multiplicity.Keys
  requires FitMass(candidates, fitness, multiplicity, first)
  requires FitMass(candidates, fitness, multiplicity, second)
  ensures first == second
{
  reveal FitMass();
  WeightedMassUnique(
    set candidate | candidate in candidates &&
                    candidate in fitness && fitness[candidate] :: candidate,
    multiplicity, first, second);
}

lemma PrivateMassUnique<Q(!new)>(
    candidates:set<Candidate<Q>>,
    question:Q,
    multiplicity:map<Candidate<Q>, nat>,
    first:nat,
    second:nat)
  requires candidates <= multiplicity.Keys
  requires PrivateMass(candidates, question, multiplicity, first)
  requires PrivateMass(candidates, question, multiplicity, second)
  ensures first == second
{
  reveal PrivateMass();
  WeightedMassUnique(
    set candidate | candidate in candidates &&
                    question in candidate && candidate[question] :: candidate,
    multiplicity, first, second);
}

lemma PrivateBoundsTransferTotal<Q(!new)>(
    candidates:set<Candidate<Q>>,
    privateQuestions:set<Q>,
    multiplicity:map<Candidate<Q>, nat>,
    firstTotal:nat,
    secondTotal:nat,
    privateLower:real,
    privateUpper:real)
  requires candidates <= multiplicity.Keys
  requires firstTotal == secondTotal
  requires forall question | question in privateQuestions ::
    exists privateMass:nat |
      PrivateMass(candidates, question, multiplicity, privateMass) ::
      privateLower * (firstTotal as real) <= (privateMass as real) <=
        privateUpper * (firstTotal as real)
  ensures forall question | question in privateQuestions ::
    exists privateMass:nat |
      PrivateMass(candidates, question, multiplicity, privateMass) ::
      privateLower * (secondTotal as real) <= (privateMass as real) <=
        privateUpper * (secondTotal as real)
{
  forall question | question in privateQuestions
    ensures exists privateMass:nat |
      PrivateMass(candidates, question, multiplicity, privateMass) ::
      privateLower * (secondTotal as real) <= (privateMass as real) <=
        privateUpper * (secondTotal as real)
  {
    var privateMass:nat :|
      PrivateMass(candidates, question, multiplicity, privateMass) &&
      privateLower * (firstTotal as real) <= (privateMass as real) <=
        privateUpper * (firstTotal as real);
  }
}

ghost function poly_ComputeFitMass<Q(!new)>(
    candidates:Set<Candidate<Q>>):nat
{
  cost_Copy(candidates.UBSize0()) + cost_Empty() +
  candidates.Cardinality() *
    (cost_Pick(0) + 2 * cost_CDPCMapLookup(candidates.Cardinality()) +
     cost_Remove(candidates.UBSize0()) + cost_Empty())
}

method ComputeFitMass<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    ghost counter_in:nat)
    returns (mass:nat, ghost counter:nat)
  requires candidates.Valid()
  requires candidates.Model() <= fitness.Keys
  requires candidates.Model() <= multiplicity.Keys
  ensures FitMass(candidates.Model(), fitness, multiplicity, mass)
  ensures counter <= counter_in + poly_ComputeFitMass(candidates)
{
  counter := counter_in;
  var remaining:Set<Candidate<Q>>;
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  mass := 0;
  WeightedMassEmpty(multiplicity);
  ghost var baseCost :=
    cost_Copy(candidates.UBSize0()) + cost_Empty();
  ghost var stepCost :=
    cost_Pick(0) + 2 * cost_CDPCMapLookup(candidates.Cardinality()) +
    cost_Remove(candidates.UBSize0()) + cost_Empty();
  LinearLoopBudgetZero(baseCost, stepCost);
  assert (set candidate | candidate in
            candidates.Model() - remaining.Model() &&
            candidate in fitness && fitness[candidate] :: candidate) == {};

  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Set(remaining, candidates)
    invariant empty == (remaining.Model() == {})
    invariant WeightedMass(
      set candidate | candidate in
        candidates.Model() - remaining.Model() &&
        candidate in fitness && fitness[candidate] :: candidate,
      multiplicity, mass)
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Set(remaining, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    ghost var previousMass := mass;
    var candidate:Candidate<Q>;
    candidate, counter := remaining.Pick(counter);
    var isFit := fitness[candidate];
    counter := counter + cost_CDPCMapLookup(candidates.Cardinality());
    if isFit {
      mass := mass + multiplicity[candidate];
      counter := counter + cost_CDPCMapLookup(candidates.Cardinality());
    }
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.Empty(counter);

    assert previousRemaining.Cardinality() == remaining.Cardinality() + 1;
    assert candidates.Cardinality() - remaining.Cardinality() ==
      (candidates.Cardinality() - previousRemaining.Cardinality()) + 1;
    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);
    assert counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality());

    ghost var previousFit :=
      set element | element in
        candidates.Model() - previousRemaining.Model() &&
        element in fitness && fitness[element] :: element;
    ghost var currentFit :=
      set element | element in
        candidates.Model() - remaining.Model() &&
        element in fitness && fitness[element] :: element;
    if isFit {
      assert candidate !in previousFit;
      WeightedMassAdd(previousFit, candidate, multiplicity, previousMass);
      assert currentFit == previousFit + {candidate};
    } else {
      assert currentFit == previousFit;
    }
  }
  identity_substraction_lemma(candidates.Model(), remaining.Model());
  FitMassDefinition(
    candidates.Model(), fitness, multiplicity, mass,
    set candidate | candidate in candidates.Model() &&
                    candidate in fitness && fitness[candidate] :: candidate);
  reveal LinearLoopBudget();
}

ghost function poly_ComputePrivateMass<Q(!new)>(
    candidates:Set<Candidate<Q>>, questionCount:nat):nat
{
  cost_Copy(candidates.UBSize0()) + cost_Empty() +
  candidates.Cardinality() *
    (cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
     cost_CDPCMapLookup(candidates.Cardinality()) +
     cost_Remove(candidates.UBSize0()) + cost_Empty())
}

ghost function {:opaque} LinearLoopBudget(
    base:nat, step:nat, processed:nat):nat
{
  base + processed * step
}

lemma LinearLoopBudgetZero(base:nat, step:nat)
  ensures LinearLoopBudget(base, step, 0) == base
{
  reveal LinearLoopBudget();
}

lemma LinearLoopBudgetAdvance(
    base:nat,
    step:nat,
    processed:nat,
    counterBase:nat,
    counterBefore:nat,
    counterAfter:nat)
  requires counterBefore <= counterBase +
    LinearLoopBudget(base, step, processed)
  requires counterAfter <= counterBefore + step
  ensures counterAfter <= counterBase +
    LinearLoopBudget(base, step, processed + 1)
{
  reveal LinearLoopBudget();
}

method {:isolate_assertions} ComputePrivateMass<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    question:Q,
    ghost questionCount:nat,
    multiplicity:map<Candidate<Q>, nat>,
    ghost counter_in:nat)
    returns (mass:nat, ghost counter:nat)
  requires candidates.Valid()
  requires candidates.Model() <= multiplicity.Keys
  requires forall candidate | candidate in candidates.Model() ::
    |candidate.Keys| <= questionCount
  ensures PrivateMass(candidates.Model(), question, multiplicity, mass)
  ensures counter <= counter_in +
    poly_ComputePrivateMass(candidates, questionCount)
{
  counter := counter_in;
  var remaining:Set<Candidate<Q>>;
  remaining, counter := candidates.Copy(counter);
  var empty:bool;
  empty, counter := remaining.Empty(counter);
  mass := 0;
  WeightedMassEmpty(multiplicity);
  ghost var baseCost :=
    cost_Copy(candidates.UBSize0()) + cost_Empty();
  ghost var stepCost :=
    cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
    cost_CDPCMapLookup(candidates.Cardinality()) +
    cost_Remove(candidates.UBSize0()) + cost_Empty();
  LinearLoopBudgetZero(baseCost, stepCost);
  assert (set candidate | candidate in
            candidates.Model() - remaining.Model() &&
            question in candidate && candidate[question] :: candidate) == {};

  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Set(remaining, candidates)
    invariant empty == (remaining.Model() == {})
    invariant WeightedMass(
      set candidate | candidate in
        candidates.Model() - remaining.Model() &&
        question in candidate && candidate[question] :: candidate,
      multiplicity, mass)
    invariant counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality())
  {
    in_universe_lemma_Set(remaining, candidates);
    ghost var iterationCounter := counter;
    var previousRemaining := remaining;
    ghost var previousMass := mass;
    var candidate:Candidate<Q>;
    candidate, counter := remaining.Pick(counter);
    var selected:bool := question in candidate;
    counter := counter + cost_CandidateMapOperation(questionCount);
    if selected {
      selected := candidate[question];
      counter := counter + cost_CandidateMapOperation(questionCount);
    }
    if selected {
      mass := mass + multiplicity[candidate];
      counter := counter + cost_CDPCMapLookup(candidates.Cardinality());
    }
    remaining, counter := remaining.Remove(candidate, counter);
    empty, counter := remaining.Empty(counter);

    assert previousRemaining.Cardinality() == remaining.Cardinality() + 1;
    assert candidates.Cardinality() - remaining.Cardinality() ==
      (candidates.Cardinality() - previousRemaining.Cardinality()) + 1;
    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      candidates.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);
    assert counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      candidates.Cardinality() - remaining.Cardinality());

    ghost var previousPrivate :=
      set element | element in
        candidates.Model() - previousRemaining.Model() &&
        question in element && element[question] :: element;
    ghost var currentPrivate :=
      set element | element in
        candidates.Model() - remaining.Model() &&
        question in element && element[question] :: element;
    if selected {
      assert candidate !in previousPrivate;
      WeightedMassAdd(previousPrivate, candidate, multiplicity, previousMass);
      assert currentPrivate == previousPrivate + {candidate};
    } else {
      assert currentPrivate == previousPrivate;
    }
  }
  identity_substraction_lemma(candidates.Model(), remaining.Model());
  PrivateMassDefinition(
    candidates.Model(), question, multiplicity, mass,
    set candidate | candidate in candidates.Model() &&
                    question in candidate && candidate[question] :: candidate);
  reveal LinearLoopBudget();
}


ghost function poly_CheckClassification<Q(!new)>(
    candidates:Set<Candidate<Q>>):nat
{
  poly_ComputeWeightedMass(candidates) +
  poly_ComputeFitMass(candidates) + 1
}

method CheckClassification<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    fitnessLower:real,
    fitnessUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires candidates.Valid()
  requires candidates.Model() != {}
  requires candidates.Model() <= fitness.Keys
  requires candidates.Model() <= multiplicity.Keys
  ensures accepted == ClassificationDecided(
    candidates.Model(), fitness, multiplicity,
    fitnessLower, fitnessUpper)
  ensures counter <= counter_in + poly_CheckClassification(candidates)
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

  assert WeightedMass(candidates.Model(), multiplicity, totalMass);
  assert FitMass(candidates.Model(), fitness, multiplicity, fitMass);
  if ClassificationDecided(
      candidates.Model(), fitness, multiplicity,
      fitnessLower, fitnessUpper) {
    reveal ClassificationDecided();
    var semanticTotal:nat, semanticFit:nat :|
      WeightedMass(candidates.Model(), multiplicity, semanticTotal) &&
      FitMass(candidates.Model(), fitness, multiplicity, semanticFit) &&
      ((semanticFit as real) <=
         fitnessLower * (semanticTotal as real) ||
       fitnessUpper * (semanticTotal as real) <=
         (semanticFit as real));
    WeightedMassUnique(
      candidates.Model(), multiplicity, totalMass, semanticTotal);
    FitMassUnique(
      candidates.Model(), fitness, multiplicity, fitMass, semanticFit);
  }
  reveal ClassificationDecided();
}

ghost function poly_CheckPrivateQuestion<Q(!new)>(
    candidates:Set<Candidate<Q>>, questionCount:nat):nat
{
  poly_ComputePrivateMass(candidates, questionCount) + 1
}

method CheckPrivateQuestion<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    question:Q,
    ghost questionCount:nat,
    multiplicity:map<Candidate<Q>, nat>,
    totalMass:nat,
    privateLower:real,
    privateUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires candidates.Valid()
  requires candidates.Model() <= multiplicity.Keys
  requires forall candidate | candidate in candidates.Model() ::
    |candidate.Keys| <= questionCount
  requires WeightedMass(candidates.Model(), multiplicity, totalMass)
  ensures accepted ==
    (exists privateMass:nat |
      PrivateMass(candidates.Model(), question, multiplicity, privateMass) ::
      privateLower * (totalMass as real) <= (privateMass as real) <=
        privateUpper * (totalMass as real))
  ensures counter <= counter_in +
    poly_CheckPrivateQuestion(candidates, questionCount)
{
  var privateMass:nat;
  privateMass, counter := ComputePrivateMass(
    candidates, question, questionCount, multiplicity, counter_in);
  accepted :=
    privateLower * (totalMass as real) <= (privateMass as real) <=
    privateUpper * (totalMass as real);
  counter := counter + 1;

  if exists semanticMass:nat |
      PrivateMass(candidates.Model(), question, multiplicity, semanticMass) ::
      privateLower * (totalMass as real) <= (semanticMass as real) <=
        privateUpper * (totalMass as real) {
    var semanticMass:nat :|
      PrivateMass(candidates.Model(), question, multiplicity, semanticMass) &&
      privateLower * (totalMass as real) <= (semanticMass as real) <=
        privateUpper * (totalMass as real);
    PrivateMassUnique(
      candidates.Model(), question, multiplicity,
      privateMass, semanticMass);
  }
}

ghost function poly_CheckPrivateSafe<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    questionCount:nat):nat
{
  poly_ComputeWeightedMass(candidates) +
  cost_Copy(privateQuestions.UBSize0()) + cost_Empty() +
  privateQuestions.Cardinality() *
    (cost_Pick(0) +
     poly_CheckPrivateQuestion(candidates, questionCount) +
     cost_Remove(privateQuestions.UBSize0()) + cost_Empty())
}

method {:isolate_assertions} CheckPrivateSafe<Q(!new)>(
    candidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    ghost questionCount:nat,
    multiplicity:map<Candidate<Q>, nat>,
    privateLower:real,
    privateUpper:real,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires candidates.Valid()
  requires candidates.Model() != {}
  requires candidates.Model() <= multiplicity.Keys
  requires privateQuestions.Valid()
  requires forall candidate | candidate in candidates.Model() ::
    |candidate.Keys| <= questionCount
  ensures accepted == PrivateSafe(
    candidates.Model(), multiplicity, privateQuestions.Model(),
    privateLower, privateUpper)
  ensures counter <= counter_in +
    poly_CheckPrivateSafe(candidates, privateQuestions, questionCount)
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
    poly_ComputeWeightedMass(candidates) +
    cost_Copy(privateQuestions.UBSize0()) + cost_Empty();
  ghost var stepCost :=
    cost_Pick(0) +
    poly_CheckPrivateQuestion(candidates, questionCount) +
    cost_Remove(privateQuestions.UBSize0()) + cost_Empty();
  LinearLoopBudgetZero(baseCost, stepCost);
  assert privateQuestions.Model() - remaining.Model() == {};
  assert accepted ==
    (forall question | question in
      privateQuestions.Model() - remaining.Model() ::
      exists privateMass:nat |
        PrivateMass(
          candidates.Model(), question, multiplicity, privateMass) ::
        privateLower * (totalMass as real) <= (privateMass as real) <=
          privateUpper * (totalMass as real));

  while !empty
    decreases remaining.Cardinality()
    invariant in_universe_Set(remaining, privateQuestions)
    invariant empty == (remaining.Model() == {})
    invariant accepted ==
      (forall question | question in
        privateQuestions.Model() - remaining.Model() ::
        exists privateMass:nat |
          PrivateMass(
            candidates.Model(), question, multiplicity, privateMass) ::
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
      candidates, question, questionCount, multiplicity, totalMass,
      privateLower, privateUpper, counter);
    accepted := accepted && questionAccepted;
    remaining, counter := remaining.Remove(question, counter);
    empty, counter := remaining.Empty(counter);

    assert previousRemaining.Cardinality() == remaining.Cardinality() + 1;
    assert privateQuestions.Cardinality() - remaining.Cardinality() ==
      (privateQuestions.Cardinality() -
        previousRemaining.Cardinality()) + 1;
    assert counter <= iterationCounter + stepCost;
    LinearLoopBudgetAdvance(
      baseCost, stepCost,
      privateQuestions.Cardinality() - previousRemaining.Cardinality(),
      counter_in, iterationCounter, counter);
    assert counter <= counter_in + LinearLoopBudget(
      baseCost, stepCost,
      privateQuestions.Cardinality() - remaining.Cardinality());

    assert privateQuestions.Model() - remaining.Model() ==
      (privateQuestions.Model() - previousRemaining.Model()) + {question};
    assert accepted ==
      (forall checked | checked in
        privateQuestions.Model() - remaining.Model() ::
        exists privateMass:nat |
          PrivateMass(
            candidates.Model(), checked, multiplicity, privateMass) ::
          privateLower * (totalMass as real) <= (privateMass as real) <=
            privateUpper * (totalMass as real));
  }
  identity_substraction_lemma(
    privateQuestions.Model(), remaining.Model());
  assert accepted ==
    (forall question | question in privateQuestions.Model() ::
      exists privateMass:nat |
        PrivateMass(
          candidates.Model(), question, multiplicity, privateMass) ::
        privateLower * (totalMass as real) <= (privateMass as real) <=
          privateUpper * (totalMass as real));

  assert accepted ==> PrivateSafe(
      candidates.Model(), multiplicity, privateQuestions.Model(),
      privateLower, privateUpper) by {
    if accepted {
      reveal PrivateSafe();
      assert exists semanticTotal:nat |
        WeightedMass(candidates.Model(), multiplicity, semanticTotal) ::
        forall question | question in privateQuestions.Model() ::
          exists privateMass:nat |
            PrivateMass(
              candidates.Model(), question, multiplicity, privateMass) ::
            privateLower * (semanticTotal as real) <=
              (privateMass as real) <=
            privateUpper * (semanticTotal as real) by {
        assert WeightedMass(
          candidates.Model(), multiplicity, totalMass);
      }
    }
  }
  assert (PrivateSafe(
      candidates.Model(), multiplicity, privateQuestions.Model(),
      privateLower, privateUpper)) ==> accepted by {
    if PrivateSafe(
        candidates.Model(), multiplicity, privateQuestions.Model(),
        privateLower, privateUpper) {
      reveal PrivateSafe();
      var semanticTotal:nat :|
        WeightedMass(candidates.Model(), multiplicity, semanticTotal) &&
        (forall question | question in privateQuestions.Model() ::
          exists privateMass:nat |
            PrivateMass(
              candidates.Model(), question, multiplicity, privateMass) ::
            privateLower * (semanticTotal as real) <=
              (privateMass as real) <=
            privateUpper * (semanticTotal as real));
      WeightedMassUnique(
        candidates.Model(), multiplicity, totalMass, semanticTotal);
      assert semanticTotal == totalMass;
      PrivateBoundsTransferTotal(
        candidates.Model(), privateQuestions.Model(), multiplicity,
        semanticTotal, totalMass, privateLower, privateUpper);
    }
  }
  reveal LinearLoopBudget();
}


ghost function cost_CheckInterviewFitsNode(questionCount:nat):nat
{
  cost_InterviewIsEnd() + cost_InterviewQuestion() +
  cost_Contains(questionCount) + cost_Remove(questionCount) +
  2 * cost_InterviewBranch()
}

ghost function poly_CheckInterviewFits<Q(!new)>(
    questionCount:nat, interview:Interview<Q>):nat
{
  interview.NodeCount() * cost_CheckInterviewFitsNode(questionCount)
}

method CheckInterviewFits<Q(!new)>(
    remaining:Set<Q>,
    interview:Interview<Q>,
    ghost questionCount:nat,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires remaining.Valid()
  requires remaining.UBSize0() <= questionCount
  requires interview.RemainingQuestions() == remaining.Model()
  decreases interview.NodeCount()
  ensures accepted == InterviewFits(
    interview.Model(), remaining.Model())
  ensures counter <= counter_in +
    poly_CheckInterviewFits(questionCount, interview)
{
  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd {
    accepted := true;
    reveal InterviewFits();
    assert 1 <= interview.NodeCount() by {
      reveal interview.NodeCount();
      reveal InterviewNodes();
    }
    return accepted, counter;
  }

  var question:Q;
  question, counter := interview.Question(counter);
  var available:bool;
  available, counter := remaining.Contains(question, counter);
  if !available {
    accepted := false;
    reveal InterviewFits();
    assert 1 <= interview.NodeCount() by {
      reveal interview.NodeCount();
      reveal InterviewNodes();
    }
    return accepted, counter;
  }

  var childRemaining:Set<Q>;
  childRemaining, counter := remaining.Remove(question, counter);
  var trueBranch:Interview<Q>;
  trueBranch, counter := interview.Branch(true, counter);
  var falseBranch:Interview<Q>;
  falseBranch, counter := interview.Branch(false, counter);
  assert childRemaining.UBSize0() <= questionCount;
  assert trueBranch.RemainingQuestions() == childRemaining.Model();
  assert falseBranch.RemainingQuestions() == childRemaining.Model();
  assert counter <= counter_in + cost_CheckInterviewFitsNode(questionCount);
  ghost var setupCounter := counter;

  var trueAccepted:bool;
  trueAccepted, counter := CheckInterviewFits(
    childRemaining, trueBranch, questionCount, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckInterviewFits(
    childRemaining, falseBranch, questionCount, counter);
  accepted := trueAccepted && falseAccepted;

  reveal InterviewFits();
  reveal interview.NodeCount();
  reveal trueBranch.NodeCount();
  reveal falseBranch.NodeCount();
  reveal InterviewNodes();
  assert interview.NodeCount() ==
    1 + trueBranch.NodeCount() + falseBranch.NodeCount();
  assert afterTrueCounter <= setupCounter +
    trueBranch.NodeCount() * cost_CheckInterviewFitsNode(questionCount);
  assert counter <= afterTrueCounter +
    falseBranch.NodeCount() * cost_CheckInterviewFitsNode(questionCount);
  assert counter <= counter_in + cost_CheckInterviewFitsNode(questionCount) +
    trueBranch.NodeCount() * cost_CheckInterviewFitsNode(questionCount) +
    falseBranch.NodeCount() * cost_CheckInterviewFitsNode(questionCount);
  assert counter <= counter_in +
    interview.NodeCount() * cost_CheckInterviewFitsNode(questionCount);
}


lemma CDPCCandidateCostMonotonic<Q(!new)>(
    smaller:Set<Candidate<Q>>,
    larger:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    questionCount:nat)
  requires smaller.Cardinality() <= larger.Cardinality()
  requires smaller.UBSize0() <= larger.UBSize0()
  ensures poly_ComputeWeightedMass(smaller) <=
          poly_ComputeWeightedMass(larger)
  ensures poly_ComputeFitMass(smaller) <= poly_ComputeFitMass(larger)
  ensures poly_ComputePrivateMass(smaller, questionCount) <=
          poly_ComputePrivateMass(larger, questionCount)
  ensures poly_FilterCandidates(smaller, questionCount) <=
          poly_FilterCandidates(larger, questionCount)
  ensures poly_CheckClassification(smaller) <=
          poly_CheckClassification(larger)
  ensures poly_CheckPrivateQuestion(smaller, questionCount) <=
          poly_CheckPrivateQuestion(larger, questionCount)
  ensures poly_CheckPrivateSafe(
            smaller, privateQuestions, questionCount) <=
          poly_CheckPrivateSafe(
            larger, privateQuestions, questionCount)
{
  assert cost_Copy(smaller.UBSize0()) <= cost_Copy(larger.UBSize0());
  assert cost_Remove(smaller.UBSize0()) <=
         cost_Remove(larger.UBSize0());
  assert cost_CDPCMapLookup(smaller.Cardinality()) <=
         cost_CDPCMapLookup(larger.Cardinality());

  mult_preserves_order(
    smaller.Cardinality(),
    cost_Pick(0) + cost_CDPCMapLookup(smaller.Cardinality()) +
      cost_Remove(smaller.UBSize0()) + cost_Empty(),
    larger.Cardinality(),
    cost_Pick(0) + cost_CDPCMapLookup(larger.Cardinality()) +
      cost_Remove(larger.UBSize0()) + cost_Empty());
  mult_preserves_order(
    smaller.Cardinality(),
    cost_Pick(0) + 2 * cost_CDPCMapLookup(smaller.Cardinality()) +
      cost_Remove(smaller.UBSize0()) + cost_Empty(),
    larger.Cardinality(),
    cost_Pick(0) + 2 * cost_CDPCMapLookup(larger.Cardinality()) +
      cost_Remove(larger.UBSize0()) + cost_Empty());
  mult_preserves_order(
    smaller.Cardinality(),
    cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
      cost_CDPCMapLookup(smaller.Cardinality()) +
      cost_Remove(smaller.UBSize0()) + cost_Empty(),
    larger.Cardinality(),
    cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
      cost_CDPCMapLookup(larger.Cardinality()) +
      cost_Remove(larger.UBSize0()) + cost_Empty());
  mult_preserves_order(
    smaller.Cardinality(),
    cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
      2 * cost_Remove(smaller.UBSize0()) + cost_Empty(),
    larger.Cardinality(),
    cost_Pick(0) + 2 * cost_CandidateMapOperation(questionCount) +
      2 * cost_Remove(larger.UBSize0()) + cost_Empty());

  assert poly_ComputeWeightedMass(smaller) <=
         poly_ComputeWeightedMass(larger);
  assert poly_ComputeFitMass(smaller) <= poly_ComputeFitMass(larger);
  assert poly_ComputePrivateMass(smaller, questionCount) <=
         poly_ComputePrivateMass(larger, questionCount);
  assert poly_FilterCandidates(smaller, questionCount) <=
         poly_FilterCandidates(larger, questionCount);
  assert poly_CheckClassification(smaller) <=
         poly_CheckClassification(larger);
  assert poly_CheckPrivateQuestion(smaller, questionCount) <=
         poly_CheckPrivateQuestion(larger, questionCount);
  mult_preserves_order(
    privateQuestions.Cardinality(),
    cost_Pick(0) +
      poly_CheckPrivateQuestion(smaller, questionCount) +
      cost_Remove(privateQuestions.UBSize0()) + cost_Empty(),
    privateQuestions.Cardinality(),
    cost_Pick(0) +
      poly_CheckPrivateQuestion(larger, questionCount) +
      cost_Remove(privateQuestions.UBSize0()) + cost_Empty());
}


ghost function cost_VerifyCDPCCertificateNode<Q(!new)>(
    rootCandidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    questionCount:nat):nat
{
  cost_InterviewIsEnd() + cost_InterviewQuestion() +
  2 * poly_FilterCandidates(rootCandidates, questionCount) +
  2 * cost_InterviewBranch() + cost_Empty() +
  poly_CheckClassification(rootCandidates) +
  poly_CheckPrivateSafe(
    rootCandidates, privateQuestions, questionCount) + 1
}

ghost function {:opaque} poly_VerifyCDPCCertificate<Q(!new)>(
    rootCandidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    questionCount:nat,
    interview:Interview<Q>):nat
  ensures poly_VerifyCDPCCertificate(
    rootCandidates, privateQuestions, questionCount, interview) ==
    if interview.NodeCount() == 0 then 0
    else
      (2 * interview.NodeCount() - 1) *
        cost_VerifyCDPCCertificateNode(
          rootCandidates, privateQuestions, questionCount)
{
  if interview.NodeCount() == 0 then 0
  else
    (2 * interview.NodeCount() - 1) *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount)
}

ghost function {:opaque} poly_CheckCDPCBranch<Q(!new)>(
    rootCandidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    questionCount:nat,
    interview:Interview<Q>):nat
  ensures poly_CheckCDPCBranch(
    rootCandidates, privateQuestions, questionCount, interview) ==
    2 * interview.NodeCount() *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount)
{
  2 * interview.NodeCount() *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount)
}

lemma CertificateAskCostCombine(
    nodes:nat,
    trueNodes:nat,
    falseNodes:nat,
    nodeCost:nat,
    counterBase:nat,
    counter:nat)
  requires nodes == 1 + trueNodes + falseNodes
  requires counter <= counterBase + nodeCost +
    2 * trueNodes * nodeCost + 2 * falseNodes * nodeCost
  ensures counter <= counterBase + (2 * nodes - 1) * nodeCost
{}

lemma VerifyCertificateCounterFinish<Q(!new)>(
    rootCandidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    questionCount:nat,
    interview:Interview<Q>,
    counterBase:nat,
    counter:nat)
  requires 1 <= interview.NodeCount()
  requires counter <= counterBase +
    (2 * interview.NodeCount() - 1) *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount)
  ensures counter <= counterBase + poly_VerifyCDPCCertificate(
    rootCandidates, privateQuestions, questionCount, interview)
{}

lemma BranchCounterFinish<Q(!new)>(
    rootCandidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    questionCount:nat,
    interview:Interview<Q>,
    counterBase:nat,
    counter:nat)
  requires counter <= counterBase +
    2 * interview.NodeCount() *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount)
  ensures counter <= counterBase + poly_CheckCDPCBranch(
    rootCandidates, privateQuestions, questionCount, interview)
{}

lemma BranchOwnCostFits(
    nodes:nat, nodeCost:nat, counterBase:nat, counter:nat)
  requires 1 <= nodes
  requires counter <= counterBase + nodeCost
  ensures counter <= counterBase + 2 * nodes * nodeCost
{}

method {:isolate_assertions} VerifyCDPCCertificateRec<Q(!new)>(
    rootCandidates:Set<Candidate<Q>>,
    candidates:Set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:Set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    ghost questionCount:nat,
    interview:Interview<Q>,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires rootCandidates.Valid()
  requires candidates.Valid()
  requires privateQuestions.Valid()
  requires candidates.Model() != {}
  requires candidates.Model() <= fitness.Keys
  requires candidates.Model() <= multiplicity.Keys
  requires candidates.Cardinality() <= rootCandidates.Cardinality()
  requires candidates.UBSize0() <= rootCandidates.UBSize0()
  requires forall candidate | candidate in candidates.Model() ::
    |candidate.Keys| <= questionCount
  decreases interview.NodeCount(), 0
  ensures accepted == CertificateCDPC(
    fitness, multiplicity, privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates.Model(), interview.Model())
  ensures counter <= counter_in + poly_VerifyCDPCCertificate(
    rootCandidates, privateQuestions, questionCount, interview)
{
  var isEnd:bool;
  isEnd, counter := interview.IsEnd(counter_in);
  if isEnd {
    var classificationAccepted:bool;
    classificationAccepted, counter := CheckClassification(
      candidates, fitness, multiplicity, fitnessLower, fitnessUpper,
      counter);
    var privacyAccepted:bool;
    privacyAccepted, counter := CheckPrivateSafe(
      candidates, privateQuestions, questionCount, multiplicity,
      privateLower, privateUpper, counter);
    accepted := classificationAccepted && privacyAccepted;
    reveal CertificateCDPC();
    reveal interview.NodeCount();
    reveal InterviewNodes();
    CDPCCandidateCostMonotonic(
      candidates, rootCandidates, privateQuestions, questionCount);
    assert interview.NodeCount() == 1;
    assert counter <= counter_in +
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount);
    VerifyCertificateCounterFinish(
      rootCandidates, privateQuestions, questionCount, interview,
      counter_in, counter);
    return accepted, counter;
  }

  var question:Q;
  question, counter := interview.Question(counter);
  var trueCandidates:Set<Candidate<Q>>;
  trueCandidates, counter := FilterCandidateSet(
    candidates, question, true, questionCount, counter);
  var falseCandidates:Set<Candidate<Q>>;
  falseCandidates, counter := FilterCandidateSet(
    candidates, question, false, questionCount, counter);
  var trueBranch:Interview<Q>;
  trueBranch, counter := interview.Branch(true, counter);
  var falseBranch:Interview<Q>;
  falseBranch, counter := interview.Branch(false, counter);

  assert trueCandidates.Model() <= candidates.Model();
  assert falseCandidates.Model() <= candidates.Model();
  if_smaller_then_less_cardinality(
    trueCandidates.Model(), candidates.Model());
  if_smaller_then_less_cardinality(
    falseCandidates.Model(), candidates.Model());
  assert trueCandidates.Cardinality() <= rootCandidates.Cardinality();
  assert falseCandidates.Cardinality() <= rootCandidates.Cardinality();
  assert trueCandidates.UBSize0() <= rootCandidates.UBSize0();
  assert falseCandidates.UBSize0() <= rootCandidates.UBSize0();
  CDPCCandidateCostMonotonic(
    candidates, rootCandidates, privateQuestions, questionCount);
  assert counter <= counter_in +
    cost_VerifyCDPCCertificateNode(
      rootCandidates, privateQuestions, questionCount);
  ghost var setupCounter := counter;

  var trueAccepted:bool;
  trueAccepted, counter := CheckCDPCBranch(
    rootCandidates, trueCandidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, questionCount, trueBranch, counter);
  ghost var afterTrueCounter := counter;
  var falseAccepted:bool;
  falseAccepted, counter := CheckCDPCBranch(
    rootCandidates, falseCandidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, questionCount, falseBranch, counter);
  accepted := trueAccepted && falseAccepted;

  reveal CertificateCDPC();
  assert trueCandidates.Model() ==
    FilterCandidates(candidates.Model(), question, true);
  assert falseCandidates.Model() ==
    FilterCandidates(candidates.Model(), question, false);
  reveal interview.NodeCount();
  reveal trueBranch.NodeCount();
  reveal falseBranch.NodeCount();
  reveal InterviewNodes();
  assert interview.NodeCount() ==
    1 + trueBranch.NodeCount() + falseBranch.NodeCount();
  assert afterTrueCounter <= setupCounter + poly_CheckCDPCBranch(
    rootCandidates, privateQuestions, questionCount, trueBranch);
  assert counter <= afterTrueCounter + poly_CheckCDPCBranch(
    rootCandidates, privateQuestions, questionCount, falseBranch);
  assert counter <= counter_in +
    cost_VerifyCDPCCertificateNode(
      rootCandidates, privateQuestions, questionCount) +
    2 * trueBranch.NodeCount() *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount) +
    2 * falseBranch.NodeCount() *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount);
  CertificateAskCostCombine(
    interview.NodeCount(), trueBranch.NodeCount(), falseBranch.NodeCount(),
    cost_VerifyCDPCCertificateNode(
      rootCandidates, privateQuestions, questionCount),
    counter_in, counter);
  VerifyCertificateCounterFinish(
    rootCandidates, privateQuestions, questionCount, interview,
    counter_in, counter);
}

method {:isolate_assertions} CheckCDPCBranch<Q(!new)>(
    rootCandidates:Set<Candidate<Q>>,
    candidates:Set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:Set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    ghost questionCount:nat,
    interview:Interview<Q>,
    ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  requires rootCandidates.Valid()
  requires candidates.Valid()
  requires privateQuestions.Valid()
  requires candidates.Model() <= fitness.Keys
  requires candidates.Model() <= multiplicity.Keys
  requires candidates.Cardinality() <= rootCandidates.Cardinality()
  requires candidates.UBSize0() <= rootCandidates.UBSize0()
  requires forall candidate | candidate in candidates.Model() ::
    |candidate.Keys| <= questionCount
  decreases interview.NodeCount(), 1
  ensures accepted == CDPCBranch(
    fitness, multiplicity, privateQuestions.Model(),
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates.Model(), interview.Model())
  ensures counter <= counter_in + poly_CheckCDPCBranch(
    rootCandidates, privateQuestions, questionCount, interview)
{
  var empty:bool;
  empty, counter := candidates.Empty(counter_in);
  if empty {
    accepted, counter := interview.IsEnd(counter);
    EmptyCDPCBranch(
      fitness, multiplicity, privateQuestions.Model(),
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      interview.Model());
    reveal interview.NodeCount();
    reveal InterviewNodes();
    assert 1 <= interview.NodeCount();
    assert counter <= counter_in +
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount);
    BranchOwnCostFits(
      interview.NodeCount(),
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount),
      counter_in, counter);
    BranchCounterFinish(
      rootCandidates, privateQuestions, questionCount, interview,
      counter_in, counter);
    return accepted, counter;
  }

  var privacyAccepted:bool;
  privacyAccepted, counter := CheckPrivateSafe(
    candidates, privateQuestions, questionCount, multiplicity,
    privateLower, privateUpper, counter);
  if !privacyAccepted {
    accepted := false;
    reveal CDPCBranch();
    reveal interview.NodeCount();
    reveal InterviewNodes();
    CDPCCandidateCostMonotonic(
      candidates, rootCandidates, privateQuestions, questionCount);
    assert 1 <= interview.NodeCount();
    assert counter <= counter_in +
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount);
    BranchOwnCostFits(
      interview.NodeCount(),
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount),
      counter_in, counter);
    BranchCounterFinish(
      rootCandidates, privateQuestions, questionCount, interview,
      counter_in, counter);
    return accepted, counter;
  }

  accepted, counter := VerifyCDPCCertificateRec(
    rootCandidates, candidates, fitness, multiplicity,
    privateQuestions, privateLower, privateUpper,
    fitnessLower, fitnessUpper, questionCount, interview, counter);
  reveal CDPCBranch();
  reveal interview.NodeCount();
  reveal InterviewNodes();
  CDPCCandidateCostMonotonic(
    candidates, rootCandidates, privateQuestions, questionCount);
  assert 1 <= interview.NodeCount();
  assert counter <= counter_in +
    cost_VerifyCDPCCertificateNode(
      rootCandidates, privateQuestions, questionCount) +
    (2 * interview.NodeCount() - 1) *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount);
  assert counter <= counter_in +
    2 * interview.NodeCount() *
      cost_VerifyCDPCCertificateNode(
        rootCandidates, privateQuestions, questionCount);
  BranchCounterFinish(
    rootCandidates, privateQuestions, questionCount, interview,
    counter_in, counter);
}


ghost function {:opaque} poly_VerifyCDPC<Q(!new)>(
    questions:Set<Q>,
    candidates:Set<Candidate<Q>>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
  ensures poly_VerifyCDPC(
    questions, candidates, privateQuestions, interview) ==
    poly_CheckInterviewFits(questions.Cardinality(), interview) +
    poly_VerifyCDPCCertificate(
      candidates, privateQuestions, questions.Cardinality(), interview)
{
  poly_CheckInterviewFits(questions.Cardinality(), interview) +
  poly_VerifyCDPCCertificate(
    candidates, privateQuestions, questions.Cardinality(), interview)
}
