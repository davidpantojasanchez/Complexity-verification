include "../Problems/CDPC.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"
include "../Auxiliary/Lemmas.dfy"

/*
Proof support for VerificationCDPC.dfy; no executable verification algorithm.
The verifier depends on these contracts, not on their proof details.
*/

// Weighted sums: enumeration independence, uniqueness, and iteration progress.

lemma MultisetCancellation<T>(common:multiset<T>, first:multiset<T>, second:multiset<T>)
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

lemma SequenceWeightedMassRemoveAt<Q(!new)>(
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
  assert values == prefix + ([values[index]] + suffix);
  SequenceWeightedMassConcat(prefix, [values[index]] + suffix, multiplicity);
  SequenceWeightedMassConcat(prefix, suffix, multiplicity);
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

lemma WeightedMassProgress<Q(!new)>(
    allCandidates:set<Candidate<Q>>,
    previousRemaining:set<Candidate<Q>>,
    remaining:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    multiplicity:map<Candidate<Q>, nat>,
    previousMass:nat,
    mass:nat)
  requires previousRemaining <= allCandidates
  requires candidate in previousRemaining
  requires remaining == previousRemaining - {candidate}
  requires allCandidates <= multiplicity.Keys
  requires WeightedMass(
    allCandidates - previousRemaining, multiplicity, previousMass)
  requires mass == previousMass + multiplicity[candidate]
  ensures WeightedMass(allCandidates - remaining, multiplicity, mass)
{
  assert candidate !in allCandidates - previousRemaining;
  WeightedMassAdd(
    allCandidates - previousRemaining, candidate,
    multiplicity, previousMass);
  assert allCandidates - remaining ==
    (allCandidates - previousRemaining) + {candidate};
}

lemma FitMassProgress<Q(!new)>(
    allCandidates:set<Candidate<Q>>,
    previousRemaining:set<Candidate<Q>>,
    remaining:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    previousMass:nat,
    mass:nat,
    isFit:bool)
  requires previousRemaining <= allCandidates
  requires candidate in previousRemaining
  requires remaining == previousRemaining - {candidate}
  requires allCandidates <= fitness.Keys
  requires allCandidates <= multiplicity.Keys
  requires isFit == fitness[candidate]
  requires mass == if isFit
                   then previousMass + multiplicity[candidate]
                   else previousMass
  requires WeightedMass(
    set element | element in allCandidates - previousRemaining &&
      element in fitness && fitness[element] :: element,
    multiplicity, previousMass)
  ensures WeightedMass(
    set element | element in allCandidates - remaining &&
      element in fitness && fitness[element] :: element,
    multiplicity, mass)
{
  ghost var previousFit :=
    set element | element in allCandidates - previousRemaining &&
      element in fitness && fitness[element] :: element;
  ghost var currentFit :=
    set element | element in allCandidates - remaining &&
      element in fitness && fitness[element] :: element;
  if isFit {
    assert candidate !in previousFit;
    WeightedMassAdd(previousFit, candidate, multiplicity, previousMass);
    assert currentFit == previousFit + {candidate};
  } else {
    assert currentFit == previousFit;
  }
}

lemma PrivateMassProgress<Q(!new)>(
    allCandidates:set<Candidate<Q>>,
    previousRemaining:set<Candidate<Q>>,
    remaining:set<Candidate<Q>>,
    candidate:Candidate<Q>,
    question:Q,
    multiplicity:map<Candidate<Q>, nat>,
    previousMass:nat,
    mass:nat,
    selected:bool)
  requires previousRemaining <= allCandidates
  requires candidate in previousRemaining
  requires remaining == previousRemaining - {candidate}
  requires allCandidates <= multiplicity.Keys
  requires selected ==
    (question in candidate && candidate[question])
  requires mass == if selected
                   then previousMass + multiplicity[candidate]
                   else previousMass
  requires WeightedMass(
    set element | element in allCandidates - previousRemaining &&
      question in element && element[question] :: element,
    multiplicity, previousMass)
  ensures WeightedMass(
    set element | element in allCandidates - remaining &&
      question in element && element[question] :: element,
    multiplicity, mass)
{
  ghost var previousPrivate :=
    set element | element in allCandidates - previousRemaining &&
      question in element && element[question] :: element;
  ghost var currentPrivate :=
    set element | element in allCandidates - remaining &&
      question in element && element[question] :: element;
  if selected {
    assert candidate !in previousPrivate;
    WeightedMassAdd(
      previousPrivate, candidate, multiplicity, previousMass);
    assert currentPrivate == previousPrivate + {candidate};
  } else {
    assert currentPrivate == previousPrivate;
  }
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

// Relational specifications can be checked using the unique computed masses.

lemma ClassificationFromMasses<Q(!new)>(
    candidates:set<Candidate<Q>>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, totalMass:nat, fitMass:nat,
    lower:real, upper:real)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires WeightedMass(candidates, multiplicity, totalMass)
  requires FitMass(candidates, fitness, multiplicity, fitMass)
  ensures ClassificationDecided(candidates, fitness, multiplicity, lower, upper) ==
    ((fitMass as real) <= lower * (totalMass as real) ||
     upper * (totalMass as real) <= (fitMass as real))
{
  reveal ClassificationDecided();
  if ClassificationDecided(candidates, fitness, multiplicity, lower, upper) {
    var semanticTotal:nat, semanticFit:nat :|
      WeightedMass(candidates, multiplicity, semanticTotal) &&
      FitMass(candidates, fitness, multiplicity, semanticFit) &&
      ((semanticFit as real) <= lower * (semanticTotal as real) ||
       upper * (semanticTotal as real) <= (semanticFit as real));
    WeightedMassUnique(candidates, multiplicity, totalMass, semanticTotal);
    FitMassUnique(candidates, fitness, multiplicity, fitMass, semanticFit);
  }
}

lemma PrivateQuestionFromMass<Q(!new)>(
    candidates:set<Candidate<Q>>, question:Q, multiplicity:map<Candidate<Q>, nat>,
    totalMass:nat, privateMass:nat, lower:real, upper:real)
  requires candidates <= multiplicity.Keys
  requires PrivateMass(candidates, question, multiplicity, privateMass)
  ensures (exists mass:nat | PrivateMass(candidates, question, multiplicity, mass) ::
    lower * (totalMass as real) <= (mass as real) <= upper * (totalMass as real)) ==
    (lower * (totalMass as real) <= (privateMass as real) <= upper * (totalMass as real))
{
  if exists mass:nat | PrivateMass(candidates, question, multiplicity, mass) ::
      lower * (totalMass as real) <= (mass as real) <= upper * (totalMass as real) {
    var mass:nat :| PrivateMass(candidates, question, multiplicity, mass) &&
      lower * (totalMass as real) <= (mass as real) <= upper * (totalMass as real);
    PrivateMassUnique(candidates, question, multiplicity, privateMass, mass);
  }
}

lemma PrivateSafeFromTotal<Q(!new)>(
    candidates:set<Candidate<Q>>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, totalMass:nat, lower:real, upper:real)
  requires candidates != {}
  requires candidates <= multiplicity.Keys
  requires WeightedMass(candidates, multiplicity, totalMass)
  ensures PrivateSafe(candidates, multiplicity, privateQuestions, lower, upper) ==
    (forall question | question in privateQuestions ::
      exists mass:nat | PrivateMass(candidates, question, multiplicity, mass) ::
        lower * (totalMass as real) <= (mass as real) <= upper * (totalMass as real))
{
  reveal PrivateSafe();
  if PrivateSafe(candidates, multiplicity, privateQuestions, lower, upper) {
    var semanticTotal:nat :| WeightedMass(candidates, multiplicity, semanticTotal) &&
      (forall question | question in privateQuestions ::
        exists mass:nat | PrivateMass(candidates, question, multiplicity, mass) ::
          lower * (semanticTotal as real) <= (mass as real) <= upper * (semanticTotal as real));
    WeightedMassUnique(candidates, multiplicity, totalMass, semanticTotal);
  }
}

// Symbolic operation budgets and polynomial cost bounds.

// Keep tree-cost arithmetic outside the quantified population proof context.
lemma TreeCostCombine(
    nodes:nat, trueNodes:nat, falseNodes:nat, nodeCost:nat, branchFactor:nat,
    counterBase:nat, setupCounter:nat, afterTrueCounter:nat, counter:nat)
  requires nodes == 1 + trueNodes + falseNodes
  requires setupCounter <= counterBase + nodeCost
  requires afterTrueCounter <= setupCounter + branchFactor * trueNodes * nodeCost
  requires counter <= afterTrueCounter + branchFactor * falseNodes * nodeCost
  ensures counter <= counterBase + (branchFactor * (nodes - 1) + 1) * nodeCost
{}

lemma BranchCostCombine(
    nodes:nat, nodeCost:nat, counterBase:nat, setupCounter:nat, counter:nat)
  requires 1 <= nodes
  requires setupCounter <= counterBase + nodeCost
  requires counter <= setupCounter + (2 * nodes - 1) * nodeCost
  ensures counter <= counterBase + 2 * nodes * nodeCost
{}

lemma BranchOwnCostFits(
    nodes:nat, nodeCost:nat, counterBase:nat, counter:nat)
  requires 1 <= nodes
  requires counter <= counterBase + nodeCost
  ensures counter <= counterBase + 2 * nodes * nodeCost
{}

ghost function poly_ComputeWeightedMass<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  cost_MapMapTCopyUniverse(candidates) + cost_MapMapTEmpty(candidates) +
  candidates.UBCardinality() *
    (cost_MapMapTPickKeyUniverse(candidates) +
     cost_MapMapTGetUniverse(multiplicity) +
     cost_MapMapTRemoveUniverse(candidates) +
     cost_MapMapTEmpty(candidates))
}

ghost function poly_FilterCandidates<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>):nat
{
  2 * cost_MapMapTCopyUniverse(candidates) +
  cost_MapMapTEmpty(candidates) +
  candidates.UBCardinality() *
    (cost_MapMapTPickKeyUniverse(candidates) +
     2 * (candidates.UBSize_Keys() + 1) +
     2 * cost_MapMapTRemoveUniverse(candidates) +
     cost_MapMapTEmpty(candidates))
}

ghost function poly_ComputeFitMass<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  cost_MapMapTCopyUniverse(candidates) + cost_MapMapTEmpty(candidates) +
  candidates.UBCardinality() *
    (cost_MapMapTPickKeyUniverse(candidates) +
     cost_MapMapTGetUniverse(fitness) +
     cost_MapMapTGetUniverse(multiplicity) +
     cost_MapMapTRemoveUniverse(candidates) +
     cost_MapMapTEmpty(candidates))
}

ghost function poly_ComputePrivateMass<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  cost_MapMapTCopyUniverse(candidates) + cost_MapMapTEmpty(candidates) +
  candidates.UBCardinality() *
    (cost_MapMapTPickKeyUniverse(candidates) +
     2 * (candidates.UBSize_Keys() + 1) +
     cost_MapMapTGetUniverse(multiplicity) +
     cost_MapMapTRemoveUniverse(candidates) +
     cost_MapMapTEmpty(candidates))
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

lemma LinearLoopBudgetBound(
    base:nat, step:nat, processed:nat, bound:nat)
  requires processed <= bound
  ensures LinearLoopBudget(base, step, processed) <=
          base + bound * step
{
  reveal LinearLoopBudget();
  mult_preserves_order(processed, step, bound, step);
}

ghost function poly_CheckClassification<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  poly_ComputeWeightedMass(candidates, multiplicity) +
  poly_ComputeFitMass(candidates, fitness, multiplicity) + 1
}

ghost function poly_CheckPrivateQuestion<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  poly_ComputePrivateMass(candidates, multiplicity) + 1
}

ghost function poly_CheckPrivateSafe<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    privateQuestions:Set<Q>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  poly_ComputeWeightedMass(candidates, multiplicity) +
  cost_SetCopyUniverse(privateQuestions) + cost_SetEmpty(privateQuestions) +
  privateQuestions.UBCardinality() *
    (cost_SetPick(privateQuestions) +
     poly_CheckPrivateQuestion(candidates, multiplicity) +
     cost_SetRemoveUniverse(privateQuestions) +
     cost_SetEmpty(privateQuestions))
}

ghost function cost_CheckInterviewFitsNode<Q(!new)>(
    rootQuestions:Map<Q, bool>):nat
{
  cost_InterviewIsEnd() + cost_InterviewQuestion() +
  cost_MapContainsKeyUniverse(rootQuestions) +
  cost_MapRemoveUniverse(rootQuestions) +
  2 * cost_InterviewBranch()
}

ghost function poly_CheckInterviewFits<Q(!new)>(
    rootQuestions:Map<Q, bool>, interview:Interview<Q>):nat
{
  interview.NodeCount() * cost_CheckInterviewFitsNode(rootQuestions)
}

ghost function cost_CDPCInterviewNode<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>):nat
{
  cost_InterviewIsEnd() + cost_InterviewQuestion() +
  2 * (fitness.UBSize_Keys() + 1) + 2 * cost_InterviewBranch()
}

lemma CDPCInterviewCostBound<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>, questions:Map<Q, bool>, interview:Interview<Q>)
  requires questions.UBSize() <= fitness.UBSize_Keys()
  ensures poly_CheckInterviewFits(questions, interview) <=
    interview.NodeCount() * cost_CDPCInterviewNode(fitness)
{
  mult_preserves_order(
    interview.NodeCount(), cost_CheckInterviewFitsNode(questions),
    interview.NodeCount(), cost_CDPCInterviewNode(fitness));
}

lemma CDPCCandidateCostMonotonic<Q(!new)>(
    smaller:Map_Map_T<Q, bool, bool>,
    larger:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>)
  requires in_universe_Map_Map_T(smaller, larger)
  ensures poly_ComputeWeightedMass(smaller, multiplicity) <=
          poly_ComputeWeightedMass(larger, multiplicity)
  ensures poly_ComputeFitMass(smaller, fitness, multiplicity) <=
          poly_ComputeFitMass(larger, fitness, multiplicity)
  ensures poly_ComputePrivateMass(smaller, multiplicity) <=
          poly_ComputePrivateMass(larger, multiplicity)
  ensures poly_FilterCandidates(smaller) <=
          poly_FilterCandidates(larger)
  ensures poly_CheckClassification(smaller, fitness, multiplicity) <=
          poly_CheckClassification(larger, fitness, multiplicity)
  ensures poly_CheckPrivateQuestion(smaller, multiplicity) <=
          poly_CheckPrivateQuestion(larger, multiplicity)
  ensures poly_CheckPrivateSafe(smaller, privateQuestions, multiplicity) <=
          poly_CheckPrivateSafe(larger, privateQuestions, multiplicity)
{
  in_universe_lemma_Map_Map_T(smaller, larger);
  assert cost_MapMapTCopyUniverse(smaller) <=
         cost_MapMapTCopyUniverse(larger);
  assert cost_MapMapTRemoveUniverse(smaller) <=
         cost_MapMapTRemoveUniverse(larger);
  assert cost_MapMapTPickKeyUniverse(smaller) <=
         cost_MapMapTPickKeyUniverse(larger);

  mult_preserves_order(
    smaller.UBCardinality(),
    cost_MapMapTPickKeyUniverse(smaller) +
      cost_MapMapTGetUniverse(multiplicity) +
      cost_MapMapTRemoveUniverse(smaller) +
      cost_MapMapTEmpty(smaller),
    larger.UBCardinality(),
    cost_MapMapTPickKeyUniverse(larger) +
      cost_MapMapTGetUniverse(multiplicity) +
      cost_MapMapTRemoveUniverse(larger) +
      cost_MapMapTEmpty(larger));
  mult_preserves_order(
    smaller.UBCardinality(),
    cost_MapMapTPickKeyUniverse(smaller) +
      cost_MapMapTGetUniverse(fitness) +
      cost_MapMapTGetUniverse(multiplicity) +
      cost_MapMapTRemoveUniverse(smaller) +
      cost_MapMapTEmpty(smaller),
    larger.UBCardinality(),
    cost_MapMapTPickKeyUniverse(larger) +
      cost_MapMapTGetUniverse(fitness) +
      cost_MapMapTGetUniverse(multiplicity) +
      cost_MapMapTRemoveUniverse(larger) +
      cost_MapMapTEmpty(larger));
  mult_preserves_order(
    smaller.UBCardinality(),
    cost_MapMapTPickKeyUniverse(smaller) +
      2 * (smaller.UBSize_Keys() + 1) +
      cost_MapMapTGetUniverse(multiplicity) +
      cost_MapMapTRemoveUniverse(smaller) +
      cost_MapMapTEmpty(smaller),
    larger.UBCardinality(),
    cost_MapMapTPickKeyUniverse(larger) +
      2 * (larger.UBSize_Keys() + 1) +
      cost_MapMapTGetUniverse(multiplicity) +
      cost_MapMapTRemoveUniverse(larger) +
      cost_MapMapTEmpty(larger));
  mult_preserves_order(
    smaller.UBCardinality(),
    cost_MapMapTPickKeyUniverse(smaller) +
      2 * (smaller.UBSize_Keys() + 1) +
      2 * cost_MapMapTRemoveUniverse(smaller) +
      cost_MapMapTEmpty(smaller),
    larger.UBCardinality(),
    cost_MapMapTPickKeyUniverse(larger) +
      2 * (larger.UBSize_Keys() + 1) +
      2 * cost_MapMapTRemoveUniverse(larger) +
      cost_MapMapTEmpty(larger));

  assert poly_ComputeWeightedMass(smaller, multiplicity) <=
         poly_ComputeWeightedMass(larger, multiplicity);
  assert poly_ComputeFitMass(smaller, fitness, multiplicity) <=
         poly_ComputeFitMass(larger, fitness, multiplicity);
  assert poly_ComputePrivateMass(smaller, multiplicity) <=
         poly_ComputePrivateMass(larger, multiplicity);
  assert poly_FilterCandidates(smaller) <= poly_FilterCandidates(larger);
  assert poly_CheckClassification(smaller, fitness, multiplicity) <=
         poly_CheckClassification(larger, fitness, multiplicity);
  assert poly_CheckPrivateQuestion(smaller, multiplicity) <=
         poly_CheckPrivateQuestion(larger, multiplicity);
  mult_preserves_order(
    privateQuestions.UBCardinality(),
    cost_SetPick(privateQuestions) +
      poly_CheckPrivateQuestion(smaller, multiplicity) +
      cost_SetRemoveUniverse(privateQuestions) +
      cost_SetEmpty(privateQuestions),
    privateQuestions.UBCardinality(),
    cost_SetPick(privateQuestions) +
      poly_CheckPrivateQuestion(larger, multiplicity) +
      cost_SetRemoveUniverse(privateQuestions) +
      cost_SetEmpty(privateQuestions));
}

ghost function cost_VerifyCDPCCertificateNode<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>):nat
{
  cost_InterviewIsEnd() + cost_InterviewQuestion() +
  2 * poly_FilterCandidates(rootCandidates) +
  2 * cost_InterviewBranch() + cost_MapMapTEmpty(rootCandidates) +
  poly_CheckClassification(rootCandidates, fitness, multiplicity) +
  poly_CheckPrivateSafe(rootCandidates, privateQuestions, multiplicity) + 1
}

ghost function {:opaque} poly_VerifyCDPCCertificate<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
  ensures poly_VerifyCDPCCertificate(
    rootCandidates, fitness, multiplicity, privateQuestions, interview) ==
    if interview.NodeCount() == 0 then 0
    else (2 * interview.NodeCount() - 1) * cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
{
  if interview.NodeCount() == 0 then 0
  else
    (2 * interview.NodeCount() - 1) * cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
}

ghost function {:opaque} poly_CheckCDPCBranch<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
  ensures poly_CheckCDPCBranch(
    rootCandidates, fitness, multiplicity, privateQuestions, interview) ==
    2 * interview.NodeCount() * cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
{
  2 * interview.NodeCount() * cost_VerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
}

ghost function {:opaque} poly_VerifyCDPC<Q(!new)>(
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
  ensures poly_VerifyCDPC(
    fitness, multiplicity, privateQuestions, interview) ==
    cost_MapMapTPickKeyUniverse(fitness) +
    interview.NodeCount() * cost_CDPCInterviewNode(fitness) +
    poly_VerifyCDPCCertificate(fitness, fitness, multiplicity, privateQuestions, interview)
{
  cost_MapMapTPickKeyUniverse(fitness) +
  interview.NodeCount() * cost_CDPCInterviewNode(fitness) +
  poly_VerifyCDPCCertificate(fitness, fitness, multiplicity, privateQuestions, interview)
}
