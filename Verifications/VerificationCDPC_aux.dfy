include "../Problems/CDPC.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Map.dfy"
include "../Auxiliary/Lemmas.dfy"

/*
Proof support for VerificationCDPC.dfy
*/

// Multiplicity-based sums: enumeration independence, uniqueness, and iteration progress.

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

lemma SequenceMultiplicitySumConcat<Q(!new)>(
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
    SequenceMultiplicitySumConcat(left[1..], right, multiplicity);
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

lemma SequenceMultiplicitySumRemoveAt<Q(!new)>(
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
  SequenceMultiplicitySumConcat(prefix, [values[index]] + suffix, multiplicity);
  SequenceMultiplicitySumConcat(prefix, suffix, multiplicity);
}

lemma SequenceMultiplicitySumPermutation<Q(!new)>(
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
    MultisetCancellation(
      multiset{candidate}, multiset(first[1..]), multiset(secondWithout));
    assert forall element | element in first[1..] + secondWithout ::
      element in multiplicity.Keys;
    SequenceMultiplicitySumPermutation(first[1..], secondWithout, multiplicity);
    SequenceMultiplicitySumRemoveAt(second, index, multiplicity);
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

lemma MultiplicitySumUnique<Q(!new)>(
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
  SequenceMultiplicitySumPermutation(firstEnumeration, secondEnumeration, multiplicity);
}

lemma MultiplicitySumAdd<Q(!new)>(
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
  SequenceMultiplicitySumConcat(enumeration, [candidate], multiplicity);
  assert multiset(enumeration + [candidate]) ==
         multiset(candidates + {candidate});
}

lemma MultiplicitySumProgress<Q(!new)>(
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
  MultiplicitySumAdd(
    allCandidates - previousRemaining, candidate,
    multiplicity, previousSum);
  assert allCandidates - remaining ==
    (allCandidates - previousRemaining) + {candidate};
}

lemma FitSumProgress<Q(!new)>(
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
    MultiplicitySumAdd(previousFit, candidate, multiplicity, previousSum);
    assert currentFit == previousFit + {candidate};
  } else {
    assert currentFit == previousFit;
  }
}

lemma PrivateSumProgress<Q(!new)>(
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
    MultiplicitySumAdd(
      previousPrivate, candidate, multiplicity, previousSum);
    assert currentPrivate == previousPrivate + {candidate};
  } else {
    assert currentPrivate == previousPrivate;
  }
}

lemma FitSumUnique<Q(!new)>(
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
  MultiplicitySumUnique(
    set candidate | candidate in candidates &&
                    candidate in fitness && fitness[candidate] :: candidate,
    multiplicity, first, second);
}

lemma PrivateSumUnique<Q(!new)>(
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
  MultiplicitySumUnique(
    set candidate | candidate in candidates &&
                    question in candidate && candidate[question] :: candidate,
    multiplicity, first, second);
}

// Relational specifications can be checked using the unique computed sums.

lemma ClassificationFromSums<Q(!new)>(
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
    MultiplicitySumUnique(candidates, multiplicity, totalSum, semanticTotal);
    FitSumUnique(candidates, fitness, multiplicity, fitSum, semanticFit);
  }
}

lemma PrivateQuestionFromSum<Q(!new)>(
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
    PrivateSumUnique(candidates, question, multiplicity, privateSum, sum);
  }
}

lemma PrivateSafeFromTotal<Q(!new)>(
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
    MultiplicitySumUnique(candidates, multiplicity, totalSum, semanticTotal);
  }
}

// Symbolic operation budgets and polynomial cost bounds.

// Keep tree-cost arithmetic outside the quantified population proof context.
lemma TreeCostCombine(
    nodes:nat, trueNodes:nat, falseNodes:nat, nodeCost:nat, branchFactor:nat,
    counterBase:nat, setupCounter:nat, afterTrueCounter:nat, counter:nat)
  requires afterTrueCounter <= setupCounter + branchFactor * trueNodes * nodeCost
  requires nodes == 1 + trueNodes + falseNodes
  requires setupCounter <= counterBase + nodeCost
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

ghost function poly_ComputeMultiplicitySum<Q(!new)>(
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

ghost function poly_ComputeFitSum<Q(!new)>(
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

ghost function poly_ComputePrivateSum<Q(!new)>(
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


ghost function poly_CheckClassification<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  poly_ComputeMultiplicitySum(candidates, multiplicity) +
  poly_ComputeFitSum(candidates, fitness, multiplicity) + 1
}

ghost function poly_CheckPrivateQuestion<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  poly_ComputePrivateSum(candidates, multiplicity) + 1
}

ghost function poly_CheckPrivateSafe<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    privateQuestions:Set<Q>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  poly_ComputeMultiplicitySum(candidates, multiplicity) +
  cost_SetEmpty(privateQuestions) +
  privateQuestions.UBCardinality() *
    (cost_SetPick(privateQuestions) +
     poly_CheckPrivateQuestion(candidates, multiplicity) +
     cost_SetRemoveUniverse(privateQuestions) +
     cost_SetEmpty(privateQuestions))
}

ghost function cost_CheckInterviewFitsNode<Q(!new)>(
    rootQuestions:Set<Q>):nat
{
  cost_InterviewIsEnd() + cost_InterviewQuestion() +
  cost_SetContainsUniverse(rootQuestions) +
  cost_SetRemoveUniverse(rootQuestions) +
  2 * cost_InterviewBranch()
}

lemma CDPCStructureCostBound<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>, questions:Set<Q>, interview:Interview<Q>)
  requires questions.Valid()
  requires interview.NodeCount() <= 2*fitness.Cardinality()*questions.Cardinality()+1
  ensures interview.NodeCount()*cost_CheckInterviewFitsNode(questions) <=
    (2*fitness.Cardinality()*questions.UBSize0()+1)*cost_CheckInterviewFitsNode(questions)
{
  assert questions.Cardinality() <= questions.UBSize0();
  mult_preserves_order(fitness.Cardinality(), questions.Cardinality(),
    fitness.Cardinality(), questions.UBSize0());
  assert interview.NodeCount() <= 2*fitness.Cardinality()*questions.UBSize0()+1;
  mult_preserves_order(interview.NodeCount(), cost_CheckInterviewFitsNode(questions),
    2*fitness.Cardinality()*questions.UBSize0()+1,
    cost_CheckInterviewFitsNode(questions));
}

lemma CDPCCandidateCostMonotonic<Q(!new)>(
    smaller:Map_Map_T<Q, bool, bool>,
    larger:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>)
  requires in_universe_Map_Map_T(smaller, larger)
  ensures poly_ComputeMultiplicitySum(smaller, multiplicity) <=
          poly_ComputeMultiplicitySum(larger, multiplicity)
  ensures poly_ComputeFitSum(smaller, fitness, multiplicity) <=
          poly_ComputeFitSum(larger, fitness, multiplicity)
  ensures poly_ComputePrivateSum(smaller, multiplicity) <=
          poly_ComputePrivateSum(larger, multiplicity)
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

  assert poly_ComputeMultiplicitySum(smaller, multiplicity) <=
         poly_ComputeMultiplicitySum(larger, multiplicity);
  assert poly_ComputeFitSum(smaller, fitness, multiplicity) <=
         poly_ComputeFitSum(larger, fitness, multiplicity);
  assert poly_ComputePrivateSum(smaller, multiplicity) <=
         poly_ComputePrivateSum(larger, multiplicity);
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

// Internal instance budget in collection measures; no tree argument.
ghost function {:opaque} {:isolate_assertions} poly_VerifyCDPC<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>, questions:Set<Q>):(cost:nat)
  ensures cost == (var b := 2*fitness.Cardinality()*questions.UBSize0()+1;
    b*cost_CheckInterviewFitsNode(questions) +
    2*b*cost_VerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions))
{
  var b := 2*fitness.Cardinality()*questions.UBSize0()+1;
  b*cost_CheckInterviewFitsNode(questions) +
    2*b*cost_VerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions)
}

// Fixed numerical envelope; n bounds candidates, questions and private questions.
ghost function CDPCVerificationNodePolynomial(n:nat):nat
{
  var c := n*n+1;
  var d := n+1;
  var sum := c+1+n*(d+2*c+1);
  var filter := 2*c+1+n*(3*d+2*c+1);
  var fit := c+1+n*(d+3*c+1);
  var privateSum := c+1+n*(3*d+2*c+1);
  6+2*filter+(sum+fit+1)+(sum+1+n*(privateSum+n+4))
}

ghost function CDPCVerificationPolynomial(n:nat):nat
{
  var nodes := 2*n*n+1;
  nodes*(2*n+6) + 2*nodes*CDPCVerificationNodePolynomial(n)
}

lemma {:isolate_assertions} CDPCVerificationCostBound<Q(!new)>(
    fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, questions:Set<Q>, n:nat)
  requires init_Set(questions) && init_Map_Map_T(fitness) && init_Map_Map_T(multiplicity) && init_Set(privateQuestions)
  requires fitness.Cardinality() <= n && multiplicity.Cardinality() <= n
  requires privateQuestions.Cardinality() <= n
  requires fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
  requires questions.Cardinality() <= n
  ensures poly_VerifyCDPC(fitness, multiplicity, privateQuestions, questions) <= CDPCVerificationPolynomial(n)
{
  assert questions.UBSize0() == questions.Cardinality();
  mult_preserves_order(fitness.Cardinality(), fitness.UBSize_Keys(), n, n);
  mult_preserves_order(fitness.Cardinality(), questions.UBSize0(), n, n);
  mult_preserves_order(multiplicity.Cardinality(), multiplicity.UBSize_Keys(), n, n);
  var c := n*n+1;
  var d := n+1;
  var sum := c+1+n*(d+2*c+1);
  var filter := 2*c+1+n*(3*d+2*c+1);
  var fit := c+1+n*(d+3*c+1);
  var privateSum := c+1+n*(3*d+2*c+1);
  mult_preserves_order(fitness.UBCardinality(),
    cost_MapMapTPickKeyUniverse(fitness)+cost_MapMapTGetUniverse(multiplicity)+
      cost_MapMapTRemoveUniverse(fitness)+1, n, d+2*c+1);
  assert poly_ComputeMultiplicitySum(fitness, multiplicity) <= sum;
  mult_preserves_order(fitness.UBCardinality(),
    cost_MapMapTPickKeyUniverse(fitness)+2*(fitness.UBSize_Keys()+1)+
      2*cost_MapMapTRemoveUniverse(fitness)+1, n, 3*d+2*c+1);
  assert poly_FilterCandidates(fitness) <= filter;
  mult_preserves_order(fitness.UBCardinality(),
    cost_MapMapTPickKeyUniverse(fitness)+cost_MapMapTGetUniverse(fitness)+
      cost_MapMapTGetUniverse(multiplicity)+cost_MapMapTRemoveUniverse(fitness)+1,
    n, d+3*c+1);
  assert poly_ComputeFitSum(fitness, fitness, multiplicity) <= fit;
  mult_preserves_order(fitness.UBCardinality(),
    cost_MapMapTPickKeyUniverse(fitness)+2*(fitness.UBSize_Keys()+1)+
      cost_MapMapTGetUniverse(multiplicity)+cost_MapMapTRemoveUniverse(fitness)+1,
    n, 3*d+2*c+1);
  assert poly_ComputePrivateSum(fitness, multiplicity) <= privateSum;
  mult_preserves_order(privateQuestions.UBCardinality(),
    poly_ComputePrivateSum(fitness, multiplicity)+privateQuestions.UBSize0()+4,
    n, privateSum+n+4);
  assert cost_VerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions) <=
    CDPCVerificationNodePolynomial(n);
  associativity(2, fitness.Cardinality(), questions.UBSize0());
  associativity(2, n, n);
  assert 2*fitness.Cardinality()*questions.UBSize0()+1 <= 2*n*n+1;
  mult_preserves_order(2*fitness.Cardinality()*questions.UBSize0()+1,
    cost_CheckInterviewFitsNode(questions),
    2*n*n+1, 2*n+6);
  mult_preserves_order(2*(2*fitness.Cardinality()*questions.UBSize0()+1),
    cost_VerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions),
    2*(2*n*n+1), CDPCVerificationNodePolynomial(n));
}

lemma CDPCCheckingCostBound<Q(!new)>(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>, interview:Interview<Q>)
  requires interview.NodeCount() <= 2*fitness.Cardinality()*questions.UBSize0()+1
  ensures poly_VerifyCDPCCertificate(fitness, fitness, multiplicity, privateQuestions, interview) <=
    2*(2*fitness.Cardinality()*questions.UBSize0()+1)*
      cost_VerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions)
{
  if interview.NodeCount() > 0 {
    mult_preserves_order(2*interview.NodeCount()-1,
      cost_VerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions),
      2*(2*fitness.Cardinality()*questions.UBSize0()+1),
      cost_VerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions));
  }
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
