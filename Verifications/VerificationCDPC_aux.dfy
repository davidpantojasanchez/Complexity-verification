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
lemma CostTreeCombine(
    nodes:nat, trueNodes:nat, falseNodes:nat, nodeCost:nat, branchFactor:nat,
    counterBase:nat, setupCounter:nat, afterTrueCounter:nat, counter:nat)
  requires afterTrueCounter <= setupCounter + branchFactor * trueNodes * nodeCost
  requires nodes == 1 + trueNodes + falseNodes
  requires setupCounter <= counterBase + nodeCost
  requires counter <= afterTrueCounter + branchFactor * falseNodes * nodeCost
  ensures counter <= counterBase + (branchFactor * (nodes - 1) + 1) * nodeCost
{}


lemma CostBranchCombine(
    nodes:nat, nodeCost:nat, counterBase:nat, setupCounter:nat, counter:nat)
  requires 1 <= nodes
  requires setupCounter <= counterBase + nodeCost
  requires counter <= setupCounter + (2 * nodes - 1) * nodeCost
  ensures counter <= counterBase + 2 * nodes * nodeCost
{}

lemma CostBranchOwnFits(
    nodes:nat, nodeCost:nat, counterBase:nat, counter:nat)
  requires 1 <= nodes
  requires counter <= counterBase + nodeCost
  ensures counter <= counterBase + 2 * nodes * nodeCost
{}

ghost function PolyComputeMultiplicitySum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  UCostCopy_Map_Map_T(candidates) + CostIsEmpty_Map_Map_T(candidates) +
  candidates.UCardinality() *
    (UCostPickKey_Map_Map_T(candidates) +
     UCostGet_Map_Map_T(multiplicity) +
     UCostRemove_Map_Map_T(candidates) +
     CostIsEmpty_Map_Map_T(candidates))
}

ghost function PolyFilterCandidates<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>):nat
{
  2 * UCostCopy_Map_Map_T(candidates) +
  CostIsEmpty_Map_Map_T(candidates) +
  candidates.UCardinality() *
    (UCostPickKey_Map_Map_T(candidates) +
     2 * (candidates.USize_Keys() + 1) +
     2 * UCostRemove_Map_Map_T(candidates) +
     CostIsEmpty_Map_Map_T(candidates))
}

ghost function PolyComputeFitSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  UCostCopy_Map_Map_T(candidates) + CostIsEmpty_Map_Map_T(candidates) +
  candidates.UCardinality() *
    (UCostPickKey_Map_Map_T(candidates) +
     UCostGet_Map_Map_T(fitness) +
     UCostGet_Map_Map_T(multiplicity) +
     UCostRemove_Map_Map_T(candidates) +
     CostIsEmpty_Map_Map_T(candidates))
}

ghost function PolyComputePrivateSum<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  UCostCopy_Map_Map_T(candidates) + CostIsEmpty_Map_Map_T(candidates) +
  candidates.UCardinality() *
    (UCostPickKey_Map_Map_T(candidates) +
     2 * (candidates.USize_Keys() + 1) +
     UCostGet_Map_Map_T(multiplicity) +
     UCostRemove_Map_Map_T(candidates) +
     CostIsEmpty_Map_Map_T(candidates))
}


ghost function PolyCheckClassification<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  PolyComputeMultiplicitySum(candidates, multiplicity) +
  PolyComputeFitSum(candidates, fitness, multiplicity) + 1
}

ghost function PolyCheckPrivateQuestion<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  PolyComputePrivateSum(candidates, multiplicity) + 1
}

ghost function PolyCheckPrivateSafe<Q(!new)>(
    candidates:Map_Map_T<Q, bool, bool>,
    privateQuestions:Set<Q>,
    multiplicity:Map_Map_T<Q, bool, nat>):nat
{
  PolyComputeMultiplicitySum(candidates, multiplicity) +
  CostIsEmpty_Set(privateQuestions) +
  privateQuestions.UCardinality() *
    (CostPick_Set(privateQuestions) +
     PolyCheckPrivateQuestion(candidates, multiplicity) +
     UCostRemove_Set(privateQuestions) +
     CostIsEmpty_Set(privateQuestions))
}

ghost function CostCheckInterviewFitsNode<Q(!new)>(
    rootQuestions:Set<Q>):nat
{
  CostIsEnd_Interview() + CostQuestion_Interview() +
  UCostContains_Set(rootQuestions) +
  UCostRemove_Set(rootQuestions) +
  2 * CostBranch_Interview()
}

lemma CostCDPCStructureBound<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>, questions:Set<Q>, interview:Interview<Q>)
  requires questions.Valid()
  requires interview.NodeCount() <= 2*fitness.Cardinality()*questions.Cardinality()+1
  ensures interview.NodeCount()*CostCheckInterviewFitsNode(questions) <=
    (2*fitness.Cardinality()*questions.USize0()+1)*CostCheckInterviewFitsNode(questions)
{
  assert questions.Cardinality() <= questions.USize0();
  MultiplicationPreservesOrder(fitness.Cardinality(), questions.Cardinality(),
    fitness.Cardinality(), questions.USize0());
  assert interview.NodeCount() <= 2*fitness.Cardinality()*questions.USize0()+1;
  MultiplicationPreservesOrder(interview.NodeCount(), CostCheckInterviewFitsNode(questions),
    2*fitness.Cardinality()*questions.USize0()+1,
    CostCheckInterviewFitsNode(questions));
}

lemma CostCDPCCandidateMonotonic<Q(!new)>(
    smaller:Map_Map_T<Q, bool, bool>,
    larger:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>)
  requires InUniverse_Map_Map_T(smaller, larger)
  ensures PolyComputeMultiplicitySum(smaller, multiplicity) <=
          PolyComputeMultiplicitySum(larger, multiplicity)
  ensures PolyComputeFitSum(smaller, fitness, multiplicity) <=
          PolyComputeFitSum(larger, fitness, multiplicity)
  ensures PolyComputePrivateSum(smaller, multiplicity) <=
          PolyComputePrivateSum(larger, multiplicity)
  ensures PolyFilterCandidates(smaller) <=
          PolyFilterCandidates(larger)
  ensures PolyCheckClassification(smaller, fitness, multiplicity) <=
          PolyCheckClassification(larger, fitness, multiplicity)
  ensures PolyCheckPrivateQuestion(smaller, multiplicity) <=
          PolyCheckPrivateQuestion(larger, multiplicity)
  ensures PolyCheckPrivateSafe(smaller, privateQuestions, multiplicity) <=
          PolyCheckPrivateSafe(larger, privateQuestions, multiplicity)
{
  InUniverseBounds_Map_Map_T(smaller, larger);
  assert UCostCopy_Map_Map_T(smaller) <=
         UCostCopy_Map_Map_T(larger);
  assert UCostRemove_Map_Map_T(smaller) <=
         UCostRemove_Map_Map_T(larger);
  assert UCostPickKey_Map_Map_T(smaller) <=
         UCostPickKey_Map_Map_T(larger);

  MultiplicationPreservesOrder(
    smaller.UCardinality(),
    UCostPickKey_Map_Map_T(smaller) +
      UCostGet_Map_Map_T(multiplicity) +
      UCostRemove_Map_Map_T(smaller) +
      CostIsEmpty_Map_Map_T(smaller),
    larger.UCardinality(),
    UCostPickKey_Map_Map_T(larger) +
      UCostGet_Map_Map_T(multiplicity) +
      UCostRemove_Map_Map_T(larger) +
      CostIsEmpty_Map_Map_T(larger));
  MultiplicationPreservesOrder(
    smaller.UCardinality(),
    UCostPickKey_Map_Map_T(smaller) +
      UCostGet_Map_Map_T(fitness) +
      UCostGet_Map_Map_T(multiplicity) +
      UCostRemove_Map_Map_T(smaller) +
      CostIsEmpty_Map_Map_T(smaller),
    larger.UCardinality(),
    UCostPickKey_Map_Map_T(larger) +
      UCostGet_Map_Map_T(fitness) +
      UCostGet_Map_Map_T(multiplicity) +
      UCostRemove_Map_Map_T(larger) +
      CostIsEmpty_Map_Map_T(larger));
  MultiplicationPreservesOrder(
    smaller.UCardinality(),
    UCostPickKey_Map_Map_T(smaller) +
      2 * (smaller.USize_Keys() + 1) +
      UCostGet_Map_Map_T(multiplicity) +
      UCostRemove_Map_Map_T(smaller) +
      CostIsEmpty_Map_Map_T(smaller),
    larger.UCardinality(),
    UCostPickKey_Map_Map_T(larger) +
      2 * (larger.USize_Keys() + 1) +
      UCostGet_Map_Map_T(multiplicity) +
      UCostRemove_Map_Map_T(larger) +
      CostIsEmpty_Map_Map_T(larger));
  MultiplicationPreservesOrder(
    smaller.UCardinality(),
    UCostPickKey_Map_Map_T(smaller) +
      2 * (smaller.USize_Keys() + 1) +
      2 * UCostRemove_Map_Map_T(smaller) +
      CostIsEmpty_Map_Map_T(smaller),
    larger.UCardinality(),
    UCostPickKey_Map_Map_T(larger) +
      2 * (larger.USize_Keys() + 1) +
      2 * UCostRemove_Map_Map_T(larger) +
      CostIsEmpty_Map_Map_T(larger));

  assert PolyComputeMultiplicitySum(smaller, multiplicity) <=
         PolyComputeMultiplicitySum(larger, multiplicity);
  assert PolyComputeFitSum(smaller, fitness, multiplicity) <=
         PolyComputeFitSum(larger, fitness, multiplicity);
  assert PolyComputePrivateSum(smaller, multiplicity) <=
         PolyComputePrivateSum(larger, multiplicity);
  assert PolyFilterCandidates(smaller) <= PolyFilterCandidates(larger);
  assert PolyCheckClassification(smaller, fitness, multiplicity) <=
         PolyCheckClassification(larger, fitness, multiplicity);
  assert PolyCheckPrivateQuestion(smaller, multiplicity) <=
         PolyCheckPrivateQuestion(larger, multiplicity);
  MultiplicationPreservesOrder(
    privateQuestions.UCardinality(),
    CostPick_Set(privateQuestions) +
      PolyCheckPrivateQuestion(smaller, multiplicity) +
      UCostRemove_Set(privateQuestions) +
      CostIsEmpty_Set(privateQuestions),
    privateQuestions.UCardinality(),
    CostPick_Set(privateQuestions) +
      PolyCheckPrivateQuestion(larger, multiplicity) +
      UCostRemove_Set(privateQuestions) +
      CostIsEmpty_Set(privateQuestions));
}

// Internal instance budget in collection measures; no tree argument.
ghost function CostCountInterviewNode():nat
{
  CostIsEnd_Interview() + 2*CostBranch_Interview()
}

ghost function {:opaque} {:isolate_assertions} PolyVerifyCDPC<Q(!new)>(fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>, questions:Set<Q>):(cost:nat)
  ensures cost == (var b := 2*fitness.Cardinality()*questions.USize0()+1;
    CostCount_Map_Map_T(fitness) + CostCount_Set(questions) + (b+1)*CostCountInterviewNode() +
    b*CostCheckInterviewFitsNode(questions) +
    2*b*CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions))
{
  var b := 2*fitness.Cardinality()*questions.USize0()+1;
  CostCount_Map_Map_T(fitness) + CostCount_Set(questions) + (b+1)*CostCountInterviewNode() +
  b*CostCheckInterviewFitsNode(questions) +
    2*b*CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions)
}

// Fixed numerical envelope; n bounds candidates, questions and private questions.
ghost function PolyCDPCVerificationNode(n:nat):nat
{
  var c := n*n+1;
  var d := n+1;
  var sum := c+1+n*(d+2*c+1);
  var filter := 2*c+1+n*(3*d+2*c+1);
  var fit := c+1+n*(d+3*c+1);
  var privateSum := c+1+n*(3*d+2*c+1);
  6+2*filter+(sum+fit+1)+(sum+1+n*(privateSum+n+4))
}

ghost function PolyCDPCVerification(n:nat):nat
{
  var nodes := 2*n*n+1;
  2 + (nodes+1)*CostCountInterviewNode() +
    nodes*(2*n+6) + 2*nodes*PolyCDPCVerificationNode(n)
}

lemma {:isolate_assertions} CostCDPCVerificationBound<Q(!new)>(
    fitness:Map_Map_T<Q, bool, bool>, multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>, questions:Set<Q>, n:nat)
  requires Init_Set(questions) && Init_Map_Map_T(fitness) && Init_Map_Map_T(multiplicity) && Init_Set(privateQuestions)
  requires fitness.Cardinality() <= n && multiplicity.Cardinality() <= n
  requires privateQuestions.Cardinality() <= n
  requires fitness.USize_Keys() <= n && multiplicity.USize_Keys() <= n
  requires questions.Cardinality() <= n
  ensures PolyVerifyCDPC(fitness, multiplicity, privateQuestions, questions) <= PolyCDPCVerification(n)
{
  assert questions.USize0() == questions.Cardinality();
  MultiplicationPreservesOrder(fitness.Cardinality(), fitness.USize_Keys(), n, n);
  MultiplicationPreservesOrder(fitness.Cardinality(), questions.USize0(), n, n);
  MultiplicationPreservesOrder(multiplicity.Cardinality(), multiplicity.USize_Keys(), n, n);
  var c := n*n+1;
  var d := n+1;
  var sum := c+1+n*(d+2*c+1);
  var filter := 2*c+1+n*(3*d+2*c+1);
  var fit := c+1+n*(d+3*c+1);
  var privateSum := c+1+n*(3*d+2*c+1);
  MultiplicationPreservesOrder(fitness.UCardinality(),
    UCostPickKey_Map_Map_T(fitness)+UCostGet_Map_Map_T(multiplicity)+
      UCostRemove_Map_Map_T(fitness)+1, n, d+2*c+1);
  assert PolyComputeMultiplicitySum(fitness, multiplicity) <= sum;
  MultiplicationPreservesOrder(fitness.UCardinality(),
    UCostPickKey_Map_Map_T(fitness)+2*(fitness.USize_Keys()+1)+
      2*UCostRemove_Map_Map_T(fitness)+1, n, 3*d+2*c+1);
  assert PolyFilterCandidates(fitness) <= filter;
  MultiplicationPreservesOrder(fitness.UCardinality(),
    UCostPickKey_Map_Map_T(fitness)+UCostGet_Map_Map_T(fitness)+
      UCostGet_Map_Map_T(multiplicity)+UCostRemove_Map_Map_T(fitness)+1,
    n, d+3*c+1);
  assert PolyComputeFitSum(fitness, fitness, multiplicity) <= fit;
  MultiplicationPreservesOrder(fitness.UCardinality(),
    UCostPickKey_Map_Map_T(fitness)+2*(fitness.USize_Keys()+1)+
      UCostGet_Map_Map_T(multiplicity)+UCostRemove_Map_Map_T(fitness)+1,
    n, 3*d+2*c+1);
  assert PolyComputePrivateSum(fitness, multiplicity) <= privateSum;
  MultiplicationPreservesOrder(privateQuestions.UCardinality(),
    PolyComputePrivateSum(fitness, multiplicity)+privateQuestions.USize0()+4,
    n, privateSum+n+4);
  assert CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions) <=
    PolyCDPCVerificationNode(n);
  MultiplicationAssociative(2, fitness.Cardinality(), questions.USize0());
  MultiplicationAssociative(2, n, n);
  assert 2*fitness.Cardinality()*questions.USize0()+1 <= 2*n*n+1;
  MultiplicationPreservesOrder(2*fitness.Cardinality()*questions.USize0()+1,
    CostCheckInterviewFitsNode(questions),
    2*n*n+1, 2*n+6);
  MultiplicationPreservesOrder(2*(2*fitness.Cardinality()*questions.USize0()+1),
    CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions),
    2*(2*n*n+1), PolyCDPCVerificationNode(n));
}

lemma CostCDPCCheckingBound<Q(!new)>(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>, interview:Interview<Q>)
  requires interview.NodeCount() <= 2*fitness.Cardinality()*questions.USize0()+1
  ensures PolyVerifyCDPCCertificate(fitness, fitness, multiplicity, privateQuestions, interview) <=
    2*(2*fitness.Cardinality()*questions.USize0()+1)*
      CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions)
{
  if interview.NodeCount() > 0 {
    MultiplicationPreservesOrder(2*interview.NodeCount()-1,
      CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions),
      2*(2*fitness.Cardinality()*questions.USize0()+1),
      CostVerifyCDPCCertificateNode(fitness, fitness, multiplicity, privateQuestions));
  }
}

ghost function CostVerifyCDPCCertificateNode<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>):nat
{
  CostIsEnd_Interview() + CostQuestion_Interview() +
  2 * PolyFilterCandidates(rootCandidates) +
  2 * CostBranch_Interview() + CostIsEmpty_Map_Map_T(rootCandidates) +
  PolyCheckClassification(rootCandidates, fitness, multiplicity) +
  PolyCheckPrivateSafe(rootCandidates, privateQuestions, multiplicity) + 1
}

ghost function {:opaque} PolyVerifyCDPCCertificate<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
  ensures PolyVerifyCDPCCertificate(
    rootCandidates, fitness, multiplicity, privateQuestions, interview) ==
    if interview.NodeCount() == 0 then 0
    else (2 * interview.NodeCount() - 1) * CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
{
  if interview.NodeCount() == 0 then 0
  else
    (2 * interview.NodeCount() - 1) * CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
}

ghost function {:opaque} PolyCheckCDPCBranch<Q(!new)>(
    rootCandidates:Map_Map_T<Q, bool, bool>,
    fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>,
    privateQuestions:Set<Q>,
    interview:Interview<Q>):nat
  ensures PolyCheckCDPCBranch(
    rootCandidates, fitness, multiplicity, privateQuestions, interview) ==
    2 * interview.NodeCount() * CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
{
  2 * interview.NodeCount() * CostVerifyCDPCCertificateNode(rootCandidates, fitness, multiplicity, privateQuestions)
}
