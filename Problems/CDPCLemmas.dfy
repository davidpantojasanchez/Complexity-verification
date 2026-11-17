include "../Foundations/CollectionLaws.dfy"
include "CDPC.dfy"

// Establish validity at the construction boundary using the candidate domains.
lemma cdpc_valid_instance_definition<Q(!new)>(instance:CDPCModel<Q>)
  requires instance.fitness.Keys == instance.multiplicity.Keys && instance.fitness.Keys != {}
  requires instance.privateQuestions <= instance.questions
  requires forall candidate | candidate in instance.fitness.Keys ::
    candidate.Keys == instance.questions && instance.multiplicity[candidate] > 0
  requires 0.0 <= instance.thresholds.privateLower <= instance.thresholds.privateUpper <= 1.0
  requires 0.0 <= instance.thresholds.fitnessLower <= instance.thresholds.fitnessUpper <= 1.0
  ensures CDPCValidInstance(instance)
{
}

lemma fit_sum_definition<Q(!new)>(candidates:set<Candidate<Q>>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>, sum:nat, filtered:set<Candidate<Q>>)
  requires candidates <= multiplicity.Keys
  requires filtered ==
    (set candidate | candidate in candidates &&
                     candidate in fitness && fitness[candidate] :: candidate)
  requires MultiplicitySum(filtered, multiplicity, sum)
  ensures FitSum(candidates, fitness, multiplicity, sum)
{
  reveal FitSum();
}

lemma private_sum_definition<Q(!new)>(candidates:set<Candidate<Q>>, privateQuestion:Q, multiplicity:map<Candidate<Q>, nat>, sum:nat, filtered:set<Candidate<Q>>)
  requires candidates <= multiplicity.Keys
  requires filtered ==
    (set candidate | candidate in candidates &&
                     privateQuestion in candidate && candidate[privateQuestion] :: candidate)
  requires MultiplicitySum(filtered, multiplicity, sum)
  ensures PrivateSum(candidates, privateQuestion, multiplicity, sum)
{
  reveal PrivateSum();
}

// Small proof-facing boundaries for the recursive definitions.
lemma multiplicity_sum_empty<Q(!new)>(multiplicity:map<Candidate<Q>, nat>)
  ensures MultiplicitySum({}, multiplicity, 0)
{
  reveal MultiplicitySum();
  var enumeration:seq<Candidate<Q>> := [];
  var empty:set<Candidate<Q>> := {};
  assert multiset(enumeration) == multiset(empty);
  reveal SequenceMultiplicitySum();
  assert 0 == SequenceMultiplicitySum(enumeration, multiplicity);
  assert exists enumeration':seq<Candidate<Q>> |
    multiset(enumeration') == multiset(empty) &&
    (forall candidate | candidate in enumeration' :: candidate in multiplicity.Keys) ::
    0 == SequenceMultiplicitySum(enumeration', multiplicity);
}

lemma multiplicity_sum_singleton<Q(!new)>(candidate:Candidate<Q>, multiplicity:map<Candidate<Q>, nat>)
  requires candidate in multiplicity.Keys
  ensures MultiplicitySum(
    {candidate}, multiplicity, multiplicity[candidate])
{
  reveal MultiplicitySum();
  assert multiset([candidate]) == multiset({candidate});
  reveal SequenceMultiplicitySum();
  assert SequenceMultiplicitySum([candidate], multiplicity) ==
         multiplicity[candidate];
  assert exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset({candidate}) &&
    (forall enumerated | enumerated in enumeration :: enumerated in multiplicity.Keys) ::
    multiplicity[candidate] ==
      SequenceMultiplicitySum(enumeration, multiplicity);
}

lemma {:isolate_assertions} cdpc_subtree_node_count_bound<Q(!new)>(
    fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, thresholds:CDPCThresholds<real>, candidates:set<Candidate<Q>>,
    remaining:set<Q>, tree:InterviewModel<Q>)
  decreases tree
  requires candidates <= fitness.Keys && candidates <= multiplicity.Keys
  requires forall c | c in candidates :: remaining <= c.Keys
  requires InterviewFits(tree, remaining)
  requires if candidates == {} then tree.End? else
    CDPCInterviewSemantics(fitness, multiplicity, privateQuestions,
      thresholds, candidates, tree)
  ensures InterviewNodes(tree) <= 2*|candidates|*|remaining| + 1
{
  reveal InterviewNodes(), InterviewFits(), CDPCInterviewSemantics(), CDPCBranch();
  if tree.Ask? {
    var q := tree.question;
    var left := FilterCandidates(candidates, q, true);
    var right := FilterCandidates(candidates, q, false);
    assert left + right == candidates;
    assert left * right == {};
    assert |left| + |right| == |candidates|;
    cdpc_subtree_node_count_bound(fitness, multiplicity, privateQuestions,
      thresholds,
      left, remaining - {q}, tree.trueBranch);
    cdpc_subtree_node_count_bound(fitness, multiplicity, privateQuestions,
      thresholds,
      right, remaining - {q}, tree.falseBranch);
    assert |remaining - {q}| == |remaining| - 1;
    cdpc_node_count_bound(|left|, |right|, |candidates|, |remaining|,
      InterviewNodes(tree.trueBranch), InterviewNodes(tree.falseBranch));
  }
}

lemma cdpc_node_count_bound(left:nat, right:nat, population:nat, questions:nat, a:nat, b:nat)
  requires a <= 2*left*(questions-1)+1
  requires b <= 2*right*(questions-1)+1
  requires left + right == population && population > 0 && questions > 0
  ensures 1+a+b <= 2*population*questions+1
{
  assert 2*left*(questions-1)+2*right*(questions-1) == 2*population*(questions-1);
  assert 2*population*(questions-1) == 2*population*questions-2*population;
}

lemma cdpc_certificate_node_count_bound<Q(!new)>(instance:CDPCModel<Q>, tree:InterviewModel<Q>)
  requires CDPCValidInstance(instance)
  requires CDPCCertificate(instance, tree)
  ensures InterviewNodes(tree) <= 2*|instance.fitness.Keys|*|instance.questions|+1
{
  cdpc_subtree_node_count_bound(instance.fitness, instance.multiplicity, instance.privateQuestions,
    instance.thresholds, instance.fitness.Keys, instance.questions, tree);
}


lemma cdpc_over_limit_not_certificate<Q(!new)>(instance:CDPCModel<Q>, tree:InterviewModel<Q>)
  requires CDPCValidInstance(instance)
  requires InterviewNodes(tree) > 2*|instance.fitness.Keys|*|instance.questions|+1
  ensures !CDPCCertificate(instance, tree)
{
  if CDPCCertificate(instance, tree) {
    cdpc_certificate_node_count_bound(instance, tree);
  }
}

// Enumeration and uniqueness laws shared by verification and reductions.
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
    cancellation_multiset(
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

// Disjoint populations compose without choosing a canonical enumeration.
lemma multiplicity_sum_disjoint_union<Q(!new)>(left:set<Candidate<Q>>, right:set<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>, leftSum:nat, rightSum:nat)
  requires left+right <= multiplicity.Keys && left !! right
  requires MultiplicitySum(left, multiplicity, leftSum)
  requires MultiplicitySum(right, multiplicity, rightSum)
  ensures MultiplicitySum(left+right, multiplicity, leftSum+rightSum)
{
  reveal MultiplicitySum();
  var first :| multiset(first) == multiset(left) &&
    (forall candidate | candidate in first :: candidate in multiplicity.Keys) &&
    leftSum == SequenceMultiplicitySum(first, multiplicity);
  var second :| multiset(second) == multiset(right) &&
    (forall candidate | candidate in second :: candidate in multiplicity.Keys) &&
    rightSum == SequenceMultiplicitySum(second, multiplicity);
  sequence_multiplicity_sum_concat(first, second, multiplicity);
  assert multiset(first+second) == multiset(left+right);
}

lemma multiplicity_sum_constant<Q(!new)>(candidates:set<Candidate<Q>>, multiplicity:map<Candidate<Q>, nat>, weight:nat)
  requires candidates <= multiplicity.Keys
  requires forall candidate | candidate in candidates :: multiplicity[candidate] == weight
  ensures MultiplicitySum(candidates, multiplicity, weight*|candidates|)
  decreases |candidates|
{
  if candidates == {} {
    multiplicity_sum_empty(multiplicity);
  } else {
    var candidate :| candidate in candidates;
    multiplicity_sum_constant(candidates-{candidate}, multiplicity, weight);
    multiplicity_sum_add(candidates-{candidate}, candidate, multiplicity, weight*|candidates-{candidate}|);
    assert candidates == (candidates-{candidate})+{candidate};
    assert |candidates| == |candidates-{candidate}|+1;
    multiplication_distributive(weight, |candidates-{candidate}|, 1);
  }
}

// Count original generators, not distinct answer maps. A whole fiber is removed
// at each induction step, so coincident generators keep all their multiplicity.
lemma multiplicity_sum_fibers<T(!new), Q(!new)>(items:set<T>, encode:T -> Candidate<Q>,
    multiplicity:map<Candidate<Q>, nat>, weight:nat)
  requires (set item | item in items :: encode(item)) <= multiplicity.Keys
  requires forall candidate | candidate in (set item | item in items :: encode(item)) ::
    multiplicity[candidate] == weight*|set item | item in items && encode(item) == candidate|
  ensures MultiplicitySum((set item | item in items :: encode(item)), multiplicity, weight*|items|)
  decreases |items|
{
  var image := set item | item in items :: encode(item);
  if items == {} {
    assert image == {};
    assert weight*|items| == 0;
    multiplicity_sum_empty(multiplicity);
  } else {
    var item :| item in items;
    var candidate := encode(item);
    var fiber := set member | member in items && encode(member) == candidate;
    var remaining := items-fiber;
    var remainingImage := set member | member in remaining :: encode(member);
    assert item in fiber;
    assert remainingImage == image-{candidate};
    forall other | other in remainingImage
      ensures multiplicity[other] == weight*|set member | member in remaining && encode(member) == other|
    {
      assert (set member | member in remaining && encode(member) == other) ==
        (set member | member in items && encode(member) == other);
    }
    multiplicity_sum_fibers(remaining, encode, multiplicity, weight);
    multiplicity_sum_add(remainingImage, candidate, multiplicity, weight*|remaining|);
    assert fiber !! remaining && fiber+remaining == items;
    assert |items| == |fiber|+|remaining|;
    assert image == remainingImage+{candidate};
    multiplication_distributive(weight, |remaining|, |fiber|);
  }
}
