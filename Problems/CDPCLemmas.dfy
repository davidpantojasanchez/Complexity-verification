include "CDPC.dfy"

// Package the direct validity clauses for construction proofs.
lemma cdpc_valid_instance_definition<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    privateLower:real, privateUpper:real, fitnessLower:real, fitnessUpper:real)
  requires fitness.Keys == multiplicity.Keys
  requires fitness.Keys != {}
  requires privateQuestions <= questions
  requires forall candidate | candidate in fitness.Keys ::
    candidate.Keys == questions && multiplicity[candidate] > 0
  requires 0.0 <= privateLower <= privateUpper <= 1.0
  requires 0.0 <= fitnessLower <= fitnessUpper <= 1.0
  ensures CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
{
  reveal CDPCValidInstance();
}

// In a valid instance the explicit component agrees with every candidate domain,
// preserving the representative-based interpretation without a second source of truth.
lemma cdpc_valid_instance_questions_determined<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    privateLower:real, privateUpper:real, fitnessLower:real, fitnessUpper:real,
    candidate:Candidate<Q>)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires candidate in fitness.Keys
  ensures candidate.Keys == questions
{
  reveal CDPCValidInstance();
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

lemma multiplicity_sum_pair<Q(!new)>(first:Candidate<Q>, second:Candidate<Q>, multiplicity:map<Candidate<Q>, nat>)
  requires first != second
  requires first in multiplicity.Keys
  requires second in multiplicity.Keys
  ensures MultiplicitySum(
    {first, second}, multiplicity,
    multiplicity[first] + multiplicity[second])
{
  reveal MultiplicitySum();
  assert multiset([first, second]) == multiset({first, second});
  reveal SequenceMultiplicitySum();
  assert SequenceMultiplicitySum([], multiplicity) == 0;
  assert SequenceMultiplicitySum([second], multiplicity) ==
         multiplicity[second];
  assert SequenceMultiplicitySum([first, second], multiplicity) ==
         multiplicity[first] + multiplicity[second];
  assert exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset({first, second}) &&
    (forall candidate | candidate in enumeration :: candidate in multiplicity.Keys) ::
    multiplicity[first] + multiplicity[second] ==
        SequenceMultiplicitySum(enumeration, multiplicity);
}

lemma empty_cdpc_branch<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    interview:InterviewModel<Q>)
  ensures CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    {}, interview) == interview.End?
{
  reveal CDPCBranch();
}

lemma cdpc_branch_step<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>,
    interview:InterviewModel<Q>)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, interview)
  ensures PrivateSafe(candidates, multiplicity, privateQuestions,
                      privateLower, privateUpper)
  ensures CDPCInterviewSemantics(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, interview)
{
  reveal CDPCBranch();
}

lemma cdpc_end_step<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires CDPCInterviewSemantics(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, End)
  ensures PrivateSafe(candidates, multiplicity, privateQuestions,
                      privateLower, privateUpper)
  ensures ClassificationDecided(candidates, fitness, multiplicity,
                                fitnessLower, fitnessUpper)
{
  reveal CDPCInterviewSemantics();
}

lemma cdpc_ask_step<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>,
    interview:InterviewModel<Q>)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires interview.Ask?
  requires CDPCInterviewSemantics(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, interview)
  ensures CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    FilterCandidates(candidates, interview.question, true),
    interview.trueBranch)
  ensures CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    FilterCandidates(candidates, interview.question, false),
    interview.falseBranch)
{
  reveal CDPCInterviewSemantics();
}

lemma {:isolate_assertions} cdpc_subtree_size_bound<Q(!new)>(
    fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, candidates:set<Candidate<Q>>,
    remaining:set<Q>, tree:InterviewModel<Q>)
  decreases tree
  requires candidates <= fitness.Keys && candidates <= multiplicity.Keys
  requires forall c | c in candidates :: remaining <= c.Keys
  requires InterviewFits(tree, remaining)
  requires if candidates == {} then tree.End? else
    CDPCInterviewSemantics(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper, candidates, tree)
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
    cdpc_subtree_size_bound(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      left, remaining - {q}, tree.trueBranch);
    cdpc_subtree_size_bound(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      right, remaining - {q}, tree.falseBranch);
    assert |remaining - {q}| == |remaining| - 1;
    cdpc_node_budget(|left|, |right|, |candidates|, |remaining|,
      InterviewNodes(tree.trueBranch), InterviewNodes(tree.falseBranch));
  }
}

lemma cdpc_node_budget(left:nat, right:nat, population:nat, questions:nat, a:nat, b:nat)
  requires a <= 2*left*(questions-1)+1
  requires b <= 2*right*(questions-1)+1
  requires left + right == population && population > 0 && questions > 0
  ensures 1+a+b <= 2*population*questions+1
{
  assert 2*left*(questions-1)+2*right*(questions-1) == 2*population*(questions-1);
  assert 2*population*(questions-1) == 2*population*questions-2*population;
}

lemma cdpc_certificate_size_bound<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, tree:InterviewModel<Q>)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires CDPCCertificate(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, tree)
  ensures InterviewNodes(tree) <= 2*|fitness.Keys|*|questions|+1
{
  cdpc_subtree_size_bound(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    fitness.Keys, questions, tree);
}


lemma cdpc_oversized_not_certificate<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, tree:InterviewModel<Q>)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires InterviewNodes(tree) > 2*|fitness.Keys|*|questions|+1
  ensures !CDPCCertificate(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, tree)
{
  if CDPCCertificate(questions, fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper, tree) {
    cdpc_certificate_size_bound(questions, fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper, tree);
  }
}
