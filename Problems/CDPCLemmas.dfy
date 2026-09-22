include "CDPC.dfy"

lemma {:isolate_assertions} CDPCSubtreeSizeBound<Q(!new)>(
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
    CDPCSubtreeSizeBound(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      left, remaining - {q}, tree.trueBranch);
    CDPCSubtreeSizeBound(fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      right, remaining - {q}, tree.falseBranch);
    assert |remaining - {q}| == |remaining| - 1;
    CDPCNodeBudget(|left|, |right|, |candidates|, |remaining|,
      InterviewNodes(tree.trueBranch), InterviewNodes(tree.falseBranch));
  }
}

lemma CDPCNodeBudget(left:nat, right:nat, population:nat, questions:nat, a:nat, b:nat)
  requires a <= 2*left*(questions-1)+1
  requires b <= 2*right*(questions-1)+1
  requires left + right == population && population > 0 && questions > 0
  ensures 1+a+b <= 2*population*questions+1
{
  assert 2*left*(questions-1)+2*right*(questions-1) == 2*population*(questions-1);
  assert 2*population*(questions-1) == 2*population*questions-2*population;
}

lemma CDPCCertificateSizeBound<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, tree:InterviewModel<Q>)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires CDPCCertificate(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, tree)
  ensures InterviewNodes(tree) <= 2*|fitness.Keys|*|questions|+1
{
  CDPCSubtreeSizeBound(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    fitness.Keys, questions, tree);
}


lemma CDPCOversizedNotCertificate<Q(!new)>(
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
    CDPCCertificateSizeBound(questions, fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper, tree);
  }
}
