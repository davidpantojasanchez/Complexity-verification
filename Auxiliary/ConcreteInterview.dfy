include "Interview.dfy"


class ConcreteInterview<Q(==)> extends Interview<Q> {
  const tree:InterviewModel<Q>
  ghost const domain:set<Q>
  ghost const remaining:set<Q>

  constructor(tree_in:InterviewModel<Q>, ghost domain_in:set<Q>, ghost remaining_in:set<Q>)
    ensures Model() == tree_in
    ensures QuestionDomain() == domain_in
    ensures RemainingQuestions() == remaining_in
  {
    tree := tree_in;
    domain := domain_in;
    remaining := remaining_in;
    reveal Model();
  }

  function Repr():InterviewModel<Q> { tree }
  ghost function QuestionDomain():set<Q> { domain }
  ghost function RemainingQuestions():set<Q> { remaining }

  method IsEnd(ghost counter_in:nat)
      returns (isEnd:bool, ghost counter_out:nat)
    ensures isEnd == Model().End?
    ensures counter_out == counter_in + cost_InterviewIsEnd()
  {
    reveal Model();
    isEnd := tree.End?;
    counter_out := counter_in + cost_InterviewIsEnd();
  }

  method Question(ghost counter_in:nat)
      returns (question:Q, ghost counter_out:nat)
    requires Model().Ask?
    ensures question == Model().question
    ensures counter_out == counter_in + cost_InterviewQuestion()
  {
    reveal Model();
    question := tree.question;
    counter_out := counter_in + cost_InterviewQuestion();
  }

  method Branch(answer:bool, ghost counter_in:nat)
      returns (branch:Interview<Q>, ghost counter_out:nat)
    requires Model().Ask?
    ensures Valid() ==> branch.Valid()
    ensures branch.NodeCount() < NodeCount()
    ensures branch.Model() ==
            if answer then Model().trueBranch else Model().falseBranch
    ensures branch.QuestionDomain() == QuestionDomain()
    ensures branch.RemainingQuestions() ==
            RemainingQuestions() - {Model().question}
    ensures counter_out == counter_in + cost_InterviewBranch()
  {
    reveal Model();
    var chosen := if answer then tree.trueBranch else tree.falseBranch;
    branch := new ConcreteInterview(chosen, domain, remaining - {tree.question});
    if Valid() {
      reveal Valid();
      InterviewStep(tree, remaining);
    }
    if answer {
      assert chosen == tree.trueBranch;
    } else {
      assert chosen == tree.falseBranch;
    }
    reveal NodeCount();
    reveal InterviewNodes();
    counter_out := counter_in + cost_InterviewBranch();
  }
}


method New_Interview<Q(==)>(tree:InterviewModel<Q>, ghost domain:set<Q>, ghost counter_in:nat)
    returns (interview:Interview<Q>, ghost counter_out:nat)
  ensures interview.Valid() == InterviewFits(tree, domain)
  ensures interview.Model() == tree
  ensures interview.QuestionDomain() == domain
  ensures interview.RemainingQuestions() == domain
  ensures counter_out == counter_in + cost_NewInterview()
{
  interview := new ConcreteInterview(tree, domain, domain);
  counter_out := counter_in + cost_NewInterview();
}
