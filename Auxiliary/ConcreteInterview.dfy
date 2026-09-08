include "Interview.dfy"


class ConcreteInterview<Q(==)> extends Interview<Q> {
  const tree:InterviewModel<Q>
  ghost const domain:set<Q>
  ghost const remaining:set<Q>

  constructor(tree_in:InterviewModel<Q>, ghost domain_in:set<Q>,
              ghost remaining_in:set<Q>)
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
    ensures branch.Model() ==
            if answer then Model().trueBranch else Model().falseBranch
    ensures branch.QuestionDomain() == QuestionDomain()
    ensures branch.RemainingQuestions() ==
            RemainingQuestions() - {Model().question}
    ensures Valid() ==> branch.Valid()
    ensures branch.NodeCount() < NodeCount()
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


method New_Interview<Q(==)>(tree:InterviewModel<Q>, ghost domain:set<Q>,
                            ghost counter_in:nat)
    returns (interview:Interview<Q>, ghost counter_out:nat)
  ensures interview.Model() == tree
  ensures interview.QuestionDomain() == domain
  ensures interview.RemainingQuestions() == domain
  ensures interview.Valid() == InterviewFits(tree, domain)
  ensures counter_out == counter_in + cost_NewInterview()
{
  interview := new ConcreteInterview(tree, domain, domain);
  counter_out := counter_in + cost_NewInterview();
}


method InterviewSmokeTest() returns (ok:bool)
  ensures ok
{
  var tree := Ask(0, End, Ask(1, End, End));
  var interview:Interview<int>;
  ghost var counter:nat := 0;
  interview, counter := New_Interview(tree, {0, 1}, counter);
  assert InterviewFits(tree, {0, 1}) by {
    reveal InterviewFits();
  }
  assert interview.Valid();
  InterviewBounds(interview);
  assert interview.Depth() <= |interview.QuestionDomain()|;
  var isEnd:bool;
  ghost var counter1:nat;
  isEnd, counter1 := interview.IsEnd(counter);
  assert !isEnd;
  var question:int;
  ghost var counter2:nat;
  question, counter2 := interview.Question(counter1);
  assert question == 0;
  var branch:Interview<int>;
  ghost var counter3:nat;
  branch, counter3 := interview.Branch(false, counter2);
  assert branch.Valid();
  assert branch.RemainingQuestions() == {1};
  assert branch.Model() == Ask(1, End, End);
  assert InterviewNodes(Ask(0, End, End)) == 3 by {
    reveal InterviewNodes();
  }
  ok := true;
}


// Invalid certificates remain representable and traversable.  Validity is a
// property for the verifier to check, not a constructor precondition.
method RepeatedQuestionSmokeTest() returns (ok:bool)
  ensures ok
{
  var tree := Ask(0, Ask(0, End, End), End);
  var interview:Interview<int>;
  ghost var counter:nat := 0;
  interview, counter := New_Interview(tree, {0}, counter);
  assert !InterviewFits(tree, {0}) by {
    reveal InterviewFits();
  }
  assert !interview.Valid();
  var branch:Interview<int>;
  branch, counter := interview.Branch(true, counter);
  assert branch.RemainingQuestions() == {};
  var question:int;
  question, counter := branch.Question(counter);
  assert question == 0;
  assert !branch.Valid() by {
    reveal branch.Valid();
    reveal InterviewFits();
  }
  ok := true;
}
