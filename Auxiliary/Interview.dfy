include "Set.dfy"

/*
Abstract interface for finite binary CDPC interviews.

The immutable model is specialized to interviews: an internal node asks a
question and its two children correspond to the Boolean answer.  The complete
question domain is stable, while RemainingQuestions records the context of the
current subtree. Candidate populations deliberately do not form part of this
abstraction; a verifier must carry and filter them separately.
*/

datatype InterviewModel<Q(==)> =
  End |
  Ask(question:Q,
      trueBranch:InterviewModel<Q>,
      falseBranch:InterviewModel<Q>)


ghost function {:opaque} InterviewQuestions<Q>(tree:InterviewModel<Q>):set<Q>
  decreases tree
{
  match tree
  case End => {}
  case Ask(question, whenTrue, whenFalse) =>
    {question} + InterviewQuestions(whenTrue) + InterviewQuestions(whenFalse)
}

ghost function {:opaque} InterviewNodes<Q>(tree:InterviewModel<Q>):nat
  decreases tree
{
  match tree
  case End => 1
  case Ask(_, whenTrue, whenFalse) =>
    1 + InterviewNodes(whenTrue) + InterviewNodes(whenFalse)
}

ghost function {:opaque} InterviewDepth<Q>(tree:InterviewModel<Q>):nat
  decreases tree
{
  match tree
  case End => 0
  case Ask(_, whenTrue, whenFalse) =>
    1 + if InterviewDepth(whenTrue) >= InterviewDepth(whenFalse)
        then InterviewDepth(whenTrue)
        else InterviewDepth(whenFalse)
}

// Questions may occur in different branches, but never twice on one path.
ghost predicate {:opaque} InterviewFits<Q>(tree:InterviewModel<Q>, remaining:set<Q>)
  decreases tree
{
  match tree
  case End => true
  case Ask(question, whenTrue, whenFalse) =>
    question in remaining &&
    InterviewFits(whenTrue, remaining - {question}) &&
    InterviewFits(whenFalse, remaining - {question})
}


lemma InterviewStep<Q>(tree:InterviewModel<Q>, remaining:set<Q>)
  requires tree.Ask?
  requires InterviewFits(tree, remaining)
  ensures tree.question in remaining
  ensures InterviewFits(tree.trueBranch, remaining - {tree.question})
  ensures InterviewFits(tree.falseBranch, remaining - {tree.question})
  ensures InterviewQuestions(tree) ==
          {tree.question} + InterviewQuestions(tree.trueBranch) +
          InterviewQuestions(tree.falseBranch)
  ensures InterviewNodes(tree) ==
          1 + InterviewNodes(tree.trueBranch) + InterviewNodes(tree.falseBranch)
  ensures InterviewDepth(tree) ==
          1 + if InterviewDepth(tree.trueBranch) >= InterviewDepth(tree.falseBranch)
              then InterviewDepth(tree.trueBranch)
              else InterviewDepth(tree.falseBranch)
  ensures InterviewNodes(tree.trueBranch) < InterviewNodes(tree)
  ensures InterviewNodes(tree.falseBranch) < InterviewNodes(tree)
{
  reveal InterviewFits();
  reveal InterviewQuestions();
  reveal InterviewNodes();
  reveal InterviewDepth();
}

lemma InterviewQuestionsBound<Q>(tree:InterviewModel<Q>, remaining:set<Q>)
  requires InterviewFits(tree, remaining)
  ensures InterviewQuestions(tree) <= remaining
  decreases tree
{
  if tree.Ask? {
    InterviewStep(tree, remaining);
    InterviewQuestionsBound(tree.trueBranch, remaining - {tree.question});
    InterviewQuestionsBound(tree.falseBranch, remaining - {tree.question});
  } else {
    reveal InterviewQuestions();
  }
}

lemma InterviewDepthBound<Q>(tree:InterviewModel<Q>, remaining:set<Q>)
  requires InterviewFits(tree, remaining)
  ensures InterviewDepth(tree) <= |remaining|
  decreases tree
{
  if tree.Ask? {
    InterviewStep(tree, remaining);
    InterviewDepthBound(tree.trueBranch, remaining - {tree.question});
    InterviewDepthBound(tree.falseBranch, remaining - {tree.question});
  } else {
    reveal InterviewDepth();
  }
}


ghost function cost_InterviewIsEnd():nat { 1 }
ghost function cost_InterviewQuestion():nat { 1 }
ghost function cost_InterviewBranch():nat { 1 }


trait Interview<Q(==)> {
  ghost function Model():InterviewModel<Q>
  ghost function QuestionDomain():set<Q>
  ghost function RemainingQuestions():set<Q>

  ghost function Valid():bool
  {
    RemainingQuestions() <= QuestionDomain() &&
    InterviewFits(Model(), RemainingQuestions())
  }

  ghost function Questions():set<Q> { InterviewQuestions(Model()) }
  ghost function NodeCount():nat { InterviewNodes(Model()) }
  ghost function Depth():nat { InterviewDepth(Model()) }

  method IsEnd(ghost counter_in:nat) returns (isEnd:bool, ghost counter_out:nat)
    ensures isEnd == Model().End?
    ensures counter_out == counter_in + cost_InterviewIsEnd()

  method Question(ghost counter_in:nat) returns (question:Q, ghost counter_out:nat)
    requires Model().Ask?
    ensures question == Model().question
    ensures counter_out == counter_in + cost_InterviewQuestion()

  method Branch(answer:bool, ghost counter_in:nat) returns (branch:Interview<Q>, ghost counter_out:nat)
    requires Model().Ask?
    ensures branch.Model() ==
            if answer then Model().trueBranch else Model().falseBranch
    ensures branch.QuestionDomain() == QuestionDomain()
    ensures branch.RemainingQuestions() ==
            RemainingQuestions() - {Model().question}
    ensures Valid() ==> branch.Valid()
    ensures branch.NodeCount() < NodeCount()
    ensures counter_out == counter_in + cost_InterviewBranch()
}


lemma InterviewBounds<Q>(interview:Interview<Q>)
  requires interview.Valid()
  ensures interview.Questions() <= interview.RemainingQuestions()
  ensures interview.RemainingQuestions() <= interview.QuestionDomain()
  ensures interview.Depth() <= |interview.RemainingQuestions()|
{
  reveal interview.Valid();
  reveal interview.Questions();
  reveal interview.Depth();
  InterviewQuestionsBound(interview.Model(), interview.RemainingQuestions());
  InterviewDepthBound(interview.Model(), interview.RemainingQuestions());
}
