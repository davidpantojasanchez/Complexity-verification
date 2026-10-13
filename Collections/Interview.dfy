/*
Trait for finite binary CDPC interviews.

Its immutable model is defined with the datatype InterviewModel: an internal
node asks a question and its two children correspond to the Boolean answer.
Every finite tree is representable and traversable, including inadmissible
certificates. There is no nontrivial representation invariant beyond this
structural model, so the interface has no Valid predicate. Contextual
certificate admissibility is expressed separately by InterviewFits(tree,
remaining). A verifier carries the question context and candidate populations
independently of the tree.

The concrete implementation is defined in ConcreteInterview.dfy.
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

// Questions may occur in different branches, but never twice on one path
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
  decreases tree
  requires InterviewFits(tree, remaining)
  ensures InterviewQuestions(tree) <= remaining
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
  decreases tree
  requires InterviewFits(tree, remaining)
  ensures InterviewDepth(tree) <= |remaining|
{
  if tree.Ask? {
    InterviewStep(tree, remaining);
    InterviewDepthBound(tree.trueBranch, remaining - {tree.question});
    InterviewDepthBound(tree.falseBranch, remaining - {tree.question});
  } else {
    reveal InterviewDepth();
  }
}



trait Interview<Q(==)> {

  function ExecutableModel():InterviewModel<Q>
  ghost function {:opaque} Model():InterviewModel<Q> { ExecutableModel() }

  ghost function Questions():set<Q> { InterviewQuestions(Model()) }
  ghost function NodeCount():nat { InterviewNodes(Model()) }
  ghost function Depth():nat { InterviewDepth(Model()) }

  method IsEnd(ghost counter_in:nat) returns (isEnd:bool, ghost counter_out:nat)
    ensures isEnd == Model().End?
    ensures counter_out == counter_in + CostIsEnd_Interview()

  method Question(ghost counter_in:nat) returns (question:Q, ghost counter_out:nat)
    requires Model().Ask?
    ensures question == Model().question
    ensures counter_out == counter_in + CostQuestion_Interview()

  method Branch(answer:bool, ghost counter_in:nat) returns (branch:Interview<Q>, ghost counter_out:nat)
    requires Model().Ask?
    ensures branch.NodeCount() < NodeCount()
    ensures branch.Model() ==
            if answer then Model().trueBranch else Model().falseBranch
    ensures counter_out == counter_in + CostBranch_Interview()
}


lemma InterviewBound<Q>(interview:Interview<Q>, remaining:set<Q>)
  requires InterviewFits(interview.Model(), remaining)
  ensures interview.Questions() <= remaining
  ensures interview.Depth() <= |remaining|
{
  reveal interview.Questions();
  reveal interview.Depth();
  InterviewQuestionsBound(interview.Model(), remaining);
  InterviewDepthBound(interview.Model(), remaining);
}


ghost function CostIsEnd_Interview():nat { 1 }
ghost function CostQuestion_Interview():nat { 1 }
ghost function CostBranch_Interview():nat { 1 }
ghost function CostNew_Interview():nat { 1 }
