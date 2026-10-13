include "Interview.dfy"


class ConcreteInterview<Q(==)> extends Interview<Q> {
  const tree:InterviewModel<Q>

  constructor(tree_in:InterviewModel<Q>)
    ensures Model() == tree_in
  {
    tree := tree_in;
    reveal Model();
  }

  function ExecutableModel():InterviewModel<Q> { tree }

  method IsEnd(ghost counter_in:nat)
      returns (isEnd:bool, ghost counter_out:nat)
    ensures isEnd == Model().End?
    ensures counter_out == counter_in + CostIsEnd_Interview()
  {
    reveal Model();
    isEnd := tree.End?;
    counter_out := counter_in + CostIsEnd_Interview();
  }

  method Question(ghost counter_in:nat)
      returns (question:Q, ghost counter_out:nat)
    requires Model().Ask?
    ensures question == Model().question
    ensures counter_out == counter_in + CostQuestion_Interview()
  {
    reveal Model();
    question := tree.question;
    counter_out := counter_in + CostQuestion_Interview();
  }

  method Branch(answer:bool, ghost counter_in:nat)
      returns (branch:Interview<Q>, ghost counter_out:nat)
    requires Model().Ask?
    ensures branch.NodeCount() < NodeCount()
    ensures branch.Model() ==
            if answer then Model().trueBranch else Model().falseBranch
    ensures counter_out == counter_in + CostBranch_Interview()
  {
    reveal Model();
    var chosen := if answer then tree.trueBranch else tree.falseBranch;
    branch := new ConcreteInterview(chosen);
    if answer {
      assert chosen == tree.trueBranch;
    } else {
      assert chosen == tree.falseBranch;
    }
    reveal NodeCount();
    reveal InterviewNodes();
    counter_out := counter_in + CostBranch_Interview();
  }
}


method New_Interview<Q(==)>(tree:InterviewModel<Q>, ghost counter_in:nat)
    returns (interview:Interview<Q>, ghost counter_out:nat)
  ensures interview.Model() == tree
  ensures counter_out == counter_in + CostNew_Interview()
{
  interview := new ConcreteInterview(tree);
  counter_out := counter_in + CostNew_Interview();
}
