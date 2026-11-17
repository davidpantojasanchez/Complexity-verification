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

  method IsEnd(ghost counter_in:nat, ghost context:SetContext<Q>)
      returns (isEnd:bool, ghost counter_out:nat)
    ensures isEnd == Model().End?
    ensures counter_out == counter_in + Cost(context)
  {
    reveal Model();
    isEnd := tree.End?;
    counter_out := counter_in + Cost(context);
  }

  method Question(ghost counter_in:nat, ghost context:SetContext<Q>)
      returns (question:Q, ghost counter_out:nat)
    requires Model().Ask?
    ensures question == Model().question
    ensures context.weight(question) < SizeBound(context.weight)
    ensures counter_out == counter_in + Cost(context)
  {
    reveal Model();
    question := tree.question;
    size_branch_bound(false, context.weight);
    counter_out := counter_in + Cost(context);
  }

  method Branch(answer:bool, ghost counter_in:nat, ghost context:SetContext<Q>)
      returns (branch:Interview<Q>, ghost counter_out:nat)
    requires Model().Ask?
    ensures branch.NodeCount() < NodeCount()
    ensures branch.SizeBound(context.weight) < SizeBound(context.weight)
    ensures branch.Model() ==
            if answer then Model().trueBranch else Model().falseBranch
    ensures counter_out == counter_in + Cost(context)
  {
    reveal Model();
    size_branch_bound(answer, context.weight);
    branch := new ConcreteInterview(if answer then tree.trueBranch else tree.falseBranch);
    reveal NodeCount(), InterviewNodes();
    counter_out := counter_in + Cost(context);
  }
}


method New_Interview<Q(==)>(tree:InterviewModel<Q>, ghost counter_in:nat, ghost context:SetContext<Q>)
    returns (interview:Interview<Q>, ghost counter_out:nat)
  ensures interview.Model() == tree
  ensures counter_out == counter_in + CostNew_Interview(InterviewRepresentationSizeBound(tree, context.weight))
{
  interview := new ConcreteInterview(tree);
  counter_out := counter_in + CostNew_Interview(InterviewRepresentationSizeBound(tree, context.weight));
}
