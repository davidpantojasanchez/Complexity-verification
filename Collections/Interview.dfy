include "../Foundations/RepresentationCosts.dfy"
include "../Foundations/CollectionRepresentation.dfy"

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
    1 + if InterviewDepth(whenFalse) <= InterviewDepth(whenTrue)
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


lemma interview_step<Q>(tree:InterviewModel<Q>, remaining:set<Q>)
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
          1 + if InterviewDepth(tree.falseBranch) <= InterviewDepth(tree.trueBranch)
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

lemma interview_questions_bound<Q>(tree:InterviewModel<Q>, remaining:set<Q>)
  decreases tree
  requires InterviewFits(tree, remaining)
  ensures InterviewQuestions(tree) <= remaining
{
  if tree.Ask? {
    interview_step(tree, remaining);
    interview_questions_bound(tree.trueBranch, remaining - {tree.question});
    interview_questions_bound(tree.falseBranch, remaining - {tree.question});
  } else {
    reveal InterviewQuestions();
  }
}

lemma interview_depth_bound<Q>(tree:InterviewModel<Q>, remaining:set<Q>)
  decreases tree
  requires InterviewFits(tree, remaining)
  ensures InterviewDepth(tree) <= |remaining|
{
  if tree.Ask? {
    interview_step(tree, remaining);
    interview_depth_bound(tree.trueBranch, remaining - {tree.question});
    interview_depth_bound(tree.falseBranch, remaining - {tree.question});
  } else {
    reveal InterviewDepth();
  }
}



// Traversal positions, not heap sharing: both child positions contribute.
ghost function InterviewSize<Q>(tree:InterviewModel<Q>, weight:Q -> nat):nat
  decreases tree
{
  match tree
  case End => 1
  case Ask(question, left, right) => 1+weight(question)+InterviewSize(left, weight)+InterviewSize(right, weight)
}

lemma interview_size_bound<Q>(tree:InterviewModel<Q>, weight:Q -> nat, bits:nat)
  requires forall question | question in InterviewQuestions(tree) :: weight(question) <= bits
  ensures InterviewNodes(tree) <= InterviewSize(tree, weight) <= InterviewNodes(tree)*(1+bits)
  decreases tree
{
  reveal InterviewNodes();
  reveal InterviewQuestions();
  if tree.Ask? {
    interview_size_bound(tree.trueBranch, weight, bits);
    interview_size_bound(tree.falseBranch, weight, bits);
    assert tree.question in InterviewQuestions(tree);
    assert weight(tree.question) <= bits;
    calc {
      InterviewSize(tree, weight);
      == 1+weight(tree.question)+InterviewSize(tree.trueBranch, weight)+InterviewSize(tree.falseBranch, weight);
      <= 1+bits+InterviewNodes(tree.trueBranch)*(1+bits)+InterviewNodes(tree.falseBranch)*(1+bits);
      == (1+InterviewNodes(tree.trueBranch)+InterviewNodes(tree.falseBranch))*(1+bits);
      == InterviewNodes(tree)*(1+bits);
    }
  }
}

lemma interview_size_member<Q>(tree:InterviewModel<Q>, weight:Q -> nat, question:Q)
  requires question in InterviewQuestions(tree)
  ensures weight(question) <= InterviewSize(tree, weight)
  decreases tree
{
  reveal InterviewQuestions();
  if tree.Ask? && question != tree.question {
    if question in InterviewQuestions(tree.trueBranch) {
      interview_size_member(tree.trueBranch, weight, question);
    } else {
      interview_size_member(tree.falseBranch, weight, question);
    }
  }
}

// A tree has unbounded depth: compose its node count with one leaf maximum.
ghost function InterviewRepresentationSizeBound<Q>(tree:InterviewModel<Q>, weight:Q -> nat):(size:nat)
  ensures 1 <= size
  ensures InterviewNodes(tree) <= size
{
  reveal InterviewNodes();
  InterviewNodes(tree)*(1+MaxLeafBits_set(InterviewQuestions(tree), weight))
}

lemma interview_representation_bound<Q>(tree:InterviewModel<Q>, weight:Q -> nat)
  ensures InterviewSize(tree, weight) <= InterviewRepresentationSizeBound(tree, weight)
  ensures InterviewRepresentationSizeBound(tree, weight) <= 2*NatPower(InterviewSize(tree, weight)+1, 2)
{
  var bits := MaxLeafBits_set(InterviewQuestions(tree), weight);
  max_by_properties(InterviewQuestions(tree), weight);
  interview_size_bound(tree, weight, bits);
  reveal InterviewNodes();
  forall question | question in InterviewQuestions(tree)
    ensures weight(question) <= InterviewSize(tree, weight)
  { interview_size_member(tree, weight, question); }
  max_leaf_bits_bound_set(InterviewQuestions(tree), weight, InterviewSize(tree, weight));
  polynomial_product_bound(InterviewSize(tree, weight), InterviewNodes(tree), 1+bits, 1, 2, 1, 1);
}

lemma interview_representation_step<Q>(tree:InterviewModel<Q>, answer:bool, weight:Q -> nat)
  requires tree.Ask?
  ensures InterviewRepresentationSizeBound(if answer then tree.trueBranch else tree.falseBranch, weight) < InterviewRepresentationSizeBound(tree, weight)
  ensures weight(tree.question) < InterviewRepresentationSizeBound(tree, weight)
{
  reveal InterviewQuestions(), InterviewNodes();
  var child := if answer then tree.trueBranch else tree.falseBranch;
  max_leaf_bits_subset_set(InterviewQuestions(child), InterviewQuestions(tree), weight);
  max_leaf_bits_member_set(InterviewQuestions(tree), weight, tree.question);
  nonnegative_product_monotonic(InterviewNodes(child), 1+MaxLeafBits_set(InterviewQuestions(child), weight),
    InterviewNodes(tree)-1, 1+MaxLeafBits_set(InterviewQuestions(tree), weight));
  var width := 1+MaxLeafBits_set(InterviewQuestions(tree), weight);
  calc {
    InterviewRepresentationSizeBound(child, weight);
    <= (InterviewNodes(tree)-1)*width;
    < (InterviewNodes(tree)-1)*width+width;
    == InterviewNodes(tree)*width;
    == InterviewRepresentationSizeBound(tree, weight);
  }
  nat_multiplication_monotonic(width, 1, InterviewNodes(tree));
}


trait Interview<Q(==)> {
  function ExecutableModel():InterviewModel<Q>
  ghost function {:opaque} Model():InterviewModel<Q> { ExecutableModel() }

  ghost function NodeCount():nat { InterviewNodes(Model()) }
  ghost function Depth():nat { InterviewDepth(Model()) }

  ghost function SizeBound(weight:Q -> nat):(size:nat)
    ensures 1 <= size && NodeCount() <= size
  { InterviewRepresentationSizeBound(Model(), weight) }

  ghost function Questions():set<Q> { InterviewQuestions(Model()) }

  // Every tree access uses one unit of work and has no external weighted operand.
  ghost function Cost(context:SetContext<Q>):(cost:nat)
    ensures (SizeBound(context.weight) <= context.bound)
      ==> (cost <= BudgetPrimitiveStep(context.bound))
  {
    var size := SizeBound(context.weight);
    collection_step_bound(1, size, 0, context.bound);
    CostRepresentation(1, size, 0)
  }

  method IsEnd(ghost counter_in:nat, ghost context:SetContext<Q>) returns (isEnd:bool, ghost counter_out:nat)
    ensures isEnd == Model().End?
    ensures counter_out == counter_in + Cost(context)

  method Question(ghost counter_in:nat, ghost context:SetContext<Q>) returns (question:Q, ghost counter_out:nat)
    requires Model().Ask?
    ensures question == Model().question
    ensures context.weight(question) < SizeBound(context.weight)
    ensures counter_out == counter_in + Cost(context)

  method Branch(answer:bool, ghost counter_in:nat, ghost context:SetContext<Q>) returns (branch:Interview<Q>, ghost counter_out:nat)
    requires Model().Ask?
    ensures branch.NodeCount() < NodeCount()
    ensures branch.SizeBound(context.weight) < SizeBound(context.weight)
    ensures branch.Model() ==
            if answer then Model().trueBranch else Model().falseBranch
    ensures counter_out == counter_in + Cost(context)

  // Complexity bounds
  lemma size_bound(weight:Q -> nat, bits:nat)
    requires 1 <= bits
    requires forall question | question in Questions() :: weight(question) <= bits
    ensures NodeCount() <= SizeBound(weight) <= NodeCount()*(1+bits)
  {
    max_leaf_bits_bound_set(Questions(), weight, bits);
    nat_multiplication_monotonic(NodeCount(), 1+MaxLeafBits_set(Questions(), weight), 1+bits);
  }

  lemma size_branch_bound(answer:bool, weight:Q -> nat)
    requires Model().Ask?
    ensures InterviewRepresentationSizeBound(if answer then Model().trueBranch else Model().falseBranch, weight) < SizeBound(weight)
    ensures weight(Model().question) < SizeBound(weight)
  { interview_representation_step(Model(), answer, weight); }

  lemma interview_bound(remaining:set<Q>)
    requires InterviewFits(Model(), remaining)
    ensures Questions() <= remaining
    ensures Depth() <= |remaining|
  {
    reveal Questions();
    reveal Depth();
    interview_questions_bound(Model(), remaining);
    interview_depth_bound(Model(), remaining);
  }
}

ghost function CostNew_Interview(size:nat):nat { CostRepresentation(1, size, 0) }
