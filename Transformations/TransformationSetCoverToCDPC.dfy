include "../Polynomial/PolynomialCDPC.dfy"
include "../Problems/CDPCRepresentation.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Arithmetic/CostedArithmetic.dfy"
include "../Problems/SetCover.dfy"
include "../Problems/CDPC.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"
include "../Collections/ConcreteSet.dfy"
include "../Collections/ConcreteMap.dfy"

// Multiplicity-based construction. Functional reduction correctness remains
// separate; these contracts cover output size, numeric lengths and weighted work.
method TransformSetCoverToCDPC<T(!new)>(instance:SetSystemInstance<T>, ghost weight:T -> nat)
    returns (r:CDPCSetInstance<T>, ghost counter:nat)
  // Representation in
  requires instance.universe.Init() && instance.sets.Init()
  // State in
  requires SetCoverValidInstance(instance.Model())
  // Representation out
  ensures r.questions.Valid() && r.fitness.Valid() && r.multiplicity.Valid() && r.privateQuestions.Valid()
  ensures CDPCConstructionOutputBounds(r, instance.universe.Cardinality()+instance.sets.Cardinality()+1, instance.sets.Model()+{{}})
  ensures CDPCConstructionBitsBounds(r, instance.universe.Cardinality()+instance.sets.Cardinality()+1)
  ensures CDPCInstanceSize(r.questions.Model(), r.fitness.Model(), r.multiplicity.Model(),
    r.privateQuestions.Model(), r.thresholds, member => Size_set(member, weight)) <=
          BudgetSetCoverToCDPCOutputSize(SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
  // Cost
  ensures 0 < counter <= BudgetTransformSetCoverToCDPC(
    SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  subset_cardinality_bound_setset(S.Universe(), U.Model());
  S.u_cardinality1_bound(U.Cardinality());
  ghost var n := U.Cardinality()+S.Cardinality()+1;
  ghost var bits := CDPCConstructionLeafBound(U, S, k, weight);
  ghost var phaseBudget := BudgetTransformSetCoverToCDPCPhase(n, bits);
  ghost var inputSize := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  budget_transform_set_cover_to_cdpc_input_bound(instance, weight);
  assert phaseBudget <= BudgetTransformSetCoverToCDPC(inputSize);
  nat_bits_monotonic(n, CDPCConstructionValueBound(n));
  var source:SetSet<T>;
  var privateQuestion:Set<T>;
  var cardinalityS:nat;
  source, privateQuestion, cardinalityS, counter := PrepareSourceSets(S, weight, n, bits, 0);
  nat_bits_monotonic(cardinalityS, n);
  assert CostLessEqualNat(cardinalityS, k) <= 1+2*bits;
  var trivial:bool;
  trivial, counter := LessEqualNat(cardinalityS, k, counter);
  assert counter <= 4*BudgetCDPCConstructionPrimitive(n, bits);
  if trivial {
    r, counter := HandlePositiveCase(privateQuestion, weight, n, bits, counter);
    cdpc_construction_output_source_bound(r, n, {{}}, S.Model()+{{}});
  } else {
    r, counter := HandleNontrivialCase(U, source, privateQuestion, cardinalityS, k, weight, n, bits, counter);
    cdpc_construction_output_source_bound(r, n, source.Model()+{{}}, S.Model()+{{}});
  }
  assert 0 < counter <= phaseBudget;
  assert 0 < counter <= BudgetTransformSetCoverToCDPC(inputSize);
  assert CDPCConstructionOutputBounds(r, n, S.Model()+{{}});
  assert CDPCConstructionBitsBounds(r, n) by {
    cdpc_construction_bits_bound(r, n, S.Model()+{{}});
  }
  cdpc_construction_output_input_bound(instance, r, weight);
}

// Remove the empty set, reserve it as the private question and count S
method PrepareSourceSets<T(!new)>(S:SetSet<T>, ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (noemptyS:SetSet<T>, privateQuestion:Set<T>, cardinalityS:nat, ghost counter:nat)
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires S.ULeafBits(weight) <= bits
  requires S.UCardinality() <= n && S.UCardinality1() <= n
  requires S.Valid()
  ensures noemptyS.Valid()
  ensures noemptyS.Cardinality() <= S.Cardinality()
  ensures noemptyS.UCardinality() <= S.UCardinality()
  ensures noemptyS.UVolumeBound1() <= S.UVolumeBound1()
  ensures privateQuestion.Valid() && privateQuestion.UVolumeBound() == 0
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetPrepareSourceSets(n, bits)
  ensures cardinalityS == noemptyS.Cardinality()
  ensures noemptyS.Model() == S.Model()-{{}}
  ensures privateQuestion.Model() == {}
  ensures noemptyS.ULeafBits(weight) <= bits
  ensures privateQuestion.ULeafBits(weight) <= bits
{
  S.u_volume_bound(n, n);
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  counter := counter_in;
  privateQuestion, counter := New_Set(counter);
  noemptyS, counter := S.Remove(privateQuestion, counter, context);
  cardinalityS, counter := noemptyS.Count(counter, context);
}

method BuildQuestions<T(!new)>(
    S:SetSet<T>, privateQuestion:Set<T>, ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (questions:SetSet<T>, ghost counter:nat)
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  requires S.UCardinality() <= n && S.UCardinality1() <= n
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires S.Valid()
  ensures questions.Valid()
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCConstructionPrimitive(n, bits)
  ensures questions.Model() == S.Model()+{privateQuestion.Model()}
  ensures questions.Cardinality() <= S.Cardinality()+1
  ensures questions.UCardinality1() <= S.UCardinality1()+privateQuestion.Cardinality()
  ensures questions.ULeafBits(weight) <= bits
{
  S.u_volume_bound(n, n);
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  questions := S;
  questions, counter := questions.Add(privateQuestion, counter_in, context);
}

method BuildOutputQuestionSets<T(!new)>(
    S:SetSet<T>, privateQuestion:Set<T>, ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (questions:SetSet<T>, privateQuestions:SetSet<T>, ghost counter:nat)
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  requires S.UCardinality() <= n && S.UCardinality1() <= n
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires S.Valid()
  ensures questions.Valid() && privateQuestions.Valid()
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetBuildOutputQuestionSets(n, bits)
  ensures questions.Model() == S.Model()+{privateQuestion.Model()}
  ensures privateQuestions.Model() == {privateQuestion.Model()}
  ensures questions.Cardinality() <= S.Cardinality()+1
  ensures questions.UCardinality1() <= S.UCardinality1()+privateQuestion.Cardinality()
  ensures privateQuestions.Cardinality() <= 1
  ensures questions.ULeafBits(weight) <= bits
  ensures privateQuestions.ULeafBits(weight) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  questions, counter := BuildQuestions(S, privateQuestion, weight, n, bits, counter_in);
  privateQuestions, counter := New_SetSet(counter);
  privateQuestions, counter := privateQuestions.Add(privateQuestion, counter, context);
}

// Fixed positive CDPC instance used in the trivial case
method HandlePositiveCase<T(!new)>(privateQuestion:Set<T>, ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (r:CDPCSetInstance<T>, ghost counter:nat)
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  requires privateQuestion.Valid()
  requires privateQuestion.Model() == {}
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetHandlePositiveCase(n, bits)
  ensures CDPCConstructionOutputBounds(r, n, {{}})
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var mapContext := BitMapCost(weight, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var fitnessContext := BitNestedMapCost(weight, BoolBits, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  counter := counter_in;
  var candidate:Map_Set_T<T, bool>;
  candidate, counter := New_Map_Set_T(counter);
  candidate, counter := candidate.Insert(privateQuestion, false, counter, mapContext);

  var fitness:Map_MapSet_T<T, bool, bool>;
  fitness, counter := New_Map_MapSet_T(counter);
  fitness, counter := fitness.Insert(candidate, true, counter, fitnessContext);

  var multiplicity:Map_MapSet_T<T, bool, nat>;
  multiplicity, counter := New_Map_MapSet_T(counter);
  multiplicity, counter := multiplicity.Insert(candidate, 1, counter, multiplicityContext);

  var questions:SetSet<T>;
  questions, counter := New_SetSet(counter);
  questions, counter := questions.Add(privateQuestion, counter, context);

  var privateQuestions:SetSet<T>;
  privateQuestions, counter := New_SetSet(counter);
  return CDPCSetInstance(questions, fitness, multiplicity, privateQuestions,
    CDPCThresholds(Rational(0, 1), Rational(1, 1), Rational(0, 1), Rational(1, 1))), counter;
}

// Build the multiplicity-based element, set and null candidates, private questions and thresholds.
method HandleNontrivialCase<T(!new)>(
    U:Set<T>, S:SetSet<T>, privateQuestion:Set<T>,
    cardinalityS:nat, k:nat, ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (r:CDPCSetInstance<T>, ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires U.ULeafBits(weight) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires U.Valid() && U.UCardinality() <= n
  requires S.Valid() && S.UCardinality() < n
  requires U.Cardinality() + S.Cardinality() < n
  requires S.UVolumeBound1() <= n
  // State in
  requires cardinalityS == S.Cardinality() && k < cardinalityS
  requires privateQuestion.Model() == {}
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetNontrivialCase(n, bits)
  ensures CDPCConstructionOutputBounds(r, n, S.Model()+{{}})
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  counter := counter_in;
  var cardinalityU:nat;
  cardinalityU, counter := U.Count(counter, context);
  ghost var maximum := CDPCConstructionValueBound(n);
  var doubled, omega, nullMultiplicity:nat;
  nat_arithmetic_within_budget(2, cardinalityU, maximum);
  doubled, counter := MultiplyNat(2, cardinalityU, counter);
  nat_arithmetic_within_budget(doubled, cardinalityS, maximum);
  omega, counter := MultiplyNat(doubled, cardinalityS, counter);
  nonnegative_product_monotonic(2*cardinalityU, cardinalityS, 2*n, n);
  nat_arithmetic_within_budget(omega, omega, maximum);
  nullMultiplicity, counter := MultiplyNat(omega, omega, counter);
  nonnegative_product_monotonic(omega, omega, 2*n*n, 2*n*n);
  assert nullMultiplicity <= CDPCConstructionValueBound(n);

  var fitness:Map_MapSet_T<T, bool, bool>;
  var multiplicity:Map_MapSet_T<T, bool, nat>;
  fitness, multiplicity, counter := BuildElementCandidates(U, S, privateQuestion, omega, weight, n, bits, counter);
  nonnegative_product_monotonic(U.Cardinality(), omega, n, 2*n*n);
  fitness, multiplicity, counter := BuildSetCandidates(S, privateQuestion, fitness, multiplicity, U.Cardinality(), weight, n, bits, counter);
  assert {:split_here} true;
  fitness, multiplicity, counter := AddNullCandidate(S, privateQuestion, fitness, multiplicity, nullMultiplicity, U.Cardinality() + S.Cardinality(), weight, n, bits, counter);
  
  var questions:SetSet<T>;
  var privateQuestions:SetSet<T>;
  questions, privateQuestions, counter := BuildOutputQuestionSets(S, privateQuestion, weight, n, bits, counter);
  S.u_volume_bound(n, n);

  var privateLower, fitnessUpper:Rational;
  privateLower, fitnessUpper, counter := ComputeThresholds(
    cardinalityU, cardinalityS, k, omega, nullMultiplicity, n, counter);

  return CDPCSetInstance(questions, fitness, multiplicity, privateQuestions,
    CDPCThresholds(privateLower, Rational(1, 1), Rational(0, 1), fitnessUpper)), counter;
}

// Add a candidate type for every element in U, with multiplicity omega
method {:isolate_assertions} BuildElementCandidates<T(!new)>(U:Set<T>, S:SetSet<T>, privateQuestion:Set<T>, omega:nat,
    ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<T, bool, bool>, multiplicity:Map_MapSet_T<T, bool, nat>, ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires U.ULeafBits(weight) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  requires U.Valid() && U.UCardinality() <= n
  requires S.Valid() && S.UCardinality() < n && S.UVolumeBound1() <= n
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires U.Cardinality() < n
  // State in
  requires omega <= 2*n*n
  // Representation out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UCardinality() <= U.Cardinality() && multiplicity.UCardinality() <= U.Cardinality()
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + 3*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetCandidateStep(n, bits)
  ensures forall candidate | candidate in multiplicity.Model() :: multiplicity.Model()[candidate] <= U.Cardinality()*omega
  ensures CDPCQuestionsWithin(fitness.Model(), S.Model()+{privateQuestion.Model()})
  ensures CDPCQuestionsWithin(multiplicity.Model(), S.Model()+{privateQuestion.Model()})
  ensures fitness.ULeafBits(weight, BoolBits, BoolBits) <= bits
  ensures multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var fitnessContext := BitNestedMapCost(weight, BoolBits, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  counter := counter_in;
  fitness, counter := New_Map_MapSet_T(counter);
  multiplicity, counter := New_Map_MapSet_T(counter);

  var remainingElements:Set<T>;
  remainingElements := U;
  var remainingElementsEmpty:bool;
  remainingElementsEmpty, counter := remainingElements.IsEmpty(counter, context);
  ghost var counter_start_loop := counter;
  linear_loop_budget_zero(counter_start_loop, BudgetCandidateStep(n, bits));
  while !remainingElementsEmpty
    // Progress
    decreases remainingElements.Cardinality()
    invariant remainingElementsEmpty == (remainingElements.Model() == {})
    // Representation
    invariant remainingElements.UCardinality() <= n
    invariant remainingElements.Cardinality() <= U.Cardinality()
    invariant fitness.UCardinality() <= U.Cardinality() - remainingElements.Cardinality()
    invariant multiplicity.UCardinality() <= U.Cardinality() - remainingElements.Cardinality()
    invariant fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
    invariant fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
    invariant remainingElements.ULeafBits(weight) <= bits
    invariant remainingElements.Valid()
    invariant fitness.ULeafBits(weight, BoolBits, BoolBits) <= bits
    invariant fitness.Valid()
    invariant multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits
    invariant multiplicity.Valid()
    // State
    invariant forall candidate | candidate in multiplicity.Model() :: multiplicity.Model()[candidate] <= (U.Cardinality()-remainingElements.Cardinality())*omega
    invariant CDPCQuestionsWithin(fitness.Model(), S.Model()+{privateQuestion.Model()})
    invariant CDPCQuestionsWithin(multiplicity.Model(), S.Model()+{privateQuestion.Model()})
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(counter_start_loop, BudgetCandidateStep(n, bits), U.Cardinality() - remainingElements.Cardinality())
  {
    linear_loop_budget_step(counter_start_loop, BudgetCandidateStep(n, bits), U.Cardinality() - remainingElements.Cardinality());
    remainingElements, fitness, multiplicity, remainingElementsEmpty, counter :=
      BuildElementCandidatesLoop(remainingElements, fitness, multiplicity, S, privateQuestion, omega,
        U.Cardinality()-remainingElements.Cardinality(), weight, n, bits, counter);
  }
  linear_loop_budget_bound(counter_start_loop, BudgetCandidateStep(n, bits), U.Cardinality(), n);
}

// Add a candidate type for every set in S, with multiplicity 1
method BuildSetCandidates<T(!new)>(S:SetSet<T>, privateQuestion:Set<T>, fitness_in:Map_MapSet_T<T, bool, bool>,
    multiplicity_in:Map_MapSet_T<T, bool, nat>, ghost population:nat, ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<T, bool, bool>, multiplicity:Map_MapSet_T<T, bool, nat>, ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  requires fitness_in.ULeafBits(weight, BoolBits, BoolBits) <= bits
  requires multiplicity_in.ULeafBits(weight, BoolBits, NatBits) <= bits
  requires S.Valid() && S.UCardinality() < n && S.UVolumeBound1() <= n
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires population + S.Cardinality() < n
  requires fitness_in.Valid() && multiplicity_in.Valid()
  requires fitness_in.UCardinality() <= population && multiplicity_in.UCardinality() <= population
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // State in
  requires forall candidate | candidate in multiplicity_in.Model() :: multiplicity_in.Model()[candidate] <= CDPCConstructionValueBound(n)
  requires CDPCQuestionsWithin(fitness_in.Model(), S.Model()+{privateQuestion.Model()})
  requires CDPCQuestionsWithin(multiplicity_in.Model(), S.Model()+{privateQuestion.Model()})
  // Representation out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UCardinality() <= population + S.Cardinality()
  ensures multiplicity.UCardinality() <= population + S.Cardinality()
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetCandidateStep(n, bits)
  ensures forall candidate | candidate in multiplicity.Model() :: multiplicity.Model()[candidate] <= CDPCConstructionValueBound(n)
  ensures CDPCQuestionsWithin(fitness.Model(), S.Model()+{privateQuestion.Model()})
  ensures CDPCQuestionsWithin(multiplicity.Model(), S.Model()+{privateQuestion.Model()})
  ensures fitness.ULeafBits(weight, BoolBits, BoolBits) <= bits
  ensures multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  counter := counter_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  // There is one set candidate per source question.  It answers true only to
  // its own set question and to the private question.
  var remainingSelectedQuestions:SetSet<T>;
  S.u_volume_bound(n, n);
  remainingSelectedQuestions := S;
  var remainingSelectedQuestionsEmpty:bool;
  remainingSelectedQuestionsEmpty, counter := remainingSelectedQuestions.IsEmpty(counter, context);
  ghost var setStart := counter;
  linear_loop_budget_zero(setStart, BudgetCandidateStep(n, bits));
  while !remainingSelectedQuestionsEmpty
    // Progress
    decreases remainingSelectedQuestions.Cardinality()
    invariant remainingSelectedQuestionsEmpty ==
      (remainingSelectedQuestions.Model() == {})
    // Representation
    invariant remainingSelectedQuestions.UCardinality() <= n
    invariant remainingSelectedQuestions.UVolumeBound1() <= n
    invariant remainingSelectedQuestions.Cardinality() <= S.Cardinality()
    invariant fitness.UCardinality() <= population + S.Cardinality() - remainingSelectedQuestions.Cardinality()
    invariant multiplicity.UCardinality() <= population + S.Cardinality() - remainingSelectedQuestions.Cardinality()
    invariant fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
    invariant fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
    invariant remainingSelectedQuestions.ULeafBits(weight) <= bits
    invariant remainingSelectedQuestions.Valid()
    invariant fitness.ULeafBits(weight, BoolBits, BoolBits) <= bits
    invariant fitness.Valid()
    invariant multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits
    invariant multiplicity.Valid()
    invariant forall candidate | candidate in multiplicity.Model() :: multiplicity.Model()[candidate] <= CDPCConstructionValueBound(n)
    invariant CDPCQuestionsWithin(fitness.Model(), S.Model()+{privateQuestion.Model()})
    invariant CDPCQuestionsWithin(multiplicity.Model(), S.Model()+{privateQuestion.Model()})
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(setStart, BudgetCandidateStep(n, bits), S.Cardinality() - remainingSelectedQuestions.Cardinality())
  {
    linear_loop_budget_step(setStart, BudgetCandidateStep(n, bits), S.Cardinality() - remainingSelectedQuestions.Cardinality());
    remainingSelectedQuestions, fitness, multiplicity, remainingSelectedQuestionsEmpty, counter :=
      BuildSetCandidatesLoop(remainingSelectedQuestions, fitness, multiplicity, S, privateQuestion, weight, n, bits, counter);
  }
  linear_loop_budget_bound(setStart, BudgetCandidateStep(n, bits), S.Cardinality(), n);
}

// Add a null candidate, with multiplicity omega^2
method {:isolate_assertions} AddNullCandidate<T(!new)>(S:SetSet<T>, privateQuestion:Set<T>,
    fitness_in:Map_MapSet_T<T, bool, bool>, multiplicity_in:Map_MapSet_T<T, bool, nat>,
    nullMultiplicity:nat, ghost population:nat, ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<T, bool, bool>,
             multiplicity:Map_MapSet_T<T, bool, nat>, ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  requires fitness_in.ULeafBits(weight, BoolBits, BoolBits) <= bits
  requires multiplicity_in.ULeafBits(weight, BoolBits, NatBits) <= bits
  requires S.Valid() && S.UCardinality() < n && S.UVolumeBound1() <= n
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires population < n
  requires fitness_in.Valid() && multiplicity_in.Valid()
  requires fitness_in.UCardinality() <= population && multiplicity_in.UCardinality() <= population
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // State in
  requires forall candidate | candidate in multiplicity_in.Model() :: multiplicity_in.Model()[candidate] <= CDPCConstructionValueBound(n)
  requires CDPCQuestionsWithin(fitness_in.Model(), S.Model()+{privateQuestion.Model()})
  requires CDPCQuestionsWithin(multiplicity_in.Model(), S.Model()+{privateQuestion.Model()})
  requires nullMultiplicity <= CDPCConstructionValueBound(n)
  // Representation out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UCardinality() <= population + 1
  ensures multiplicity.UCardinality() <= population + 1
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + 5*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits)
  ensures forall candidate | candidate in multiplicity.Model() :: multiplicity.Model()[candidate] <= CDPCConstructionValueBound(n)
  ensures CDPCQuestionsWithin(fitness.Model(), S.Model()+{privateQuestion.Model()})
  ensures CDPCQuestionsWithin(multiplicity.Model(), S.Model()+{privateQuestion.Model()})

  ensures fitness.ULeafBits(weight, BoolBits, BoolBits) <= bits
  ensures multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var mapContext := BitMapCost(weight, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var fitnessContext := BitNestedMapCost(weight, BoolBits, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  counter := counter_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  fitness_in.u_volume_bound(n, n, n);
  multiplicity_in.u_volume_bound(n, n, n);
  // The unique fit candidate answers false to every question.
  var nullCandidate:Map_Set_T<T, bool>;
  nullCandidate, counter := New_Map_Set_T(counter);
  var remainingQuestions:SetSet<T>;
  S.u_volume_bound(n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter, context);
  assert counter <= counter_in + 2*BudgetCDPCConstructionPrimitive(n, bits);
  ghost var nullStart := counter;
  linear_loop_budget_zero(nullStart, BudgetQuestionStep(n, bits));
  while !remainingQuestionsEmpty
    // Progress
    decreases remainingQuestions.Cardinality()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Representation
    invariant remainingQuestions.UCardinality() <= n
    invariant remainingQuestions.Cardinality() <= S.Cardinality()
    invariant nullCandidate.UCardinality() + remainingQuestions.Cardinality() <= S.Cardinality()
    invariant remainingQuestions.UVolumeBound1() <= n
    invariant remainingQuestions.Model() <= S.Model()
    invariant nullCandidate.Model().Keys <= S.Model()
    invariant nullCandidate.ULeafBits(weight, BoolBits) <= bits
    invariant nullCandidate.Valid()
    invariant nullCandidate.UCardinalityKeys() <= n
    invariant remainingQuestions.ULeafBits(weight) <= bits
    invariant remainingQuestions.Valid()
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(nullStart, BudgetQuestionStep(n, bits),
      S.Cardinality() - remainingQuestions.Cardinality())
  {
    linear_loop_budget_step(nullStart, BudgetQuestionStep(n, bits), S.Cardinality() - remainingQuestions.Cardinality());
    remainingQuestions, nullCandidate, remainingQuestionsEmpty, counter :=
      AddNullCandidateLoop(remainingQuestions, nullCandidate, weight, n, bits, counter);
  }
  linear_loop_budget_bound(nullStart, BudgetQuestionStep(n, bits), S.Cardinality(), n);
  assert counter <= counter_in + 2*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  nullCandidate.u_volume_bound(n, n);
  nullCandidate, counter := nullCandidate.Insert(privateQuestion, false, counter, mapContext);
  assert counter <= counter_in + 3*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  nullCandidate.u_volume_bound(n, n);
  fitness, counter := fitness.Insert(nullCandidate, true, counter, fitnessContext);
  assert counter <= counter_in + 4*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  nat_bits_monotonic(nullMultiplicity, CDPCConstructionValueBound(n));
  multiplicity, counter := multiplicity.Insert(nullCandidate, nullMultiplicity, counter, multiplicityContext);
}

// Build one element's answer map and add its multiplicity, merging coincident candidates.
method {:isolate_assertions} BuildElementCandidatesLoop<T(!new)>(
    remainingElements_in:Set<T>,
    fitness_in:Map_MapSet_T<T, bool, bool>,
    multiplicity_in:Map_MapSet_T<T, bool, nat>,
    S:SetSet<T>,
    privateQuestion:Set<T>,
    omega:nat, ghost processed:nat,
    ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (remainingElements:Set<T>,
             fitness:Map_MapSet_T<T, bool, bool>,
             multiplicity:Map_MapSet_T<T, bool, nat>,
             remainingElementsEmpty:bool,
             ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires remainingElements_in.ULeafBits(weight) <= bits
  requires fitness_in.ULeafBits(weight, BoolBits, BoolBits) <= bits
  requires multiplicity_in.ULeafBits(weight, BoolBits, NatBits) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  // Progress in
  requires remainingElements_in.Model() != {}
  // Representation in
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires remainingElements_in.Valid()
  requires fitness_in.Valid()
  requires multiplicity_in.Valid()
  requires S.Valid()
  requires remainingElements_in.UCardinality() <= n
  requires S.UCardinality() < n
  requires S.UVolumeBound1() <= n
  requires fitness_in.UCardinality() < n && multiplicity_in.UCardinality() < n
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // State in
  requires processed < n && omega <= 2*n*n
  requires forall candidate | candidate in multiplicity_in.Model() :: multiplicity_in.Model()[candidate] <= processed*omega
  requires CDPCQuestionsWithin(fitness_in.Model(), S.Model()+{privateQuestion.Model()})
  requires CDPCQuestionsWithin(multiplicity_in.Model(), S.Model()+{privateQuestion.Model()})
  // Progress out
  ensures remainingElementsEmpty == (remainingElements.Model() == {})
  ensures remainingElements.Cardinality() == remainingElements_in.Cardinality() - 1
  // Representation out
  ensures remainingElements.Valid()
  ensures fitness.Valid()
  ensures multiplicity.Valid()
  ensures fitness.UCardinality() <= fitness_in.UCardinality() + 1
  ensures multiplicity.UCardinality() <= multiplicity_in.UCardinality() + 1
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // State out
  ensures remainingElements.Universe() == remainingElements_in.Universe()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCandidateStep(n, bits)
  // State out
  ensures forall candidate | candidate in multiplicity.Model() :: multiplicity.Model()[candidate] <= (processed+1)*omega
  ensures CDPCQuestionsWithin(fitness.Model(), S.Model()+{privateQuestion.Model()})
  ensures CDPCQuestionsWithin(multiplicity.Model(), S.Model()+{privateQuestion.Model()})
  // Representation out
  ensures remainingElements.ULeafBits(weight) <= bits
  ensures fitness.ULeafBits(weight, BoolBits, BoolBits) <= bits
  ensures multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits
{
  assert processed*omega + omega == (processed+1)*omega;
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var mapContext := BitMapCost(weight, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var fitnessContext := BitNestedMapCost(weight, BoolBits, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  fitness_in.u_volume_bound(n, n, n);
  multiplicity_in.u_volume_bound(n, n, n);
  assert fitness_in.USizeBound(weight, BoolBits, BoolBits) <= CDPCConstructionSizeBound(n,bits);
  assert multiplicity_in.USizeBound(weight, BoolBits, NatBits) <= CDPCConstructionSizeBound(n,bits);
  assert remainingElements_in.USizeBound(weight) <= CDPCConstructionSizeBound(n, bits);
  remainingElements := remainingElements_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  counter := counter_in;
  var element:T;
  element, counter := remainingElements.Pick(counter, context);
  assert counter <= counter_in + BudgetCDPCConstructionPrimitive(n, bits);
  assert remainingElements.Cost(remainingElements.TraversalWork(), weight(element), context) <=
    BudgetCDPCConstructionPrimitive(n, bits);
  remainingElements, counter := remainingElements.Remove(element, counter, context);
  assert counter <= counter_in + 2*BudgetCDPCConstructionPrimitive(n, bits);

  var candidate:Map_Set_T<T, bool>;
  candidate, counter := New_Map_Set_T(counter);
  assert counter <= counter_in + 3*BudgetCDPCConstructionPrimitive(n, bits);
  var remainingQuestions:SetSet<T>;
  S.u_volume_bound(n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter, context);
  assert counter <= counter_in + 4*BudgetCDPCConstructionPrimitive(n, bits);
  ghost var questionStart := counter;
  linear_loop_budget_zero(questionStart, BudgetQuestionStep(n, bits));
  while !remainingQuestionsEmpty
    // Progress
    decreases remainingQuestions.Cardinality()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Representation
    invariant remainingQuestions.Model() <= S.Model()
    invariant candidate.Model().Keys <= S.Model()
    invariant candidate.ULeafBits(weight, BoolBits) <= bits
    invariant candidate.Valid()
    invariant candidate.UCardinalityKeys() <= n
    invariant remainingQuestions.ULeafBits(weight) <= bits
    invariant remainingQuestions.Valid()
    invariant remainingQuestions.UCardinality() <= n
    invariant remainingQuestions.Cardinality() <= S.Cardinality()
    invariant candidate.UCardinality() + remainingQuestions.Cardinality() <= S.Cardinality()
    invariant remainingQuestions.UVolumeBound1() <= n
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(questionStart, BudgetQuestionStep(n, bits),
      S.Cardinality() - remainingQuestions.Cardinality())
  {
    linear_loop_budget_step(questionStart, BudgetQuestionStep(n, bits), S.Cardinality() - remainingQuestions.Cardinality());
    remainingQuestions, candidate, remainingQuestionsEmpty, counter :=
      BuildElementCandidateQuestionsLoop(remainingQuestions, candidate, element, weight, n, bits, counter);
  }
  assert remainingQuestions.Cardinality() == 0;
  assert counter <= LinearLoopBudget(questionStart, BudgetQuestionStep(n,bits), S.Cardinality());
  nat_multiplication_monotonic(n, 0, BudgetQuestionStep(n, bits));
  linear_loop_budget_transfer(questionStart, BudgetQuestionStep(n, bits), S.Cardinality(), n, counter, 0,
    counter_in+4*BudgetCDPCConstructionPrimitive(n,bits)+n*BudgetQuestionStep(n,bits));
  assert counter <= counter_in + 4*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  candidate.u_volume_bound(n, n);
  assert candidate.USizeBound(weight, BoolBits) <= CDPCConstructionSizeBound(n,bits)-bits;
  candidate, counter := candidate.Insert(privateQuestion, false, counter, mapContext);
  assert counter <= counter_in + 5*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  candidate.u_volume_bound(n, n);
  assert candidate.USizeBound(weight, BoolBits) <= CDPCConstructionSizeBound(n,bits)-bits;

  assert candidate.LeafBits(weight, BoolBits) <= bits;
  var alreadyPresent:bool;
  alreadyPresent, counter := multiplicity.ContainsKey(candidate, counter, multiplicityContext);
  assert counter <= counter_in + 6*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  if alreadyPresent {
    var previousMultiplicity:nat;
    previousMultiplicity, counter := multiplicity.Get(candidate, counter, multiplicityContext);
    ghost var maximum := CDPCConstructionValueBound(n);
    cdpc_construction_multiplicity_bound(previousMultiplicity, omega, processed, n);
    nat_arithmetic_within_budget(previousMultiplicity, omega, maximum);
    var combined:nat;
    combined, counter := AddNat(previousMultiplicity, omega, counter);
    nat_bits_monotonic(combined, maximum);
    multiplicity, counter := multiplicity.Insert(candidate, combined, counter, multiplicityContext);
    assert multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits;
    forall key | key in multiplicity.Model()
      ensures multiplicity.Model()[key] <= (processed+1)*omega
    {
      if key != candidate.Model() {
        assert key in multiplicity_in.Model();
        assert multiplicity.Model()[key] == multiplicity_in.Model()[key];
      }
    }
    assert counter <= counter_in + 9*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  } else {
    nat_bits_monotonic(omega, CDPCConstructionValueBound(n));
    nonnegative_product_monotonic(1, omega, processed+1, omega);
    multiplicity, counter := multiplicity.Insert(candidate, omega, counter, multiplicityContext);
    assert multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits;
    forall key | key in multiplicity.Model()
      ensures multiplicity.Model()[key] <= (processed+1)*omega
    {
      if key != candidate.Model() {
        assert key in multiplicity_in.Model();
        assert multiplicity.Model()[key] == multiplicity_in.Model()[key];
      } else {
        assert multiplicity.Model()[key] == omega;
      }
    }
    assert counter <= counter_in + 9*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  }
  fitness, counter := fitness.Insert(candidate, false, counter, fitnessContext);
  assert counter <= counter_in + 10*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  remainingElementsEmpty, counter := remainingElements.IsEmpty(counter, context);
}

// Record whether the element belongs to one question's set, then consume that question.
method BuildElementCandidateQuestionsLoop<T(!new)>(
    remainingQuestions_in:SetSet<T>,
    candidate_in:Map_Set_T<T, bool>,
    element:T,
    ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (remainingQuestions:SetSet<T>,
             candidate:Map_Set_T<T, bool>,
             remainingQuestionsEmpty:bool,
             ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires remainingQuestions_in.ULeafBits(weight) <= bits
  requires candidate_in.ULeafBits(weight, BoolBits) <= bits
  requires weight(element) <= bits
  // Progress in
  requires remainingQuestions_in.Model() != {}
  // Representation in
  requires remainingQuestions_in.Valid()
  requires candidate_in.Valid()
  requires candidate_in.UCardinalityKeys() <= n
  requires remainingQuestions_in.UCardinality() <= n
  requires candidate_in.UCardinality() <= n
  requires remainingQuestions_in.UVolumeBound1() <= n
  // Progress out
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality() == remainingQuestions_in.Cardinality() - 1
  // Representation out
  ensures remainingQuestions.Valid()
  ensures candidate.Valid()
  ensures candidate.UCardinalityKeys() <= n
  ensures candidate.UCardinality() <= candidate_in.UCardinality() + 1
  ensures remainingQuestions.UVolumeBound1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  // State out
  ensures remainingQuestions.Model() <= remainingQuestions_in.Model()
  ensures candidate.Model().Keys <= candidate_in.Model().Keys + remainingQuestions_in.Model()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetQuestionStep(n, bits)
  // Representation out
  ensures remainingQuestions.ULeafBits(weight) <= bits
  ensures candidate.ULeafBits(weight, BoolBits) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var mapContext := BitMapCost(weight, BoolBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  remainingQuestions_in.u_volume_bound(n, n);
  candidate_in.u_volume_bound(n, n);
  remainingQuestions := remainingQuestions_in;
  candidate := candidate_in;
  counter := counter_in;

  var question:Set<T>;
  question, counter := remainingQuestions.Pick(counter, context);
  var answer:bool;
  answer, counter := question.Contains(element, counter, context);
  candidate, counter := candidate.Insert(question, answer, counter, mapContext);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter, context);
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter, context);
}

// Add a unit-multiplicity set candidate answering true to its own question and the private question.
method BuildSetCandidatesLoop<T(!new)>(
    remainingSelectedQuestions_in:SetSet<T>,
    fitness_in:Map_MapSet_T<T, bool, bool>,
    multiplicity_in:Map_MapSet_T<T, bool, nat>,
    S:SetSet<T>,
    privateQuestion:Set<T>,
    ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (remainingSelectedQuestions:SetSet<T>,
             fitness:Map_MapSet_T<T, bool, bool>,
             multiplicity:Map_MapSet_T<T, bool, nat>,
             remainingSelectedQuestionsEmpty:bool,
             ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires remainingSelectedQuestions_in.ULeafBits(weight) <= bits
  requires fitness_in.ULeafBits(weight, BoolBits, BoolBits) <= bits
  requires multiplicity_in.ULeafBits(weight, BoolBits, NatBits) <= bits
  requires S.ULeafBits(weight) <= bits
  requires privateQuestion.ULeafBits(weight) <= bits
  // Progress in
  requires remainingSelectedQuestions_in.Model() != {}
  // Representation in
  requires privateQuestion.Valid() && privateQuestion.UVolumeBound() <= n
  requires remainingSelectedQuestions_in.Valid()
  requires fitness_in.Valid()
  requires multiplicity_in.Valid()
  requires S.Valid()
  requires remainingSelectedQuestions_in.UCardinality() <= n
  requires remainingSelectedQuestions_in.UVolumeBound1() <= n
  requires S.UCardinality() < n
  requires S.UVolumeBound1() <= n
  requires fitness_in.UCardinality() < n && multiplicity_in.UCardinality() < n
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // State in
  requires forall candidate | candidate in multiplicity_in.Model() :: multiplicity_in.Model()[candidate] <= CDPCConstructionValueBound(n)
  requires CDPCQuestionsWithin(fitness_in.Model(), S.Model()+{privateQuestion.Model()})
  requires CDPCQuestionsWithin(multiplicity_in.Model(), S.Model()+{privateQuestion.Model()})
  // Progress out
  ensures remainingSelectedQuestionsEmpty == (remainingSelectedQuestions.Model() == {})
  ensures remainingSelectedQuestions.Cardinality() == remainingSelectedQuestions_in.Cardinality() - 1
  // Representation out
  ensures remainingSelectedQuestions.Valid()
  ensures fitness.Valid()
  ensures multiplicity.Valid()
  ensures remainingSelectedQuestions.UVolumeBound1() <= n
  ensures fitness.UCardinality() <= fitness_in.UCardinality() + 1
  ensures multiplicity.UCardinality() <= multiplicity_in.UCardinality() + 1
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // State out
  ensures remainingSelectedQuestions.Universe() == remainingSelectedQuestions_in.Universe()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCandidateStep(n, bits)
  // State out
  ensures forall candidate | candidate in multiplicity.Model() :: multiplicity.Model()[candidate] <= CDPCConstructionValueBound(n)
  ensures CDPCQuestionsWithin(fitness.Model(), S.Model()+{privateQuestion.Model()})
  ensures CDPCQuestionsWithin(multiplicity.Model(), S.Model()+{privateQuestion.Model()})
  // Representation out
  ensures remainingSelectedQuestions.ULeafBits(weight) <= bits
  ensures fitness.ULeafBits(weight, BoolBits, BoolBits) <= bits
  ensures multiplicity.ULeafBits(weight, BoolBits, NatBits) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var mapContext := BitMapCost(weight, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var fitnessContext := BitNestedMapCost(weight, BoolBits, BoolBits, CDPCConstructionSizeBound(n, bits));
  ghost var multiplicityContext := BitNestedMapCost(weight, BoolBits, NatBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  fitness_in.u_volume_bound(n, n, n);
  multiplicity_in.u_volume_bound(n, n, n);
  remainingSelectedQuestions := remainingSelectedQuestions_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  counter := counter_in;

  var selectedQuestion:Set<T>;
  remainingSelectedQuestions_in.u_volume_bound(n, n);
  selectedQuestion, counter := remainingSelectedQuestions.Pick(counter, context);
  remainingSelectedQuestions, counter := remainingSelectedQuestions.Remove(selectedQuestion, counter, context);

  var candidate:Map_Set_T<T, bool>;
  candidate, counter := New_Map_Set_T(counter);
  var remainingQuestions:SetSet<T>;
  S.u_volume_bound(n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter, context);
  assert counter <= counter_in + 4*BudgetCDPCConstructionPrimitive(n, bits);
  ghost var questionStart := counter;
  linear_loop_budget_zero(questionStart, BudgetQuestionStep(n, bits));
  while !remainingQuestionsEmpty
    // Progress
    decreases remainingQuestions.Cardinality()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Representation
    invariant remainingQuestions.Model() <= S.Model()
    invariant candidate.Model().Keys <= S.Model()
    invariant candidate.ULeafBits(weight, BoolBits) <= bits
    invariant candidate.Valid()
    invariant candidate.UCardinalityKeys() <= n
    invariant remainingQuestions.ULeafBits(weight) <= bits
    invariant remainingQuestions.Valid()
    invariant remainingQuestions.UCardinality() <= n
    invariant remainingQuestions.Cardinality() <= S.Cardinality()
    invariant candidate.UCardinality() + remainingQuestions.Cardinality() <= S.Cardinality()
    invariant remainingQuestions.UVolumeBound1() <= n
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(questionStart, BudgetQuestionStep(n, bits),
      S.Cardinality() - remainingQuestions.Cardinality())
  {
    linear_loop_budget_step(questionStart, BudgetQuestionStep(n, bits), S.Cardinality() - remainingQuestions.Cardinality());
    remainingQuestions, candidate, remainingQuestionsEmpty, counter :=
      BuildSetCandidateQuestionsLoop(remainingQuestions, candidate, selectedQuestion, weight, n, bits, counter);
  }
  linear_loop_budget_bound(questionStart, BudgetQuestionStep(n, bits), S.Cardinality(), n);
  assert counter <= counter_in + 4*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  candidate.u_volume_bound(n, n);
  candidate, counter := candidate.Insert(privateQuestion, true, counter, mapContext);
  assert counter <= counter_in + 5*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  candidate.u_volume_bound(n, n);
  fitness, counter := fitness.Insert(candidate, false, counter, fitnessContext);
  assert counter <= counter_in + 6*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  multiplicity, counter := multiplicity.Insert(candidate, 1, counter, multiplicityContext);
  assert counter <= counter_in + 7*BudgetCDPCConstructionPrimitive(n, bits) + n*BudgetQuestionStep(n, bits);
  remainingSelectedQuestionsEmpty, counter := remainingSelectedQuestions.IsEmpty(counter, context);
}

// Record whether one question is the selected set's question, then advance the traversal.
method BuildSetCandidateQuestionsLoop<T(!new)>(
    remainingQuestions_in:SetSet<T>,
    candidate_in:Map_Set_T<T, bool>,
    selectedQuestion:Set<T>,
    ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (remainingQuestions:SetSet<T>,
             candidate:Map_Set_T<T, bool>,
             remainingQuestionsEmpty:bool,
             ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires remainingQuestions_in.ULeafBits(weight) <= bits
  requires candidate_in.ULeafBits(weight, BoolBits) <= bits
  requires selectedQuestion.ULeafBits(weight) <= bits
  // Progress in
  requires remainingQuestions_in.Model() != {}
  // Representation in
  requires selectedQuestion.Valid() && selectedQuestion.UVolumeBound() <= n
  requires remainingQuestions_in.Valid()
  requires candidate_in.Valid()
  requires candidate_in.UCardinalityKeys() <= n
  requires remainingQuestions_in.UCardinality() <= n
  requires candidate_in.UCardinality() <= n
  requires remainingQuestions_in.UVolumeBound1() <= n
  // Progress out
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality() == remainingQuestions_in.Cardinality() - 1
  // Representation out
  ensures remainingQuestions.Valid()
  ensures candidate.Valid()
  ensures candidate.UCardinalityKeys() <= n
  ensures candidate.UCardinality() <= candidate_in.UCardinality() + 1
  ensures remainingQuestions.UVolumeBound1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  // State out
  ensures remainingQuestions.Model() <= remainingQuestions_in.Model()
  ensures candidate.Model().Keys <= candidate_in.Model().Keys + remainingQuestions_in.Model()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetQuestionStep(n, bits)
  // Representation out
  ensures remainingQuestions.ULeafBits(weight) <= bits
  ensures candidate.ULeafBits(weight, BoolBits) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var mapContext := BitMapCost(weight, BoolBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  remainingQuestions_in.u_volume_bound(n, n);
  candidate_in.u_volume_bound(n, n);
  remainingQuestions := remainingQuestions_in;
  candidate := candidate_in;
  counter := counter_in;

  var question:Set<T>;
  question, counter := remainingQuestions.Pick(counter, context);
  var answer:bool;
  answer, counter := question.Equal(selectedQuestion, counter, context);
  candidate, counter := candidate.Insert(question, answer, counter, mapContext);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter, context);
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter, context);
}

// Extend the null candidate with a false answer to one remaining question.
method AddNullCandidateLoop<T(!new)>(
    remainingQuestions_in:SetSet<T>,
    nullCandidate_in:Map_Set_T<T, bool>,
    ghost weight:T -> nat, ghost n:nat, ghost bits:nat, ghost counter_in:nat)
    returns (remainingQuestions:SetSet<T>,
             nullCandidate:Map_Set_T<T, bool>,
             remainingQuestionsEmpty:bool,
             ghost counter:nat)
  // Representation in
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires remainingQuestions_in.ULeafBits(weight) <= bits
  requires nullCandidate_in.ULeafBits(weight, BoolBits) <= bits
  // Progress in
  requires remainingQuestions_in.Model() != {}
  // Representation in
  requires remainingQuestions_in.Valid()
  requires nullCandidate_in.Valid()
  requires nullCandidate_in.UCardinalityKeys() <= n
  requires remainingQuestions_in.UCardinality() <= n
  requires nullCandidate_in.UCardinality() <= n
  requires remainingQuestions_in.UVolumeBound1() <= n
  // Progress out
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality() == remainingQuestions_in.Cardinality() - 1
  // Representation out
  ensures remainingQuestions.Valid()
  ensures nullCandidate.Valid()
  ensures nullCandidate.UCardinalityKeys() <= n
  ensures nullCandidate.UCardinality() <= nullCandidate_in.UCardinality() + 1
  ensures remainingQuestions.UVolumeBound1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  // State out
  ensures remainingQuestions.Model() <= remainingQuestions_in.Model()
  ensures nullCandidate.Model().Keys <= nullCandidate_in.Model().Keys + remainingQuestions_in.Model()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetQuestionStep(n, bits)
  // Representation out
  ensures remainingQuestions.ULeafBits(weight) <= bits
  ensures nullCandidate.ULeafBits(weight, BoolBits) <= bits
{
  ghost var context := BitSetCost(weight, CDPCConstructionSizeBound(n, bits));
  ghost var mapContext := BitMapCost(weight, BoolBits, CDPCConstructionSizeBound(n, bits));
  cdpc_construction_bounds(n, bits);
  remainingQuestions_in.u_volume_bound(n, n);
  nullCandidate_in.u_volume_bound(n, n);
  remainingQuestions := remainingQuestions_in;
  nullCandidate := nullCandidate_in;
  counter := counter_in;

  var question:Set<T>;
  question, counter := remainingQuestions.Pick(counter, context);
  nullCandidate, counter := nullCandidate.Insert(question, false, counter, mapContext);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter, context);
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter, context);
}

// Exact thresholds on the nontrivial branch (k < sourceSetCount).
method ComputeThresholds(
    universeCardinality:nat, sourceSetCount:nat, k:nat, omega:nat, square:nat, ghost n:nat, ghost counter_in:nat)
    returns (privateLower:Rational, fitnessUpper:Rational, ghost counter:nat)
  requires k < sourceSetCount <= n && universeCardinality <= n
  requires omega <= 2*n*n && square == omega*omega
  ensures privateLower.numerator == sourceSetCount-k
  ensures privateLower.denominator == universeCardinality*omega+square+sourceSetCount-k
  ensures fitnessUpper.numerator == square && fitnessUpper.denominator == square+sourceSetCount
  ensures privateLower.numerator <= CDPCConstructionValueBound(n)
  ensures privateLower.denominator <= CDPCConstructionValueBound(n)
  ensures fitnessUpper.numerator <= CDPCConstructionValueBound(n)
  ensures fitnessUpper.denominator <= CDPCConstructionValueBound(n)
  ensures counter_in < counter
  ensures counter <= counter_in+6*BudgetNatArithmetic(CDPCConstructionValueBound(n))
{
  ghost var maximum := CDPCConstructionValueBound(n);
  nonnegative_product_monotonic(universeCardinality, omega, n, 2*n*n);
  nonnegative_product_monotonic(omega, omega, 2*n*n, 2*n*n);
  assert 1 <= n;
  assert omega <= maximum && square <= maximum;
  var weighted, total, privateNumerator, privateDenominator, fitnessDenominator:nat;
  nat_arithmetic_within_budget(universeCardinality, omega, maximum);
  weighted, counter := MultiplyNat(universeCardinality, omega, counter_in);
  nat_arithmetic_within_budget(weighted, square, maximum);
  total, counter := AddNat(weighted, square, counter);
  nat_arithmetic_within_budget(total, sourceSetCount, maximum);
  total, counter := AddNat(total, sourceSetCount, counter);
  nat_arithmetic_within_budget(sourceSetCount, k, maximum);
  privateNumerator, counter := SubtractNat(sourceSetCount, k, counter);
  nat_arithmetic_within_budget(total, k, maximum);
  privateDenominator, counter := SubtractNat(total, k, counter);
  nat_arithmetic_within_budget(square, sourceSetCount, maximum);
  fitnessDenominator, counter := AddNat(square, sourceSetCount, counter);
  privateLower := Rational(privateNumerator, privateDenominator);
  fitnessUpper := Rational(square, fitnessDenominator);
}
