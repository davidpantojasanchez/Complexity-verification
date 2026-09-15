include "../Problems/SetCover.dfy"
include "../Problems/CDPC.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/ConcreteSet.dfy"
include "../Auxiliary/ConcreteMap.dfy"


// Prepare the source questions, select the output branch and compose the total cost bound.
method SetCoverToCDPC_Method(U:Set<int>, S:SetSet<int>, k:nat)
    returns (r:(SetSet<int>, Map_MapSet_T<int, bool, bool>, Map_MapSet_T<int, bool, nat>,
                SetSet<int>, real, real, real, real), ghost counter:nat)
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires init_Set(U) && init_SetSet(S)
  requires S.UBSize1() <= U.UBSize0()
  ensures counter <= SetCoverToCDPCPolynomial(U.Cardinality() + S.Cardinality() + 1)
{
  ghost var n := U.Cardinality() + S.Cardinality() + 1;
  var S':SetSet<int>;
  var privateQuestion:Set<int>;
  var cardinalityS:nat;
  S', privateQuestion, cardinalityS, counter := SetCoverToCDPC_prepare(S, n, 0);
  if cardinalityS <= k {
    r, counter := SetCoverToCDPC_positive(privateQuestion, n, counter);
  } else {
    r, counter := SetCoverToCDPC_nontrivial(U, S', privateQuestion, cardinalityS, k, n, counter);
  }
  PolynomialComposition(n);
}


// Remove the empty set, reserve it as the private question and count S
method SetCoverToCDPC_prepare(S:SetSet<int>, ghost n:nat, ghost counter_in:nat)
    returns (noemptyS:SetSet<int>, privateQuestion:Set<int>, cardinalityS:nat, ghost counter:nat)
  requires S.Valid()
  requires S.UBCardinality() <= n && S.UBSize1() <= n
  ensures noemptyS.Valid()
  ensures noemptyS.Cardinality() <= S.Cardinality()
  ensures noemptyS.UBCardinality() <= S.UBCardinality()
  ensures noemptyS.UBSize1() <= n
  ensures privateQuestion.Valid() && privateQuestion.UBSize0() == 0
  ensures counter <= counter_in + poly_prepare(n)
{
  counter := counter_in;
  SetSetUniverseSizeBound(S, n, n);
  privateQuestion, counter := New_Set(counter);
  noemptyS, counter := S.Remove(privateQuestion, counter);
  cardinalityS, counter := noemptyS.nElements(counter);
  reveal poly_prepare();
}

method SetCoverToCDPC_questions(
    S:SetSet<int>, privateQuestion:Set<int>, ghost n:nat, ghost counter_in:nat)
    returns (questions:SetSet<int>, ghost counter:nat)
  requires S.Valid() && S.UBCardinality() <= n && S.UBSize1() <= n
  ensures questions.Valid()
  ensures counter <= counter_in + (n*n + 1)
{
  SetSetUniverseSizeBound(S, n, n);
  questions := S;
  questions, counter := questions.Add(privateQuestion, counter_in);
}

method SetCoverToCDPC_output_question_sets(
    S:SetSet<int>, privateQuestion:Set<int>, ghost n:nat, ghost counter_in:nat)
    returns (questions:SetSet<int>, privateQuestions:SetSet<int>, ghost counter:nat)
  requires S.Valid() && S.UBCardinality() <= n && S.UBSize1() <= n
  ensures questions.Valid() && privateQuestions.Valid()
  ensures counter <= counter_in + cost_NewSetSet() + 2*(n*n + 1) + 1
{
  questions, counter := SetCoverToCDPC_questions(S, privateQuestion, n, counter_in);
  privateQuestions, counter := New_SetSet(counter);
  privateQuestions, counter := privateQuestions.Add(privateQuestion, counter);
}


// Fixed positive CDPC instance used in the trivial case
method SetCoverToCDPC_positive(privateQuestion:Set<int>, ghost n:nat, ghost counter_in:nat)
    returns (r:(SetSet<int>, Map_MapSet_T<int, bool, bool>,
                 Map_MapSet_T<int, bool, nat>,
                 SetSet<int>, real, real, real, real), ghost counter:nat)
  requires privateQuestion.Valid() && privateQuestion.UBSize0() <= n
  ensures counter <= counter_in + poly_positive(n)
{
  counter := counter_in;
  var candidate:Map_Set_T<int, bool>;
  candidate, counter := New_Map_Set_T(counter);
  MapSetTUniverseSizeBound(candidate, n, n);
  candidate, counter := candidate.Insert(privateQuestion, false, counter);

  var fitness:Map_MapSet_T<int, bool, bool>;
  fitness, counter := New_Map_MapSet_T(counter);
  fitness, counter := fitness.Insert(candidate, true, counter);

  var multiplicity:Map_MapSet_T<int, bool, nat>;
  multiplicity, counter := New_Map_MapSet_T(counter);
  multiplicity, counter := multiplicity.Insert(candidate, 1, counter);

  var questions:SetSet<int>;
  questions, counter := New_SetSet(counter);
  questions, counter := questions.Add(privateQuestion, counter);

  var privateQuestions:SetSet<int>;
  privateQuestions, counter := New_SetSet(counter);
  reveal poly_positive();
  return (questions, fitness, multiplicity, privateQuestions,
          0.0, 1.0, 0.0, 1.0), counter;
}


// Build the multiplicity-based element, set and null candidates, private questions and thresholds.
method SetCoverToCDPC_nontrivial(
    U:Set<int>, S:SetSet<int>, privateQuestion:Set<int>,
    cardinalityS:nat, k:nat, ghost n:nat, ghost counter_in:nat)
    returns (r:(SetSet<int>, Map_MapSet_T<int, bool, bool>,
                 Map_MapSet_T<int, bool, nat>,
                SetSet<int>, real, real, real, real), ghost counter:nat)
  // Types in
  requires privateQuestion.Valid() && privateQuestion.UBSize0() <= n
  requires U.Valid() && U.UBCardinality() <= n
  requires S.Valid() && S.UBCardinality() < n
  requires U.Cardinality() + S.Cardinality() < n
  requires S.UBSize1() <= n
  // Counter
  ensures counter <= counter_in + poly_nontrivial(n)
{
  counter := counter_in;
  var sizeU:nat;
  sizeU, counter := U.nElements(counter);
  var omega:nat := 2 * sizeU * cardinalityS;
  var nullMultiplicity:nat := omega * omega;

  var fitness:Map_MapSet_T<int, bool, bool>;
  var multiplicity:Map_MapSet_T<int, bool, nat>;
  fitness, multiplicity, counter := SetCoverToCDPC_element_candidates(U, S, privateQuestion, omega, n, counter);
  fitness, multiplicity, counter := SetCoverToCDPC_set_candidates(S, privateQuestion, fitness, multiplicity, U.Cardinality(), n, counter);
  fitness, multiplicity, counter := SetCoverToCDPC_null_candidate(S, privateQuestion, fitness, multiplicity, nullMultiplicity, U.Cardinality() + S.Cardinality(), n, counter);
  
  ghost var prepared := counter;
  var questions:SetSet<int>;
  var privateQuestions:SetSet<int>;
  questions, privateQuestions, counter :=
    SetCoverToCDPC_output_question_sets(S, privateQuestion, n, counter);

  var privateLower:real;
  var fitnessUpper:real;
  privateLower, fitnessUpper := SetCoverCDPCThresholds(sizeU, cardinalityS, k, omega);

  nontrivial_costs(n, counter_in, prepared, counter);
  return (questions, fitness, multiplicity, privateQuestions, privateLower, 1.0, 0.0, fitnessUpper), counter;
}


// Add a candidate type for every element in U, with multiplicity omega
method SetCoverToCDPC_element_candidates(U:Set<int>, S:SetSet<int>, privateQuestion:Set<int>, omega:nat,
    ghost n:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<int, bool, bool>, multiplicity:Map_MapSet_T<int, bool, nat>, ghost counter:nat)
  // Types in
  requires U.Valid() && U.UBCardinality() <= n
  requires S.Valid() && S.UBCardinality() < n && S.UBSize1() <= n
  requires privateQuestion.Valid() && privateQuestion.UBSize0() <= n
  requires U.Cardinality() < n
  // Types out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UBCardinality() <= U.Cardinality() && multiplicity.UBCardinality() <= U.Cardinality()
  ensures fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
  ensures fitness.UBSize_Keys_Keys() <= n && multiplicity.UBSize_Keys_Keys() <= n
  // Counter
  ensures counter <= counter_in + 2*cost_NewMapMapSetT() + 1 + n*poly_candidate(n)
{
  counter := counter_in;
  fitness, counter := New_Map_MapSet_T(counter);
  multiplicity, counter := New_Map_MapSet_T(counter);

  var remainingElements:Set<int>;
  remainingElements := U;
  var remainingElementsEmpty:bool;
  remainingElementsEmpty, counter := remainingElements.Empty(counter);
  ghost var counter_start_loop := counter;
  LinearLoopBudgetZero(counter_start_loop, poly_candidate(n));
  while !remainingElementsEmpty
    // Termination
    decreases remainingElements.Cardinality()
    invariant remainingElementsEmpty == (remainingElements.Model() == {})
    // Types
    invariant remainingElements.UBCardinality() <= n
    invariant remainingElements.Cardinality() <= U.Cardinality()
    invariant fitness.UBCardinality() <= U.Cardinality() - remainingElements.Cardinality()
    invariant multiplicity.UBCardinality() <= U.Cardinality() - remainingElements.Cardinality()
    invariant fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
    invariant fitness.UBSize_Keys_Keys() <= n && multiplicity.UBSize_Keys_Keys() <= n
    invariant remainingElements.Valid()
    invariant fitness.Valid()
    invariant multiplicity.Valid()
    // Counter
    invariant counter <= LinearLoopBudget(counter_start_loop, poly_candidate(n), U.Cardinality() - remainingElements.Cardinality())
  {
    LinearLoopBudgetStep(counter_start_loop, poly_candidate(n), U.Cardinality() - remainingElements.Cardinality());
    remainingElements, fitness, multiplicity, remainingElementsEmpty, counter :=
      SetCoverToCDPC_element_candidates_loop(remainingElements, fitness, multiplicity, S, privateQuestion, omega, n, counter);
  }
  LinearLoopBudgetBound(counter_start_loop, poly_candidate(n), U.Cardinality(), n);
}

// Add a candidate type for every set in S, with multiplicity 1
method SetCoverToCDPC_set_candidates(S:SetSet<int>, privateQuestion:Set<int>,
    fitness_in:Map_MapSet_T<int, bool, bool>, multiplicity_in:Map_MapSet_T<int, bool, nat>,
    ghost population:nat, ghost n:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<int, bool, bool>, multiplicity:Map_MapSet_T<int, bool, nat>, ghost counter:nat)
  // Types in
  requires S.Valid() && S.UBCardinality() < n && S.UBSize1() <= n
  requires privateQuestion.Valid() && privateQuestion.UBSize0() <= n
  requires population + S.Cardinality() < n
  requires fitness_in.Valid() && multiplicity_in.Valid()
  requires fitness_in.UBCardinality() <= population && multiplicity_in.UBCardinality() <= population
  requires fitness_in.UBSize_Keys() <= n && multiplicity_in.UBSize_Keys() <= n
  requires fitness_in.UBSize_Keys_Keys() <= n && multiplicity_in.UBSize_Keys_Keys() <= n
  // Types out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UBCardinality() <= population + S.Cardinality()
  ensures multiplicity.UBCardinality() <= population + S.Cardinality()
  ensures fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
  ensures fitness.UBSize_Keys_Keys() <= n && multiplicity.UBSize_Keys_Keys() <= n
  // Counter
  ensures counter <= counter_in + 1 + n*poly_candidate(n)
{
  counter := counter_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  // There is one set candidate per source question.  It answers true only to
  // its own set question and to the private question.
  var remainingSelectedQuestions:SetSet<int>;
  SetSetUniverseSizeBound(S, n, n);
  remainingSelectedQuestions := S;
  var remainingSelectedQuestionsEmpty:bool;
  remainingSelectedQuestionsEmpty, counter := remainingSelectedQuestions.Empty(counter);
  ghost var setStart := counter;
  LinearLoopBudgetZero(setStart, poly_candidate(n));
  while !remainingSelectedQuestionsEmpty
    // Termination
    decreases remainingSelectedQuestions.Cardinality()
    invariant remainingSelectedQuestionsEmpty ==
      (remainingSelectedQuestions.Model() == {})
    // Types
    invariant remainingSelectedQuestions.UBCardinality() <= n
    invariant remainingSelectedQuestions.UBSize1() <= n
    invariant remainingSelectedQuestions.Cardinality() <= S.Cardinality()
    invariant fitness.UBCardinality() <= population + S.Cardinality() - remainingSelectedQuestions.Cardinality()
    invariant multiplicity.UBCardinality() <= population + S.Cardinality() - remainingSelectedQuestions.Cardinality()
    invariant fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
    invariant fitness.UBSize_Keys_Keys() <= n && multiplicity.UBSize_Keys_Keys() <= n
    invariant remainingSelectedQuestions.Valid()
    invariant fitness.Valid()
    invariant multiplicity.Valid()
    // Counter
    invariant counter <= LinearLoopBudget(setStart, poly_candidate(n), S.Cardinality() - remainingSelectedQuestions.Cardinality())
  {
    LinearLoopBudgetStep(setStart, poly_candidate(n), S.Cardinality() - remainingSelectedQuestions.Cardinality());
    remainingSelectedQuestions, fitness, multiplicity, remainingSelectedQuestionsEmpty, counter :=
      SetCoverToCDPC_set_candidates_loop(remainingSelectedQuestions, fitness, multiplicity, S, privateQuestion, n, counter);
  }
  LinearLoopBudgetBound(setStart, poly_candidate(n), S.Cardinality(), n);
}

// Add a null candidate, with multiplicity omega^2
method SetCoverToCDPC_null_candidate(S:SetSet<int>, privateQuestion:Set<int>,
    fitness_in:Map_MapSet_T<int, bool, bool>, multiplicity_in:Map_MapSet_T<int, bool, nat>,
    nullMultiplicity:nat, ghost population:nat, ghost n:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<int, bool, bool>,
             multiplicity:Map_MapSet_T<int, bool, nat>, ghost counter:nat)
  // Types in
  requires S.Valid() && S.UBCardinality() < n && S.UBSize1() <= n
  requires privateQuestion.Valid() && privateQuestion.UBSize0() <= n
  requires population < n
  requires fitness_in.Valid() && multiplicity_in.Valid()
  requires fitness_in.UBCardinality() <= population && multiplicity_in.UBCardinality() <= population
  requires fitness_in.UBSize_Keys() <= n && multiplicity_in.UBSize_Keys() <= n
  requires fitness_in.UBSize_Keys_Keys() <= n && multiplicity_in.UBSize_Keys_Keys() <= n
  // Types out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UBCardinality() <= population + 1
  ensures multiplicity.UBCardinality() <= population + 1
  ensures fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
  ensures fitness.UBSize_Keys_Keys() <= n && multiplicity.UBSize_Keys_Keys() <= n
  // Counter
  ensures counter <= counter_in + cost_NewMapSetT() + (n*n + 1) + 1 +
    n*poly_question_step(n) + 2*(n*n*n + 1)
{
  counter := counter_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  MapMapSetTUniverseSizeBound(fitness_in, n, n, n);
  MapMapSetTUniverseSizeBound(multiplicity_in, n, n, n);
  // The unique fit candidate answers false to every question.
  var nullCandidate:Map_Set_T<int, bool>;
  nullCandidate, counter := New_Map_Set_T(counter);
  var remainingQuestions:SetSet<int>;
  SetSetUniverseSizeBound(S, n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.Empty(counter);
  ghost var nullStart := counter;
  LinearLoopBudgetZero(nullStart, poly_question_step(n));
  while !remainingQuestionsEmpty
    // Termination
    decreases remainingQuestions.Cardinality()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Types
    invariant remainingQuestions.UBCardinality() <= n
    invariant remainingQuestions.Cardinality() <= S.Cardinality()
    invariant nullCandidate.UBCardinality() + remainingQuestions.Cardinality() <= S.Cardinality()
    invariant remainingQuestions.UBSize1() <= n
    invariant nullCandidate.Valid()
    invariant nullCandidate.UBSize_Keys() <= n
    invariant remainingQuestions.Valid()
    // Counter
    invariant counter <= LinearLoopBudget(nullStart, poly_question_step(n),
      S.Cardinality() - remainingQuestions.Cardinality())
  {
    LinearLoopBudgetStep(nullStart, poly_question_step(n), S.Cardinality() - remainingQuestions.Cardinality());
    remainingQuestions, nullCandidate, remainingQuestionsEmpty, counter :=
      SetCoverToCDPC_null_candidate_loop(remainingQuestions, nullCandidate, n, counter);
  }
  LinearLoopBudgetBound(nullStart, poly_question_step(n), S.Cardinality(), n);
  MapSetTUniverseSizeBound(nullCandidate, n, n);
  nullCandidate, counter := nullCandidate.Insert(privateQuestion, false, counter);
  fitness, counter := fitness.Insert(nullCandidate, true, counter);
  multiplicity, counter := multiplicity.Insert(nullCandidate, nullMultiplicity, counter);
}

// Build one element's answer map and add its multiplicity, merging coincident candidates.
method SetCoverToCDPC_element_candidates_loop(
    remainingElements_in:Set<int>,
    fitness_in:Map_MapSet_T<int, bool, bool>,
    multiplicity_in:Map_MapSet_T<int, bool, nat>,
    S:SetSet<int>,
    privateQuestion:Set<int>,
    omega:nat,
    ghost n:nat, ghost counter_in:nat)
    returns (remainingElements:Set<int>,
             fitness:Map_MapSet_T<int, bool, bool>,
             multiplicity:Map_MapSet_T<int, bool, nat>,
             remainingElementsEmpty:bool,
             ghost counter:nat)
  // Termination in
  requires remainingElements_in.Model() != {}
  // Types in
  requires privateQuestion.Valid() && privateQuestion.UBSize0() <= n
  requires remainingElements_in.Valid()
  requires fitness_in.Valid()
  requires multiplicity_in.Valid()
  requires S.Valid()
  requires remainingElements_in.UBCardinality() <= n
  requires S.UBCardinality() < n
  requires S.UBSize1() <= n
  requires fitness_in.UBCardinality() < n && multiplicity_in.UBCardinality() < n
  requires fitness_in.UBSize_Keys() <= n && multiplicity_in.UBSize_Keys() <= n
  requires fitness_in.UBSize_Keys_Keys() <= n && multiplicity_in.UBSize_Keys_Keys() <= n
  // Termination out
  ensures remainingElementsEmpty == (remainingElements.Model() == {})
  ensures remainingElements.Cardinality() == remainingElements_in.Cardinality() - 1
  // Types out
  ensures remainingElements.Valid()
  ensures fitness.Valid()
  ensures multiplicity.Valid()
  ensures fitness.UBCardinality() <= fitness_in.UBCardinality() + 1
  ensures multiplicity.UBCardinality() <= multiplicity_in.UBCardinality() + 1
  ensures fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
  ensures fitness.UBSize_Keys_Keys() <= n && multiplicity.UBSize_Keys_Keys() <= n
  // Invariant out
  ensures remainingElements.Universe() == remainingElements_in.Universe()
  // Counter
  ensures counter <= counter_in + poly_candidate(n)
{
  MapMapSetTUniverseSizeBound(fitness_in, n, n, n);
  MapMapSetTUniverseSizeBound(multiplicity_in, n, n, n);
  remainingElements := remainingElements_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  counter := counter_in;
  var element:int;
  element, counter := remainingElements.Pick(counter);
  remainingElements, counter := remainingElements.Remove(element, counter);

  var candidate:Map_Set_T<int, bool>;
  candidate, counter := New_Map_Set_T(counter);
  var remainingQuestions:SetSet<int>;
  SetSetUniverseSizeBound(S, n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.Empty(counter);
  ghost var questionStart := counter;
  LinearLoopBudgetZero(questionStart, poly_question_step(n));
  while !remainingQuestionsEmpty
    // Termination
    decreases remainingQuestions.Cardinality()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Types
    invariant candidate.Valid()
    invariant candidate.UBSize_Keys() <= n
    invariant remainingQuestions.Valid()
    invariant remainingQuestions.UBCardinality() <= n
    invariant remainingQuestions.Cardinality() <= S.Cardinality()
    invariant candidate.UBCardinality() + remainingQuestions.Cardinality() <= S.Cardinality()
    invariant remainingQuestions.UBSize1() <= n
    // Counter
    invariant counter <= LinearLoopBudget(questionStart, poly_question_step(n),
      S.Cardinality() - remainingQuestions.Cardinality())
  {
    LinearLoopBudgetStep(questionStart, poly_question_step(n), S.Cardinality() - remainingQuestions.Cardinality());
    remainingQuestions, candidate, remainingQuestionsEmpty, counter :=
      SetCoverToCDPC_element_candidates_question_loop(remainingQuestions, candidate, element, n, counter);
  }
  LinearLoopBudgetBound(questionStart, poly_question_step(n), S.Cardinality(), n);
  MapSetTUniverseSizeBound(candidate, n, n);
  candidate, counter := candidate.Insert(privateQuestion, false, counter);

  var alreadyPresent:bool;
  alreadyPresent, counter := multiplicity.ContainsKey(candidate, counter);
  if alreadyPresent {
    var previousMultiplicity:nat;
    previousMultiplicity, counter := multiplicity.Get(candidate, counter);
    multiplicity, counter := multiplicity.Insert(candidate, previousMultiplicity + omega, counter);
  } else {
    multiplicity, counter := multiplicity.Insert(candidate, omega, counter);
  }
  fitness, counter := fitness.Insert(candidate, false, counter);
  remainingElementsEmpty, counter := remainingElements.Empty(counter);
  reveal poly_candidate();
}
// Record whether the element belongs to one question's set, then consume that question.
method SetCoverToCDPC_element_candidates_question_loop(
    remainingQuestions_in:SetSet<int>,
    candidate_in:Map_Set_T<int, bool>,
    element:int,
    ghost n:nat, ghost counter_in:nat)
    returns (remainingQuestions:SetSet<int>,
             candidate:Map_Set_T<int, bool>,
             remainingQuestionsEmpty:bool,
             ghost counter:nat)
  requires remainingQuestions_in.Model() != {}
  requires remainingQuestions_in.Valid()
  requires candidate_in.Valid()
  requires candidate_in.UBSize_Keys() <= n
  requires remainingQuestions_in.UBCardinality() <= n
  requires candidate_in.UBCardinality() <= n
  requires remainingQuestions_in.UBSize1() <= n
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality() == remainingQuestions_in.Cardinality() - 1
  ensures remainingQuestions.Valid()
  ensures candidate.Valid()
  ensures candidate.UBSize_Keys() <= n
  ensures candidate.UBCardinality() <= candidate_in.UBCardinality() + 1
  ensures remainingQuestions.UBSize1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  ensures counter <= counter_in + poly_question_step(n)
{
  SetSetUniverseSizeBound(remainingQuestions_in, n, n);
  MapSetTUniverseSizeBound(candidate_in, n, n);
  reveal poly_question_step();
  remainingQuestions := remainingQuestions_in;
  candidate := candidate_in;
  counter := counter_in;

  var question:Set<int>;
  question, counter := remainingQuestions.Pick(counter);
  var answer:bool;
  answer, counter := question.Contains(element, counter);
  candidate, counter := candidate.Insert(question, answer, counter);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter);
  remainingQuestionsEmpty, counter := remainingQuestions.Empty(counter);
}


// Add a unit-multiplicity set candidate answering true to its own question and the private question.
method SetCoverToCDPC_set_candidates_loop(
    remainingSelectedQuestions_in:SetSet<int>,
    fitness_in:Map_MapSet_T<int, bool, bool>,
    multiplicity_in:Map_MapSet_T<int, bool, nat>,
    S:SetSet<int>,
    privateQuestion:Set<int>,
    ghost n:nat, ghost counter_in:nat)
    returns (remainingSelectedQuestions:SetSet<int>,
             fitness:Map_MapSet_T<int, bool, bool>,
             multiplicity:Map_MapSet_T<int, bool, nat>,
             remainingSelectedQuestionsEmpty:bool,
             ghost counter:nat)
  // Termination in
  requires remainingSelectedQuestions_in.Model() != {}
  // Types in
  requires privateQuestion.Valid() && privateQuestion.UBSize0() <= n
  requires remainingSelectedQuestions_in.Valid()
  requires fitness_in.Valid()
  requires multiplicity_in.Valid()
  requires S.Valid()
  requires remainingSelectedQuestions_in.UBCardinality() <= n
  requires remainingSelectedQuestions_in.UBSize1() <= n
  requires S.UBCardinality() < n
  requires S.UBSize1() <= n
  requires fitness_in.UBCardinality() < n && multiplicity_in.UBCardinality() < n
  requires fitness_in.UBSize_Keys() <= n && multiplicity_in.UBSize_Keys() <= n
  requires fitness_in.UBSize_Keys_Keys() <= n && multiplicity_in.UBSize_Keys_Keys() <= n
  // Termination out
  ensures remainingSelectedQuestionsEmpty == (remainingSelectedQuestions.Model() == {})
  ensures remainingSelectedQuestions.Cardinality() == remainingSelectedQuestions_in.Cardinality() - 1
  // Types out
  ensures remainingSelectedQuestions.Valid()
  ensures fitness.Valid()
  ensures multiplicity.Valid()
  ensures remainingSelectedQuestions.UBSize1() <= n
  ensures fitness.UBCardinality() <= fitness_in.UBCardinality() + 1
  ensures multiplicity.UBCardinality() <= multiplicity_in.UBCardinality() + 1
  ensures fitness.UBSize_Keys() <= n && multiplicity.UBSize_Keys() <= n
  ensures fitness.UBSize_Keys_Keys() <= n && multiplicity.UBSize_Keys_Keys() <= n
  // Invariant out
  ensures remainingSelectedQuestions.Universe() == remainingSelectedQuestions_in.Universe()
  // Counter
  ensures counter <= counter_in + poly_candidate(n)
{
  MapMapSetTUniverseSizeBound(fitness_in, n, n, n);
  MapMapSetTUniverseSizeBound(multiplicity_in, n, n, n);
  remainingSelectedQuestions := remainingSelectedQuestions_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  counter := counter_in;

  var selectedQuestion:Set<int>;
  SetSetUniverseSizeBound(remainingSelectedQuestions_in, n, n);
  selectedQuestion, counter := remainingSelectedQuestions.Pick(counter);
  remainingSelectedQuestions, counter := remainingSelectedQuestions.Remove(selectedQuestion, counter);

  var candidate:Map_Set_T<int, bool>;
  candidate, counter := New_Map_Set_T(counter);
  var remainingQuestions:SetSet<int>;
  SetSetUniverseSizeBound(S, n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.Empty(counter);
  ghost var questionStart := counter;
  LinearLoopBudgetZero(questionStart, poly_question_step(n));
  while !remainingQuestionsEmpty
    // Termination
    decreases remainingQuestions.Cardinality()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Types
    invariant candidate.Valid()
    invariant candidate.UBSize_Keys() <= n
    invariant remainingQuestions.Valid()
    invariant remainingQuestions.UBCardinality() <= n
    invariant remainingQuestions.Cardinality() <= S.Cardinality()
    invariant candidate.UBCardinality() + remainingQuestions.Cardinality() <= S.Cardinality()
    invariant remainingQuestions.UBSize1() <= n
    // Counter
    invariant counter <= LinearLoopBudget(questionStart, poly_question_step(n),
      S.Cardinality() - remainingQuestions.Cardinality())
  {
    LinearLoopBudgetStep(questionStart, poly_question_step(n), S.Cardinality() - remainingQuestions.Cardinality());
    remainingQuestions, candidate, remainingQuestionsEmpty, counter :=
      SetCoverToCDPC_set_candidates_question_loop(remainingQuestions, candidate, selectedQuestion, n, counter);
  }
  LinearLoopBudgetBound(questionStart, poly_question_step(n), S.Cardinality(), n);
  MapSetTUniverseSizeBound(candidate, n, n);
  candidate, counter := candidate.Insert(privateQuestion, true, counter);
  fitness, counter := fitness.Insert(candidate, false, counter);
  multiplicity, counter := multiplicity.Insert(candidate, 1, counter);
  remainingSelectedQuestionsEmpty, counter := remainingSelectedQuestions.Empty(counter);
  reveal poly_candidate();
}
// Record whether one question is the selected set's question, then advance the traversal.
method SetCoverToCDPC_set_candidates_question_loop(
    remainingQuestions_in:SetSet<int>,
    candidate_in:Map_Set_T<int, bool>,
    selectedQuestion:Set<int>,
    ghost n:nat, ghost counter_in:nat)
    returns (remainingQuestions:SetSet<int>,
             candidate:Map_Set_T<int, bool>,
             remainingQuestionsEmpty:bool,
             ghost counter:nat)
  requires remainingQuestions_in.Model() != {}
  requires selectedQuestion.Valid() && selectedQuestion.UBSize0() <= n
  requires remainingQuestions_in.Valid()
  requires candidate_in.Valid()
  requires candidate_in.UBSize_Keys() <= n
  requires remainingQuestions_in.UBCardinality() <= n
  requires candidate_in.UBCardinality() <= n
  requires remainingQuestions_in.UBSize1() <= n
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality() == remainingQuestions_in.Cardinality() - 1
  ensures remainingQuestions.Valid()
  ensures candidate.Valid()
  ensures candidate.UBSize_Keys() <= n
  ensures candidate.UBCardinality() <= candidate_in.UBCardinality() + 1
  ensures remainingQuestions.UBSize1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  ensures counter <= counter_in + poly_question_step(n)
{
  SetSetUniverseSizeBound(remainingQuestions_in, n, n);
  MapSetTUniverseSizeBound(candidate_in, n, n);
  reveal poly_question_step();
  remainingQuestions := remainingQuestions_in;
  candidate := candidate_in;
  counter := counter_in;

  var question:Set<int>;
  question, counter := remainingQuestions.Pick(counter);
  var answer:bool;
  answer, counter := question.Equal(selectedQuestion, counter);
  candidate, counter := candidate.Insert(question, answer, counter);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter);
  remainingQuestionsEmpty, counter := remainingQuestions.Empty(counter);
}


// Extend the null candidate with a false answer to one remaining question.
method SetCoverToCDPC_null_candidate_loop(
    remainingQuestions_in:SetSet<int>,
    nullCandidate_in:Map_Set_T<int, bool>,
    ghost n:nat, ghost counter_in:nat)
    returns (remainingQuestions:SetSet<int>,
             nullCandidate:Map_Set_T<int, bool>,
             remainingQuestionsEmpty:bool,
             ghost counter:nat)
  requires remainingQuestions_in.Model() != {}
  requires remainingQuestions_in.Valid()
  requires nullCandidate_in.Valid()
  requires nullCandidate_in.UBSize_Keys() <= n
  requires remainingQuestions_in.UBCardinality() <= n
  requires nullCandidate_in.UBCardinality() <= n
  requires remainingQuestions_in.UBSize1() <= n
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality() == remainingQuestions_in.Cardinality() - 1
  ensures remainingQuestions.Valid()
  ensures nullCandidate.Valid()
  ensures nullCandidate.UBSize_Keys() <= n
  ensures nullCandidate.UBCardinality() <= nullCandidate_in.UBCardinality() + 1
  ensures remainingQuestions.UBSize1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  ensures counter <= counter_in + poly_question_step(n)
{
  SetSetUniverseSizeBound(remainingQuestions_in, n, n);
  MapSetTUniverseSizeBound(nullCandidate_in, n, n);
  reveal poly_question_step();
  remainingQuestions := remainingQuestions_in;
  nullCandidate := nullCandidate_in;
  counter := counter_in;

  var question:Set<int>;
  question, counter := remainingQuestions.Pick(counter);
  nullCandidate, counter := nullCandidate.Insert(question, false, counter);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter);
  remainingQuestionsEmpty, counter := remainingQuestions.Empty(counter);
}


// Compute the privacy lower and fitness upper thresholds, returning zero for a zero denominator.
method SetCoverCDPCThresholds(universeSize:nat, sourceSetCount:nat, k:nat, omega:nat)
    returns (privateLower:real, fitnessUpper:real)
{
  var privateNumerator:int := (sourceSetCount as int) - (k as int);
  var privateDenominator:int :=
    (universeSize * omega + omega * omega + sourceSetCount) as int -
    (k as int);
  var fitnessNumerator:nat := omega * omega;
  var fitnessDenominator:nat := omega * omega + sourceSetCount;
  privateLower := if privateDenominator == 0 then 0.0 else
    (privateNumerator as real) / (privateDenominator as real);
  fitnessUpper := if fitnessDenominator == 0 then 0.0 else
    (fitnessNumerator as real) / (fitnessDenominator as real);
}


ghost function {:opaque} poly_question_step(n:nat):nat
{ 3*(n + 1) + 2*(n*n + 1) + 1 }

ghost function {:opaque} poly_candidate(n:nat):nat
{
  3*(n + 1) + 2*(n*n + 1) + 4*(n*n*n + 1) + cost_NewMapSetT() + 3 +
  n*poly_question_step(n)
}

ghost function {:opaque} poly_prepare(n:nat):nat
{ cost_NewSet() + (n*n + 1) + 1 }

ghost function {:opaque} poly_positive(n:nat):nat
{ cost_NewMapSetT() + 2*cost_NewMapMapSetT() + 2*cost_NewSetSet() + (n*n + 1) + 3*(n + 1) }

ghost function {:opaque} poly_nontrivial(n:nat):nat
{
  2*cost_NewMapMapSetT() + cost_NewMapSetT() + cost_NewSetSet() +
  3*(n*n + 1) + 2*(n*n*n + 1) + 5 +
  2*n*poly_candidate(n) + n*poly_question_step(n)
}

// Fixed polynomial witness, independent of k and of output map contents.
ghost function SetCoverToCDPCPolynomial(n:nat):nat
{ 12*n*n*n*n + 14*n*n*n + 26*n*n + 35*n + 26 }

// Identify the sum of phase bounds with the fixed degree-four polynomial.
lemma PolynomialComposition(n:nat)
  ensures poly_prepare(n) + poly_positive(n) + poly_nontrivial(n) == SetCoverToCDPCPolynomial(n)
{
  reveal poly_prepare(), poly_positive(), poly_nontrivial();
  reveal poly_candidate(), poly_question_step();
}

// Compose the three population phases and final output operations outside collection contexts.
lemma nontrivial_costs(n:nat, start:nat, prepared:nat, spent:nat)
  requires prepared <= start + 2*cost_NewMapMapSetT() + cost_NewMapSetT() +
    (n*n + 1) + 2*(n*n*n + 1) + 4 +
    2*n*poly_candidate(n) + n*poly_question_step(n)
  requires spent <= prepared + cost_NewSetSet() + 2*(n*n + 1) + 1
  ensures spent <= start + poly_nontrivial(n)
{ reveal poly_nontrivial(); }
