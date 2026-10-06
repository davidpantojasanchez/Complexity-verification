include "../Problems/SetCover.dfy"
include "../Problems/CDPC.dfy"
include "../Lemmas/Lemmas.dfy"
include "../Collections/ConcreteSet.dfy"
include "../Collections/ConcreteMap.dfy"


// Prepare the source questions, select the output branch and compose the total cost bound.
method TransformSetCoverToCDPC(U:Set<int>, S:SetSet<int>, k:nat)
    returns (r:(SetSet<int>, Map_MapSet_T<int, bool, bool>, Map_MapSet_T<int, bool, nat>,
                SetSet<int>, real, real, real, real), ghost counter:nat)
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires Init_Set(U) && Init_SetSet(S)
  ensures counter <= PolySetCoverToCDPC(U.Cardinality0() + S.Cardinality0() + 1)
{
  assert S.USize1() <= U.USize0() by {
    UniverseSubsetSizeBound_SetSet(S, U.Model());
  }
  ghost var n := U.Cardinality0() + S.Cardinality0() + 1;
  var S':SetSet<int>;
  var privateQuestion:Set<int>;
  var cardinalityS:nat;
  S', privateQuestion, cardinalityS, counter := Prepare(S, n, 0);
  if cardinalityS <= k {
    r, counter := HandlePositiveCase(privateQuestion, n, counter);
  } else {
    r, counter := HandleNontrivialCase(U, S', privateQuestion, cardinalityS, k, n, counter);
  }
  PolySetCoverToCDPCComposition(n);
}


// Remove the empty set, reserve it as the private question and count S
method Prepare(S:SetSet<int>, ghost n:nat, ghost counter_in:nat)
    returns (noemptyS:SetSet<int>, privateQuestion:Set<int>, cardinalityS:nat, ghost counter:nat)
  requires S.Valid()
  requires S.UCardinality0() <= n && S.USize1() <= n
  ensures noemptyS.Valid()
  ensures noemptyS.Cardinality0() <= S.Cardinality0()
  ensures noemptyS.UCardinality0() <= S.UCardinality0()
  ensures noemptyS.USize1() <= n
  ensures privateQuestion.Valid() && privateQuestion.USize0() == 0
  ensures counter <= counter_in + PolyPrepare(n)
{
  counter := counter_in;
  UniverseSizeBound_SetSet(S, n, n);
  privateQuestion, counter := New_Set(counter);
  noemptyS, counter := S.Remove(privateQuestion, counter);
  cardinalityS, counter := noemptyS.Count(counter);
  reveal PolyPrepare();
}

method BuildQuestions(
    S:SetSet<int>, privateQuestion:Set<int>, ghost n:nat, ghost counter_in:nat)
    returns (questions:SetSet<int>, ghost counter:nat)
  requires S.Valid() && S.UCardinality0() <= n && S.USize1() <= n
  ensures questions.Valid()
  ensures counter <= counter_in + (n*n + 1)
{
  UniverseSizeBound_SetSet(S, n, n);
  questions := S;
  questions, counter := questions.Add(privateQuestion, counter_in);
}

method BuildOutputQuestionSets(
    S:SetSet<int>, privateQuestion:Set<int>, ghost n:nat, ghost counter_in:nat)
    returns (questions:SetSet<int>, privateQuestions:SetSet<int>, ghost counter:nat)
  requires S.Valid() && S.UCardinality0() <= n && S.USize1() <= n
  ensures questions.Valid() && privateQuestions.Valid()
  ensures counter <= counter_in + CostNew_SetSet() + 2*(n*n + 1) + 1
{
  questions, counter := BuildQuestions(S, privateQuestion, n, counter_in);
  privateQuestions, counter := New_SetSet(counter);
  privateQuestions, counter := privateQuestions.Add(privateQuestion, counter);
}


// Fixed positive CDPC instance used in the trivial case
method HandlePositiveCase(privateQuestion:Set<int>, ghost n:nat, ghost counter_in:nat)
    returns (r:(SetSet<int>, Map_MapSet_T<int, bool, bool>,
                 Map_MapSet_T<int, bool, nat>,
                 SetSet<int>, real, real, real, real), ghost counter:nat)
  requires privateQuestion.Valid() && privateQuestion.USize0() <= n
  ensures counter <= counter_in + PolyPositiveCase(n)
{
  counter := counter_in;
  var candidate:Map_Set_T<int, bool>;
  candidate, counter := New_Map_Set_T(counter);
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
  reveal PolyPositiveCase();
  return (questions, fitness, multiplicity, privateQuestions,
          0.0, 1.0, 0.0, 1.0), counter;
}


// Build the multiplicity-based element, set and null candidates, private questions and thresholds.
method HandleNontrivialCase(
    U:Set<int>, S:SetSet<int>, privateQuestion:Set<int>,
    cardinalityS:nat, k:nat, ghost n:nat, ghost counter_in:nat)
    returns (r:(SetSet<int>, Map_MapSet_T<int, bool, bool>,
                 Map_MapSet_T<int, bool, nat>,
                SetSet<int>, real, real, real, real), ghost counter:nat)
  // Types in
  requires privateQuestion.Valid() && privateQuestion.USize0() <= n
  requires U.Valid() && U.UCardinality0() <= n
  requires S.Valid() && S.UCardinality0() < n
  requires U.Cardinality0() + S.Cardinality0() < n
  requires S.USize1() <= n
  // Counter
  ensures counter <= counter_in + PolyNontrivialCase(n)
{
  counter := counter_in;
  var sizeU:nat;
  sizeU, counter := U.Count(counter);
  var omega:nat := 2 * sizeU * cardinalityS;
  var nullMultiplicity:nat := omega * omega;

  var fitness:Map_MapSet_T<int, bool, bool>;
  var multiplicity:Map_MapSet_T<int, bool, nat>;
  fitness, multiplicity, counter := BuildElementCandidates(U, S, privateQuestion, omega, n, counter);
  fitness, multiplicity, counter := BuildSetCandidates(S, privateQuestion, fitness, multiplicity, U.Cardinality0(), n, counter);
  fitness, multiplicity, counter := AddNullCandidate(S, privateQuestion, fitness, multiplicity, nullMultiplicity, U.Cardinality0() + S.Cardinality0(), n, counter);
  
  ghost var prepared := counter;
  var questions:SetSet<int>;
  var privateQuestions:SetSet<int>;
  questions, privateQuestions, counter := BuildOutputQuestionSets(S, privateQuestion, n, counter);

  var privateLower:real;
  var fitnessUpper:real;
  privateLower, fitnessUpper := ComputeThresholds(sizeU, cardinalityS, k, omega);

  CostNontrivialBound(n, counter_in, prepared, counter);
  return (questions, fitness, multiplicity, privateQuestions, privateLower, 1.0, 0.0, fitnessUpper), counter;
}


// Add a candidate type for every element in U, with multiplicity omega
method BuildElementCandidates(U:Set<int>, S:SetSet<int>, privateQuestion:Set<int>, omega:nat, ghost n:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<int, bool, bool>, multiplicity:Map_MapSet_T<int, bool, nat>, ghost counter:nat)
  // Types in
  requires U.Valid() && U.UCardinality0() <= n
  requires S.Valid() && S.UCardinality0() < n && S.USize1() <= n
  requires privateQuestion.Valid() && privateQuestion.USize0() <= n
  requires U.Cardinality0() < n
  // Types out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UCardinality() <= U.Cardinality0() && multiplicity.UCardinality() <= U.Cardinality0()
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Counter
  ensures counter <= counter_in + 2*CostNew_Map_MapSet_T() + 1 + n*PolyCandidate(n)
{
  counter := counter_in;
  fitness, counter := New_Map_MapSet_T(counter);
  multiplicity, counter := New_Map_MapSet_T(counter);

  var remainingElements:Set<int>;
  remainingElements := U;
  var remainingElementsEmpty:bool;
  remainingElementsEmpty, counter := remainingElements.IsEmpty(counter);
  ghost var counter_start_loop := counter;
  LinearLoopBudgetZero(counter_start_loop, PolyCandidate(n));
  while !remainingElementsEmpty
    // Termination
    decreases remainingElements.Cardinality0()
    invariant remainingElementsEmpty == (remainingElements.Model() == {})
    // Types
    invariant remainingElements.UCardinality0() <= n
    invariant remainingElements.Cardinality0() <= U.Cardinality0()
    invariant fitness.UCardinality() <= U.Cardinality0() - remainingElements.Cardinality0()
    invariant multiplicity.UCardinality() <= U.Cardinality0() - remainingElements.Cardinality0()
    invariant fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
    invariant fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
    invariant remainingElements.Valid()
    invariant fitness.Valid()
    invariant multiplicity.Valid()
    // Counter
    invariant counter <= LinearLoopBudget(counter_start_loop, PolyCandidate(n), U.Cardinality0() - remainingElements.Cardinality0())
  {
    LinearLoopBudgetStep(counter_start_loop, PolyCandidate(n), U.Cardinality0() - remainingElements.Cardinality0());
    remainingElements, fitness, multiplicity, remainingElementsEmpty, counter :=
      BuildElementCandidatesLoop(remainingElements, fitness, multiplicity, S, privateQuestion, omega, n, counter);
  }
  LinearLoopBudgetBound(counter_start_loop, PolyCandidate(n), U.Cardinality0(), n);
}

// Add a candidate type for every set in S, with multiplicity 1
method BuildSetCandidates(S:SetSet<int>, privateQuestion:Set<int>, fitness_in:Map_MapSet_T<int, bool, bool>,
    multiplicity_in:Map_MapSet_T<int, bool, nat>, ghost population:nat, ghost n:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<int, bool, bool>, multiplicity:Map_MapSet_T<int, bool, nat>, ghost counter:nat)
  // Types in
  requires S.Valid() && S.UCardinality0() < n && S.USize1() <= n
  requires privateQuestion.Valid() && privateQuestion.USize0() <= n
  requires population + S.Cardinality0() < n
  requires fitness_in.Valid() && multiplicity_in.Valid()
  requires fitness_in.UCardinality() <= population && multiplicity_in.UCardinality() <= population
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // Types out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UCardinality() <= population + S.Cardinality0()
  ensures multiplicity.UCardinality() <= population + S.Cardinality0()
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Counter
  ensures counter <= counter_in + 1 + n*PolyCandidate(n)
{
  counter := counter_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  // There is one set candidate per source question.  It answers true only to
  // its own set question and to the private question.
  var remainingSelectedQuestions:SetSet<int>;
  UniverseSizeBound_SetSet(S, n, n);
  remainingSelectedQuestions := S;
  var remainingSelectedQuestionsEmpty:bool;
  remainingSelectedQuestionsEmpty, counter := remainingSelectedQuestions.IsEmpty(counter);
  ghost var setStart := counter;
  LinearLoopBudgetZero(setStart, PolyCandidate(n));
  while !remainingSelectedQuestionsEmpty
    // Termination
    decreases remainingSelectedQuestions.Cardinality0()
    invariant remainingSelectedQuestionsEmpty ==
      (remainingSelectedQuestions.Model() == {})
    // Types
    invariant remainingSelectedQuestions.UCardinality0() <= n
    invariant remainingSelectedQuestions.USize1() <= n
    invariant remainingSelectedQuestions.Cardinality0() <= S.Cardinality0()
    invariant fitness.UCardinality() <= population + S.Cardinality0() - remainingSelectedQuestions.Cardinality0()
    invariant multiplicity.UCardinality() <= population + S.Cardinality0() - remainingSelectedQuestions.Cardinality0()
    invariant fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
    invariant fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
    invariant remainingSelectedQuestions.Valid()
    invariant fitness.Valid()
    invariant multiplicity.Valid()
    // Counter
    invariant counter <= LinearLoopBudget(setStart, PolyCandidate(n), S.Cardinality0() - remainingSelectedQuestions.Cardinality0())
  {
    LinearLoopBudgetStep(setStart, PolyCandidate(n), S.Cardinality0() - remainingSelectedQuestions.Cardinality0());
    remainingSelectedQuestions, fitness, multiplicity, remainingSelectedQuestionsEmpty, counter :=
      BuildSetCandidatesLoop(remainingSelectedQuestions, fitness, multiplicity, S, privateQuestion, n, counter);
  }
  LinearLoopBudgetBound(setStart, PolyCandidate(n), S.Cardinality0(), n);
}

// Add a null candidate, with multiplicity omega^2
method AddNullCandidate(S:SetSet<int>, privateQuestion:Set<int>,
    fitness_in:Map_MapSet_T<int, bool, bool>, multiplicity_in:Map_MapSet_T<int, bool, nat>,
    nullMultiplicity:nat, ghost population:nat, ghost n:nat, ghost counter_in:nat)
    returns (fitness:Map_MapSet_T<int, bool, bool>,
             multiplicity:Map_MapSet_T<int, bool, nat>, ghost counter:nat)
  // Types in
  requires S.Valid() && S.UCardinality0() < n && S.USize1() <= n
  requires privateQuestion.Valid() && privateQuestion.USize0() <= n
  requires population < n
  requires fitness_in.Valid() && multiplicity_in.Valid()
  requires fitness_in.UCardinality() <= population && multiplicity_in.UCardinality() <= population
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // Types out
  ensures fitness.Valid() && multiplicity.Valid()
  ensures fitness.UCardinality() <= population + 1
  ensures multiplicity.UCardinality() <= population + 1
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Counter
  ensures counter <= counter_in + CostNew_Map_Set_T() + (n*n + 1) + 1 +
    n*PolyQuestionStep(n) + 2*(n*n*n + 1)
{
  counter := counter_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  UniverseSizeBound_Map_MapSet_T(fitness_in, n, n, n);
  UniverseSizeBound_Map_MapSet_T(multiplicity_in, n, n, n);
  // The unique fit candidate answers false to every question.
  var nullCandidate:Map_Set_T<int, bool>;
  nullCandidate, counter := New_Map_Set_T(counter);
  var remainingQuestions:SetSet<int>;
  UniverseSizeBound_SetSet(S, n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter);
  ghost var nullStart := counter;
  LinearLoopBudgetZero(nullStart, PolyQuestionStep(n));
  while !remainingQuestionsEmpty
    // Termination
    decreases remainingQuestions.Cardinality0()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Types
    invariant remainingQuestions.UCardinality0() <= n
    invariant remainingQuestions.Cardinality0() <= S.Cardinality0()
    invariant nullCandidate.UCardinality() + remainingQuestions.Cardinality0() <= S.Cardinality0()
    invariant remainingQuestions.USize1() <= n
    invariant nullCandidate.Valid()
    invariant nullCandidate.UCardinalityKeys() <= n
    invariant remainingQuestions.Valid()
    // Counter
    invariant counter <= LinearLoopBudget(nullStart, PolyQuestionStep(n),
      S.Cardinality0() - remainingQuestions.Cardinality0())
  {
    LinearLoopBudgetStep(nullStart, PolyQuestionStep(n), S.Cardinality0() - remainingQuestions.Cardinality0());
    remainingQuestions, nullCandidate, remainingQuestionsEmpty, counter :=
      AddNullCandidateLoop(remainingQuestions, nullCandidate, n, counter);
  }
  LinearLoopBudgetBound(nullStart, PolyQuestionStep(n), S.Cardinality0(), n);
  UniverseSizeBound_Map_Set_T(nullCandidate, n, n);
  nullCandidate, counter := nullCandidate.Insert(privateQuestion, false, counter);
  ModelSizeBound_Map_Set_T(nullCandidate);
  fitness, counter := fitness.Insert(nullCandidate, true, counter);
  multiplicity, counter := multiplicity.Insert(nullCandidate, nullMultiplicity, counter);
}

// Build one element's answer map and add its multiplicity, merging coincident candidates.
method BuildElementCandidatesLoop(
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
  requires privateQuestion.Valid() && privateQuestion.USize0() <= n
  requires remainingElements_in.Valid()
  requires fitness_in.Valid()
  requires multiplicity_in.Valid()
  requires S.Valid()
  requires remainingElements_in.UCardinality0() <= n
  requires S.UCardinality0() < n
  requires S.USize1() <= n
  requires fitness_in.UCardinality() < n && multiplicity_in.UCardinality() < n
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // Termination out
  ensures remainingElementsEmpty == (remainingElements.Model() == {})
  ensures remainingElements.Cardinality0() == remainingElements_in.Cardinality0() - 1
  // Types out
  ensures remainingElements.Valid()
  ensures fitness.Valid()
  ensures multiplicity.Valid()
  ensures fitness.UCardinality() <= fitness_in.UCardinality() + 1
  ensures multiplicity.UCardinality() <= multiplicity_in.UCardinality() + 1
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Invariant out
  ensures remainingElements.Universe() == remainingElements_in.Universe()
  // Counter
  ensures counter <= counter_in + PolyCandidate(n)
{
  UniverseSizeBound_Map_MapSet_T(fitness_in, n, n, n);
  UniverseSizeBound_Map_MapSet_T(multiplicity_in, n, n, n);
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
  UniverseSizeBound_SetSet(S, n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter);
  ghost var questionStart := counter;
  LinearLoopBudgetZero(questionStart, PolyQuestionStep(n));
  while !remainingQuestionsEmpty
    // Termination
    decreases remainingQuestions.Cardinality0()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Types
    invariant candidate.Valid()
    invariant candidate.UCardinalityKeys() <= n
    invariant remainingQuestions.Valid()
    invariant remainingQuestions.UCardinality0() <= n
    invariant remainingQuestions.Cardinality0() <= S.Cardinality0()
    invariant candidate.UCardinality() + remainingQuestions.Cardinality0() <= S.Cardinality0()
    invariant remainingQuestions.USize1() <= n
    // Counter
    invariant counter <= LinearLoopBudget(questionStart, PolyQuestionStep(n),
      S.Cardinality0() - remainingQuestions.Cardinality0())
  {
    LinearLoopBudgetStep(questionStart, PolyQuestionStep(n), S.Cardinality0() - remainingQuestions.Cardinality0());
    remainingQuestions, candidate, remainingQuestionsEmpty, counter :=
      BuildElementCandidateQuestionsLoop(remainingQuestions, candidate, element, n, counter);
  }
  LinearLoopBudgetBound(questionStart, PolyQuestionStep(n), S.Cardinality0(), n);
  UniverseSizeBound_Map_Set_T(candidate, n, n);
  candidate, counter := candidate.Insert(privateQuestion, false, counter);
  ModelSizeBound_Map_Set_T(candidate);

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
  remainingElementsEmpty, counter := remainingElements.IsEmpty(counter);
  reveal PolyCandidate();
}
// Record whether the element belongs to one question's set, then consume that question.
method BuildElementCandidateQuestionsLoop(
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
  requires candidate_in.UCardinalityKeys() <= n
  requires remainingQuestions_in.UCardinality0() <= n
  requires candidate_in.UCardinality() <= n
  requires remainingQuestions_in.USize1() <= n
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality0() == remainingQuestions_in.Cardinality0() - 1
  ensures remainingQuestions.Valid()
  ensures candidate.Valid()
  ensures candidate.UCardinalityKeys() <= n
  ensures candidate.UCardinality() <= candidate_in.UCardinality() + 1
  ensures remainingQuestions.USize1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  ensures counter <= counter_in + PolyQuestionStep(n)
{
  UniverseSizeBound_SetSet(remainingQuestions_in, n, n);
  UniverseSizeBound_Map_Set_T(candidate_in, n, n);
  reveal PolyQuestionStep();
  remainingQuestions := remainingQuestions_in;
  candidate := candidate_in;
  counter := counter_in;

  var question:Set<int>;
  question, counter := remainingQuestions.Pick(counter);
  var answer:bool;
  answer, counter := question.Contains(element, counter);
  candidate, counter := candidate.Insert(question, answer, counter);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter);
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter);
}


// Add a unit-multiplicity set candidate answering true to its own question and the private question.
method BuildSetCandidatesLoop(
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
  requires privateQuestion.Valid() && privateQuestion.USize0() <= n
  requires remainingSelectedQuestions_in.Valid()
  requires fitness_in.Valid()
  requires multiplicity_in.Valid()
  requires S.Valid()
  requires remainingSelectedQuestions_in.UCardinality0() <= n
  requires remainingSelectedQuestions_in.USize1() <= n
  requires S.UCardinality0() < n
  requires S.USize1() <= n
  requires fitness_in.UCardinality() < n && multiplicity_in.UCardinality() < n
  requires fitness_in.UCardinalityKeys() <= n && multiplicity_in.UCardinalityKeys() <= n
  requires fitness_in.UCardinalityKeysKeys() <= n && multiplicity_in.UCardinalityKeysKeys() <= n
  // Termination out
  ensures remainingSelectedQuestionsEmpty == (remainingSelectedQuestions.Model() == {})
  ensures remainingSelectedQuestions.Cardinality0() == remainingSelectedQuestions_in.Cardinality0() - 1
  // Types out
  ensures remainingSelectedQuestions.Valid()
  ensures fitness.Valid()
  ensures multiplicity.Valid()
  ensures remainingSelectedQuestions.USize1() <= n
  ensures fitness.UCardinality() <= fitness_in.UCardinality() + 1
  ensures multiplicity.UCardinality() <= multiplicity_in.UCardinality() + 1
  ensures fitness.UCardinalityKeys() <= n && multiplicity.UCardinalityKeys() <= n
  ensures fitness.UCardinalityKeysKeys() <= n && multiplicity.UCardinalityKeysKeys() <= n
  // Invariant out
  ensures remainingSelectedQuestions.Universe() == remainingSelectedQuestions_in.Universe()
  // Counter
  ensures counter <= counter_in + PolyCandidate(n)
{
  UniverseSizeBound_Map_MapSet_T(fitness_in, n, n, n);
  UniverseSizeBound_Map_MapSet_T(multiplicity_in, n, n, n);
  remainingSelectedQuestions := remainingSelectedQuestions_in;
  fitness := fitness_in;
  multiplicity := multiplicity_in;
  counter := counter_in;

  var selectedQuestion:Set<int>;
  UniverseSizeBound_SetSet(remainingSelectedQuestions_in, n, n);
  selectedQuestion, counter := remainingSelectedQuestions.Pick(counter);
  remainingSelectedQuestions, counter := remainingSelectedQuestions.Remove(selectedQuestion, counter);

  var candidate:Map_Set_T<int, bool>;
  candidate, counter := New_Map_Set_T(counter);
  var remainingQuestions:SetSet<int>;
  UniverseSizeBound_SetSet(S, n, n);
  remainingQuestions := S;
  var remainingQuestionsEmpty:bool;
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter);
  ghost var questionStart := counter;
  LinearLoopBudgetZero(questionStart, PolyQuestionStep(n));
  while !remainingQuestionsEmpty
    // Termination
    decreases remainingQuestions.Cardinality0()
    invariant remainingQuestionsEmpty == (remainingQuestions.Model() == {})
    // Types
    invariant candidate.Valid()
    invariant candidate.UCardinalityKeys() <= n
    invariant remainingQuestions.Valid()
    invariant remainingQuestions.UCardinality0() <= n
    invariant remainingQuestions.Cardinality0() <= S.Cardinality0()
    invariant candidate.UCardinality() + remainingQuestions.Cardinality0() <= S.Cardinality0()
    invariant remainingQuestions.USize1() <= n
    // Counter
    invariant counter <= LinearLoopBudget(questionStart, PolyQuestionStep(n),
      S.Cardinality0() - remainingQuestions.Cardinality0())
  {
    LinearLoopBudgetStep(questionStart, PolyQuestionStep(n), S.Cardinality0() - remainingQuestions.Cardinality0());
    remainingQuestions, candidate, remainingQuestionsEmpty, counter :=
      BuildSetCandidateQuestionsLoop(remainingQuestions, candidate, selectedQuestion, n, counter);
  }
  LinearLoopBudgetBound(questionStart, PolyQuestionStep(n), S.Cardinality0(), n);
  UniverseSizeBound_Map_Set_T(candidate, n, n);
  candidate, counter := candidate.Insert(privateQuestion, true, counter);
  ModelSizeBound_Map_Set_T(candidate);
  fitness, counter := fitness.Insert(candidate, false, counter);
  multiplicity, counter := multiplicity.Insert(candidate, 1, counter);
  remainingSelectedQuestionsEmpty, counter := remainingSelectedQuestions.IsEmpty(counter);
  reveal PolyCandidate();
}
// Record whether one question is the selected set's question, then advance the traversal.
method BuildSetCandidateQuestionsLoop(
    remainingQuestions_in:SetSet<int>,
    candidate_in:Map_Set_T<int, bool>,
    selectedQuestion:Set<int>,
    ghost n:nat, ghost counter_in:nat)
    returns (remainingQuestions:SetSet<int>,
             candidate:Map_Set_T<int, bool>,
             remainingQuestionsEmpty:bool,
             ghost counter:nat)
  requires remainingQuestions_in.Model() != {}
  requires selectedQuestion.Valid() && selectedQuestion.USize0() <= n
  requires remainingQuestions_in.Valid()
  requires candidate_in.Valid()
  requires candidate_in.UCardinalityKeys() <= n
  requires remainingQuestions_in.UCardinality0() <= n
  requires candidate_in.UCardinality() <= n
  requires remainingQuestions_in.USize1() <= n
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality0() == remainingQuestions_in.Cardinality0() - 1
  ensures remainingQuestions.Valid()
  ensures candidate.Valid()
  ensures candidate.UCardinalityKeys() <= n
  ensures candidate.UCardinality() <= candidate_in.UCardinality() + 1
  ensures remainingQuestions.USize1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  ensures counter <= counter_in + PolyQuestionStep(n)
{
  UniverseSizeBound_SetSet(remainingQuestions_in, n, n);
  UniverseSizeBound_Map_Set_T(candidate_in, n, n);
  reveal PolyQuestionStep();
  remainingQuestions := remainingQuestions_in;
  candidate := candidate_in;
  counter := counter_in;

  var question:Set<int>;
  question, counter := remainingQuestions.Pick(counter);
  var answer:bool;
  answer, counter := question.Equal(selectedQuestion, counter);
  candidate, counter := candidate.Insert(question, answer, counter);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter);
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter);
}


// Extend the null candidate with a false answer to one remaining question.
method AddNullCandidateLoop(
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
  requires nullCandidate_in.UCardinalityKeys() <= n
  requires remainingQuestions_in.UCardinality0() <= n
  requires nullCandidate_in.UCardinality() <= n
  requires remainingQuestions_in.USize1() <= n
  ensures remainingQuestionsEmpty == (remainingQuestions.Model() == {})
  ensures remainingQuestions.Cardinality0() == remainingQuestions_in.Cardinality0() - 1
  ensures remainingQuestions.Valid()
  ensures nullCandidate.Valid()
  ensures nullCandidate.UCardinalityKeys() <= n
  ensures nullCandidate.UCardinality() <= nullCandidate_in.UCardinality() + 1
  ensures remainingQuestions.USize1() <= n
  ensures remainingQuestions.Universe() == remainingQuestions_in.Universe()
  ensures counter <= counter_in + PolyQuestionStep(n)
{
  UniverseSizeBound_SetSet(remainingQuestions_in, n, n);
  UniverseSizeBound_Map_Set_T(nullCandidate_in, n, n);
  reveal PolyQuestionStep();
  remainingQuestions := remainingQuestions_in;
  nullCandidate := nullCandidate_in;
  counter := counter_in;

  var question:Set<int>;
  question, counter := remainingQuestions.Pick(counter);
  nullCandidate, counter := nullCandidate.Insert(question, false, counter);
  remainingQuestions, counter := remainingQuestions.Remove(question, counter);
  remainingQuestionsEmpty, counter := remainingQuestions.IsEmpty(counter);
}


// Compute the privacy lower and fitness upper thresholds, returning zero for a zero denominator.
method ComputeThresholds(universeSize:nat, sourceSetCount:nat, k:nat, omega:nat)
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


ghost function {:opaque} PolyQuestionStep(n:nat):nat
{ 3*(n + 1) + 2*(n*n + 1) + 1 }

ghost function {:opaque} PolyCandidate(n:nat):nat
{
  3*(n + 1) + 2*(n*n + 1) + 4*(n*n*n + 1) + CostNew_Map_Set_T() + 3 +
  n*PolyQuestionStep(n)
}

ghost function {:opaque} PolyPrepare(n:nat):nat
{ CostNew_Set() + (n*n + 1) + 1 }

ghost function {:opaque} PolyPositiveCase(n:nat):nat
{ CostNew_Map_Set_T() + 2*CostNew_Map_MapSet_T() + 2*CostNew_SetSet() + (n*n + 1) + 3*(n + 1) }

ghost function {:opaque} PolyNontrivialCase(n:nat):nat
{
  2*CostNew_Map_MapSet_T() + CostNew_Map_Set_T() + CostNew_SetSet() +
  3*(n*n + 1) + 2*(n*n*n + 1) + 5 +
  2*n*PolyCandidate(n) + n*PolyQuestionStep(n)
}

// Fixed polynomial witness, independent of k and of output map contents.
ghost function PolySetCoverToCDPC(n:nat):nat
{ 12*n*n*n*n + 14*n*n*n + 26*n*n + 35*n + 26 }

// Identify the sum of phase bounds with the fixed degree-four polynomial.
lemma PolySetCoverToCDPCComposition(n:nat)
  ensures PolyPrepare(n) + PolyPositiveCase(n) + PolyNontrivialCase(n) == PolySetCoverToCDPC(n)
{
  reveal PolyPrepare(), PolyPositiveCase(), PolyNontrivialCase();
  reveal PolyCandidate(), PolyQuestionStep();
}

// Compose the three population phases and final output operations outside collection contexts.
lemma CostNontrivialBound(n:nat, start:nat, prepared:nat, spent:nat)
  requires prepared <= start + 2*CostNew_Map_MapSet_T() + CostNew_Map_Set_T() +
    (n*n + 1) + 2*(n*n*n + 1) + 4 +
    2*n*PolyCandidate(n) + n*PolyQuestionStep(n)
  requires spent <= prepared + CostNew_SetSet() + 2*(n*n + 1) + 1
  ensures spent <= start + PolyNontrivialCase(n)
{ reveal PolyNontrivialCase(); }
