include "../Collections/Interview.dfy"

/*
Multiplicity-based semantics of the binary Classification problem with private
characteristics (CDPC).

A candidate type is a total Boolean answer map over the finite question domain.
The fitness and multiplicity maps enumerate only types present in the population.
Multiplicities are kept as integers; they are never expanded into individuals.
*/

type Candidate<Q(==)> = map<Q, bool>

ghost predicate CDPC<Q(!new)>(
    questions:set<Q>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions, privateLower, privateUpper, fitnessLower, fitnessUpper)
{
  exists interview:InterviewModel<Q> ::
    CDPCCertificate(
      questions, fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      interview)
}

ghost predicate CDPCValidInstance<Q(!new)>(
    questions:set<Q>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real)
{
  fitness.Keys == multiplicity.Keys &&
  fitness.Keys != {} &&
  privateQuestions <= questions &&
  (forall candidate | candidate in fitness.Keys ::
    candidate.Keys == questions && multiplicity[candidate] > 0) &&
  0.0 <= privateLower <= privateUpper <= 1.0 &&
  0.0 <= fitnessLower <= fitnessUpper <= 1.0
}

// Complete correctness at the root; CDPCInterviewSemantics below is the recursive
// population semantics and intentionally remains separate from tree structure.
ghost predicate CDPCCertificate<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, interview:InterviewModel<Q>)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
{
  InterviewFits(interview, questions) &&
  CDPCInterviewSemantics(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, fitness.Keys, interview)
}

ghost predicate {:opaque} CDPCInterviewSemantics<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>,
    interview:InterviewModel<Q>)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  decreases interview, 0
{
  match interview
  // * Caso base
  case End =>
    // Se ha obtenido la información necesaria según x e y
    ClassificationDecided(candidates, fitness, multiplicity, fitnessLower, fitnessUpper) &&
    // Por cada caractrística privada, no se ha inferido más información que la permitida por a y b
    PrivateSafe(candidates, multiplicity, privateQuestions, privateLower, privateUpper)
  // * Casos recursivos
  case Ask(question, whenTrue, whenFalse) =>
    CDPCBranch(
      fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      FilterCandidates(candidates, question, true),
      whenTrue) &&
    CDPCBranch(
      fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      FilterCandidates(candidates, question, false),
      whenFalse)
}

ghost predicate {:opaque} CDPCBranch<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>,
    interview:InterviewModel<Q>)
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  decreases interview, 1
{
  if candidates == {} then interview.End?
  else
    PrivateSafe(candidates, multiplicity, privateQuestions, privateLower, privateUpper) &&      // No es necesario
    CDPCInterviewSemantics(fitness, multiplicity, privateQuestions, privateLower, privateUpper, fitnessLower, fitnessUpper, candidates, interview)
}

ghost predicate ClassificationDecided<Q(!new)>(
    candidates:set<Candidate<Q>>,
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    fitnessLower:real,
    fitnessUpper:real)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
{
  exists totalSum:nat, fitSum:nat |
    MultiplicitySum(candidates, multiplicity, totalSum) &&
    FitSum(candidates, fitness, multiplicity, fitSum) ::
    ((fitSum as real) <= fitnessLower * (totalSum as real) ||
     fitnessUpper * (totalSum as real) <= (fitSum as real))
}

// Cross-products express the inclusive ratio bounds without division.
ghost predicate PrivateSafe<Q(!new)>(
    candidates:set<Candidate<Q>>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real)
  requires candidates != {}
  requires candidates <= multiplicity.Keys
{
  exists totalSum:nat | MultiplicitySum(candidates, multiplicity, totalSum) ::
    (forall question | question in privateQuestions ::
      exists privateSum:nat |
        PrivateSum(candidates, question, multiplicity, privateSum) ::
        privateLower * (totalSum as real) <= (privateSum as real) <=
          privateUpper * (totalSum as real))
}

ghost function FilterCandidates<Q(!new)>(candidates:set<Candidate<Q>>, question:Q, answer:bool):set<Candidate<Q>>
  ensures FilterCandidates(candidates, question, answer) <= candidates
{
  set candidate | candidate in candidates && question in candidate && candidate[question] == answer :: candidate
}

// A sequence witnesses a finite sum without selecting an arbitrary ordering as part of the problem input
// Its multiset must contain every type exactly once
ghost predicate {:opaque} MultiplicitySum<Q(!new)>(candidates:set<Candidate<Q>>, multiplicity:map<Candidate<Q>, nat>, sum:nat)
  requires candidates <= multiplicity.Keys
{
  exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset(candidates) &&
    (forall candidate | candidate in enumeration :: candidate in multiplicity.Keys) ::    // Debería ser consecuencia de la precondición, pero la demostración no es trivial. Dejarlo aquí parece la solución más sencilla. La alternativa sería añadir un lema.
    sum == SequenceMultiplicitySum(enumeration, multiplicity)
}

// Aux function for MultiplicitySum
ghost function SequenceMultiplicitySum<Q(!new)>(candidates:seq<Candidate<Q>>, multiplicity:map<Candidate<Q>, nat>):nat
  requires forall candidate | candidate in candidates :: candidate in multiplicity.Keys
  decreases |candidates|
{
  if candidates == [] then 0
  else multiplicity[candidates[0]] + SequenceMultiplicitySum(candidates[1..], multiplicity)
}

ghost predicate {:opaque} FitSum<Q(!new)>(candidates:set<Candidate<Q>>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>, sum:nat)
  requires candidates <= multiplicity.Keys
{
  MultiplicitySum(
    set candidate | candidate in candidates &&
                    candidate in fitness && fitness[candidate] :: candidate,
    multiplicity, sum)
}

ghost predicate {:opaque} PrivateSum<Q(!new)>(candidates:set<Candidate<Q>>, privateQuestion:Q, multiplicity:map<Candidate<Q>, nat>, sum:nat)
  requires candidates <= multiplicity.Keys
{
  MultiplicitySum(
    set candidate | candidate in candidates &&
                    privateQuestion in candidate && candidate[privateQuestion] :: candidate,
    multiplicity, sum)
}


// Lemmas

// Package the direct validity clauses for construction proofs.
lemma CDPCValidInstanceDefinition<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    privateLower:real, privateUpper:real, fitnessLower:real, fitnessUpper:real)
  requires fitness.Keys == multiplicity.Keys
  requires fitness.Keys != {}
  requires privateQuestions <= questions
  requires forall candidate | candidate in fitness.Keys ::
    candidate.Keys == questions && multiplicity[candidate] > 0
  requires 0.0 <= privateLower <= privateUpper <= 1.0
  requires 0.0 <= fitnessLower <= fitnessUpper <= 1.0
  ensures CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
{
  reveal CDPCValidInstance();
}

// In a valid instance the explicit component agrees with every candidate domain,
// preserving the representative-based interpretation without a second source of truth.
lemma CDPCValidInstanceQuestionsDetermined<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    privateLower:real, privateUpper:real, fitnessLower:real, fitnessUpper:real,
    candidate:Candidate<Q>)
  requires CDPCValidInstance(questions, fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
  requires candidate in fitness.Keys
  ensures candidate.Keys == questions
{
  reveal CDPCValidInstance();
}

lemma CDPCQuestionDomainRegressionCases()
{
  var first := map[0 := true, 1 := false];
  var second := map[0 := false, 1 := true];
  assert first[0] != second[0];
  assert first != second;
  var fitness := map[first := true, second := false];
  var multiplicity := map[first := 2, second := 1];
  assert first in fitness.Keys;
  assert forall candidate | candidate in fitness.Keys :: candidate.Keys == {0, 1};
  assert CDPCValidInstance({0, 1}, fitness, multiplicity, {1}, 0.0, 1.0, 0.0, 1.0);
  CDPCValidInstanceQuestionsDetermined(
    {0, 1}, fitness, multiplicity, {1}, 0.0, 1.0, 0.0, 1.0, first);
  assert !CDPCValidInstance({0, 1}, fitness, multiplicity, {2}, 0.0, 1.0, 0.0, 1.0);
  assert !CDPCValidInstance({0, 1}, fitness, map[first := 0, second := 1], {}, 0.0, 1.0, 0.0, 1.0);
  assert !CDPCValidInstance({0, 1}, fitness, map[first := 1], {}, 0.0, 1.0, 0.0, 1.0);

  var partial := map[0 := false];
  assert !CDPCValidInstance(
    {0, 1},
    map[first := true, partial := false], map[first := 1, partial := 1],
    {}, 0.0, 1.0, 0.0, 1.0);
  assert !CDPCValidInstance<int>({}, map[], map[], {}, 0.0, 1.0, 0.0, 1.0);

  // A nonempty population may still have no questions at all.
  var noAnswers:Candidate<int> := map[];
  assert CDPCValidInstance(
    {}, map[noAnswers := true], map[noAnswers := 1], {}, 0.0, 1.0, 0.0, 1.0);
}


lemma FitSumDefinition<Q(!new)>(candidates:set<Candidate<Q>>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>, sum:nat, filtered:set<Candidate<Q>>)
  requires candidates <= multiplicity.Keys
  requires filtered ==
    (set candidate | candidate in candidates &&
                     candidate in fitness && fitness[candidate] :: candidate)
  requires MultiplicitySum(filtered, multiplicity, sum)
  ensures FitSum(candidates, fitness, multiplicity, sum)
{
  reveal FitSum();
}

lemma PrivateSumDefinition<Q(!new)>(candidates:set<Candidate<Q>>, privateQuestion:Q, multiplicity:map<Candidate<Q>, nat>, sum:nat, filtered:set<Candidate<Q>>)
  requires candidates <= multiplicity.Keys
  requires filtered ==
    (set candidate | candidate in candidates &&
                     privateQuestion in candidate && candidate[privateQuestion] :: candidate)
  requires MultiplicitySum(filtered, multiplicity, sum)
  ensures PrivateSum(candidates, privateQuestion, multiplicity, sum)
{
  reveal PrivateSum();
}

// Small proof-facing boundaries for the recursive definitions.
lemma MultiplicitySumEmpty<Q(!new)>(multiplicity:map<Candidate<Q>, nat>)
  ensures MultiplicitySum({}, multiplicity, 0)
{
  reveal MultiplicitySum();
  var enumeration:seq<Candidate<Q>> := [];
  var empty:set<Candidate<Q>> := {};
  assert multiset(enumeration) == multiset(empty);
  reveal SequenceMultiplicitySum();
  assert 0 == SequenceMultiplicitySum(enumeration, multiplicity);
  assert exists enumeration':seq<Candidate<Q>> |
    multiset(enumeration') == multiset(empty) &&
    (forall candidate | candidate in enumeration' :: candidate in multiplicity.Keys) ::
    0 == SequenceMultiplicitySum(enumeration', multiplicity);
}

lemma MultiplicitySumSingleton<Q(!new)>(candidate:Candidate<Q>, multiplicity:map<Candidate<Q>, nat>)
  requires candidate in multiplicity.Keys
  ensures MultiplicitySum(
    {candidate}, multiplicity, multiplicity[candidate])
{
  reveal MultiplicitySum();
  assert multiset([candidate]) == multiset({candidate});
  reveal SequenceMultiplicitySum();
  assert SequenceMultiplicitySum([candidate], multiplicity) ==
         multiplicity[candidate];
  assert exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset({candidate}) &&
    (forall enumerated | enumerated in enumeration :: enumerated in multiplicity.Keys) ::
    multiplicity[candidate] ==
      SequenceMultiplicitySum(enumeration, multiplicity);
}

lemma MultiplicitySumPair<Q(!new)>(first:Candidate<Q>, second:Candidate<Q>, multiplicity:map<Candidate<Q>, nat>)
  requires first != second
  requires first in multiplicity.Keys
  requires second in multiplicity.Keys
  ensures MultiplicitySum(
    {first, second}, multiplicity,
    multiplicity[first] + multiplicity[second])
{
  reveal MultiplicitySum();
  assert multiset([first, second]) == multiset({first, second});
  reveal SequenceMultiplicitySum();
  assert SequenceMultiplicitySum([], multiplicity) == 0;
  assert SequenceMultiplicitySum([second], multiplicity) ==
         multiplicity[second];
  assert SequenceMultiplicitySum([first, second], multiplicity) ==
         multiplicity[first] + multiplicity[second];
  assert exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset({first, second}) &&
    (forall candidate | candidate in enumeration :: candidate in multiplicity.Keys) ::
    multiplicity[first] + multiplicity[second] ==
        SequenceMultiplicitySum(enumeration, multiplicity);
}

lemma EmptyCDPCBranch<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    interview:InterviewModel<Q>)
  ensures CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    {}, interview) == interview.End?
{
  reveal CDPCBranch();
}

lemma CDPCBranchStep<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>,
    interview:InterviewModel<Q>)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, interview)
  ensures PrivateSafe(candidates, multiplicity, privateQuestions,
                      privateLower, privateUpper)
  ensures CDPCInterviewSemantics(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, interview)
{
  reveal CDPCBranch();
}

lemma CDPCEndStep<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires CDPCInterviewSemantics(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, End)
  ensures PrivateSafe(candidates, multiplicity, privateQuestions,
                      privateLower, privateUpper)
  ensures ClassificationDecided(candidates, fitness, multiplicity,
                                fitnessLower, fitnessUpper)
{
  reveal CDPCInterviewSemantics();
}

lemma CDPCAskStep<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real,
    candidates:set<Candidate<Q>>,
    interview:InterviewModel<Q>)
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires interview.Ask?
  requires CDPCInterviewSemantics(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, interview)
  ensures CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    FilterCandidates(candidates, interview.question, true),
    interview.trueBranch)
  ensures CDPCBranch(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    FilterCandidates(candidates, interview.question, false),
    interview.falseBranch)
{
  reveal CDPCInterviewSemantics();
}
