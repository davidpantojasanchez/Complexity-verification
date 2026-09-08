include "../Auxiliary/Interview.dfy"

/*
Weighted semantics of the binary Classification problem with private
characteristics (CDPC).

A candidate type is a total Boolean answer map over the finite question domain.
The fitness and multiplicity maps enumerate only types present in the population.
Multiplicities are kept as integers; they are never expanded into individuals.
*/

type Candidate<Q(==)> = map<Q, bool>

ghost predicate CDPC<Q(!new)>(
    fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>,
    privateLower:real,
    privateUpper:real,
    fitnessLower:real,
    fitnessUpper:real)
  requires CDPCValidInstance(fitness, multiplicity, privateQuestions, privateLower, privateUpper, fitnessLower, fitnessUpper)
{
  exists interview:InterviewModel<Q> | InterviewFits(interview, CDPCQuestions(fitness.Keys)) ::
    CDPCCertificate(
      fitness, multiplicity, privateQuestions,
      privateLower, privateUpper, fitnessLower, fitnessUpper,
      fitness.Keys, interview)
}

ghost predicate CDPCValidInstance<Q(!new)>(
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
  privateQuestions <= CDPCQuestions(fitness.Keys) &&
  (forall candidate | candidate in fitness.Keys ::
    candidate.Keys == CDPCQuestions(fitness.Keys) && multiplicity[candidate] > 0) &&
  0.0 <= privateLower <= privateUpper <= 1.0 &&
  0.0 <= fitnessLower <= fitnessUpper <= 1.0
}

// Complete correctness at the root; CDPCCertificate below is the recursive
// population semantics and intentionally remains separate from tree structure.
ghost predicate CDPCCorrectCertificate<Q(!new)>(
    fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>,
    privateQuestions:set<Q>, privateLower:real, privateUpper:real,
    fitnessLower:real, fitnessUpper:real, interview:InterviewModel<Q>)
  requires CDPCValidInstance(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper)
{
  InterviewFits(interview, CDPCQuestions(fitness.Keys)) &&
  CDPCCertificate(fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper, fitness.Keys, interview)
}

ghost predicate {:opaque} CDPCCertificate<Q(!new)>(
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
    CDPCCertificate(fitness, multiplicity, privateQuestions, privateLower, privateUpper, fitnessLower, fitnessUpper, candidates, interview)
}

// Valid instances have a nonempty population and a common answer domain.
// The chosen representative is ghost; executable callers may pick any candidate.
ghost function CDPCQuestions<Q(!new)>(candidates:set<Candidate<Q>>):(questions:set<Q>)
  requires candidates != {}
  ensures exists candidate | candidate in candidates :: questions == candidate.Keys
{
  var candidate :| candidate in candidates;
  candidate.Keys
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
  exists totalMass:nat, fitMass:nat |
    WeightedMass(candidates, multiplicity, totalMass) &&
    FitMass(candidates, fitness, multiplicity, fitMass) ::
    ((fitMass as real) <= fitnessLower * (totalMass as real) ||
     fitnessUpper * (totalMass as real) <= (fitMass as real))
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
  exists totalMass:nat | WeightedMass(candidates, multiplicity, totalMass) ::
    (forall question | question in privateQuestions ::
      exists privateMass:nat |
        PrivateMass(candidates, question, multiplicity, privateMass) ::
        privateLower * (totalMass as real) <= (privateMass as real) <=
          privateUpper * (totalMass as real))
}

ghost function FilterCandidates<Q(!new)>(candidates:set<Candidate<Q>>, question:Q, answer:bool):set<Candidate<Q>>
  ensures FilterCandidates(candidates, question, answer) <= candidates
{
  set candidate | candidate in candidates && question in candidate && candidate[question] == answer :: candidate
}

// A sequence witnesses a finite sum without selecting an arbitrary ordering as part of the problem input
// Its multiset must contain every type exactly once
ghost predicate {:opaque} WeightedMass<Q(!new)>(candidates:set<Candidate<Q>>, multiplicity:map<Candidate<Q>, nat>, mass:nat)
  requires candidates <= multiplicity.Keys
{
  exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset(candidates) &&
    (forall candidate | candidate in enumeration :: candidate in multiplicity.Keys) ::    // Debería ser consecuencia de la precondición, pero la demostración no es trivial. Dejarlo aquí parece la solución más sencilla. La alternativa sería añadir un lema.
    mass == SequenceWeightedMass(enumeration, multiplicity)
}

// Aux function for WeightedMass
ghost function SequenceWeightedMass<Q(!new)>(candidates:seq<Candidate<Q>>, multiplicity:map<Candidate<Q>, nat>):nat
  requires forall candidate | candidate in candidates :: candidate in multiplicity.Keys
  decreases |candidates|
{
  if candidates == [] then 0
  else multiplicity[candidates[0]] + SequenceWeightedMass(candidates[1..], multiplicity)
}

ghost predicate {:opaque} FitMass<Q(!new)>(candidates:set<Candidate<Q>>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>, mass:nat)
  requires candidates <= multiplicity.Keys
{
  WeightedMass(
    set candidate | candidate in candidates &&
                    candidate in fitness && fitness[candidate] :: candidate,
    multiplicity, mass)
}

ghost predicate {:opaque} PrivateMass<Q(!new)>(candidates:set<Candidate<Q>>, privateQuestion:Q, multiplicity:map<Candidate<Q>, nat>, mass:nat)
  requires candidates <= multiplicity.Keys
{
  WeightedMass(
    set candidate | candidate in candidates &&
                    privateQuestion in candidate && candidate[privateQuestion] :: candidate,
    multiplicity, mass)
}


// Lemmas

// The result does not depend on which representative is chosen.
lemma CDPCQuestionsCommonDomain<Q(!new)>(candidates:set<Candidate<Q>>, questions:set<Q>)
  requires candidates != {}
  requires forall candidate | candidate in candidates :: candidate.Keys == questions
  ensures CDPCQuestions(candidates) == questions
{
  var representative :| representative in candidates &&
    CDPCQuestions(candidates) == representative.Keys;
}

// Equivalence with the former explicit-domain conditions, for any common domain.
lemma CDPCValidInstanceCommonDomain<Q(!new)>(
    questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    privateLower:real, privateUpper:real, fitnessLower:real, fitnessUpper:real)
  requires fitness.Keys != {}
  requires fitness.Keys == multiplicity.Keys
  requires forall candidate | candidate in fitness.Keys :: candidate.Keys == questions
  ensures CDPCValidInstance(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper) ==
      (privateQuestions <= questions &&
       (forall candidate | candidate in fitness.Keys :: multiplicity[candidate] > 0) &&
       0.0 <= privateLower <= privateUpper <= 1.0 &&
       0.0 <= fitnessLower <= fitnessUpper <= 1.0)
{
  CDPCQuestionsCommonDomain(fitness.Keys, questions);
}

lemma CDPCQuestionDomainRegressions()
{
  var first := map[0 := true, 1 := false];
  var second := map[0 := false, 1 := true];
  assert first[0] != second[0];
  assert first != second;
  var fitness := map[first := true, second := false];
  var multiplicity := map[first := 2, second := 1];
  assert first in fitness.Keys;
  assert forall candidate | candidate in fitness.Keys :: candidate.Keys == {0, 1};
  CDPCValidInstanceCommonDomain(
    {0, 1}, fitness, multiplicity, {1}, 0.0, 1.0, 0.0, 1.0);
  assert CDPCValidInstance(fitness, multiplicity, {1}, 0.0, 1.0, 0.0, 1.0);
  assert CDPCQuestions(fitness.Keys) == {0, 1};
  assert !CDPCValidInstance(fitness, multiplicity, {2}, 0.0, 1.0, 0.0, 1.0);
  assert !CDPCValidInstance(fitness, map[first := 0, second := 1], {}, 0.0, 1.0, 0.0, 1.0);
  assert !CDPCValidInstance(fitness, map[first := 1], {}, 0.0, 1.0, 0.0, 1.0);

  var partial := map[0 := false];
  assert !CDPCValidInstance(
    map[first := true, partial := false], map[first := 1, partial := 1],
    {}, 0.0, 1.0, 0.0, 1.0);
  assert !CDPCValidInstance<int>(map[], map[], {}, 0.0, 1.0, 0.0, 1.0);

  // A nonempty population may still have no questions at all.
  var noAnswers:Candidate<int> := map[];
  CDPCQuestionsCommonDomain({noAnswers}, {});
  assert CDPCValidInstance(
    map[noAnswers := true], map[noAnswers := 1], {}, 0.0, 1.0, 0.0, 1.0);
}


lemma FitMassDefinition<Q(!new)>(candidates:set<Candidate<Q>>, fitness:map<Candidate<Q>, bool>, multiplicity:map<Candidate<Q>, nat>, mass:nat, filtered:set<Candidate<Q>>)
  requires candidates <= multiplicity.Keys
  requires filtered ==
    (set candidate | candidate in candidates &&
                     candidate in fitness && fitness[candidate] :: candidate)
  requires WeightedMass(filtered, multiplicity, mass)
  ensures FitMass(candidates, fitness, multiplicity, mass)
{
  reveal FitMass();
}

lemma PrivateMassDefinition<Q(!new)>(candidates:set<Candidate<Q>>, privateQuestion:Q, multiplicity:map<Candidate<Q>, nat>, mass:nat, filtered:set<Candidate<Q>>)
  requires candidates <= multiplicity.Keys
  requires filtered ==
    (set candidate | candidate in candidates &&
                     privateQuestion in candidate && candidate[privateQuestion] :: candidate)
  requires WeightedMass(filtered, multiplicity, mass)
  ensures PrivateMass(candidates, privateQuestion, multiplicity, mass)
{
  reveal PrivateMass();
}

// Small proof-facing boundaries for the recursive definitions.
lemma WeightedMassEmpty<Q(!new)>(multiplicity:map<Candidate<Q>, nat>)
  ensures WeightedMass({}, multiplicity, 0)
{
  reveal WeightedMass();
  var enumeration:seq<Candidate<Q>> := [];
  var empty:set<Candidate<Q>> := {};
  assert multiset(enumeration) == multiset(empty);
  reveal SequenceWeightedMass();
  assert 0 == SequenceWeightedMass(enumeration, multiplicity);
  assert exists enumeration':seq<Candidate<Q>> |
    multiset(enumeration') == multiset(empty) &&
    (forall candidate | candidate in enumeration' :: candidate in multiplicity.Keys) ::
    0 == SequenceWeightedMass(enumeration', multiplicity);
}

lemma WeightedMassSingleton<Q(!new)>(candidate:Candidate<Q>, multiplicity:map<Candidate<Q>, nat>)
  requires candidate in multiplicity.Keys
  ensures WeightedMass(
    {candidate}, multiplicity, multiplicity[candidate])
{
  reveal WeightedMass();
  assert multiset([candidate]) == multiset({candidate});
  reveal SequenceWeightedMass();
  assert SequenceWeightedMass([candidate], multiplicity) ==
         multiplicity[candidate];
  assert exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset({candidate}) &&
    (forall enumerated | enumerated in enumeration :: enumerated in multiplicity.Keys) ::
    multiplicity[candidate] ==
      SequenceWeightedMass(enumeration, multiplicity);
}

lemma WeightedMassPair<Q(!new)>(first:Candidate<Q>, second:Candidate<Q>, multiplicity:map<Candidate<Q>, nat>)
  requires first != second
  requires first in multiplicity.Keys
  requires second in multiplicity.Keys
  ensures WeightedMass(
    {first, second}, multiplicity,
    multiplicity[first] + multiplicity[second])
{
  reveal WeightedMass();
  assert multiset([first, second]) == multiset({first, second});
  reveal SequenceWeightedMass();
  assert SequenceWeightedMass([], multiplicity) == 0;
  assert SequenceWeightedMass([second], multiplicity) ==
         multiplicity[second];
  assert SequenceWeightedMass([first, second], multiplicity) ==
         multiplicity[first] + multiplicity[second];
  assert exists enumeration:seq<Candidate<Q>> |
    multiset(enumeration) == multiset({first, second}) &&
    (forall candidate | candidate in enumeration :: candidate in multiplicity.Keys) ::
    multiplicity[first] + multiplicity[second] ==
        SequenceWeightedMass(enumeration, multiplicity);
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
  ensures CDPCCertificate(
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
  requires CDPCCertificate(
    fitness, multiplicity, privateQuestions,
    privateLower, privateUpper, fitnessLower, fitnessUpper,
    candidates, End)
  ensures PrivateSafe(candidates, multiplicity, privateQuestions,
                      privateLower, privateUpper)
  ensures ClassificationDecided(candidates, fitness, multiplicity,
                                fitnessLower, fitnessUpper)
{
  reveal CDPCCertificate();
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
  requires interview.Ask?
  requires candidates != {}
  requires candidates <= fitness.Keys
  requires candidates <= multiplicity.Keys
  requires CDPCCertificate(
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
  reveal CDPCCertificate();
}

/*

// Semantic regressions for the boundary cases that were unsound in the
// historical specification.
lemma UnequalWeightsRegression()
  ensures
    var answersTrue := map[0 := true];
    var answersFalse := map[0 := false];
    var multiplicity := map[answersTrue := 3, answersFalse := 1];
    WeightedMass({answersTrue, answersFalse}, multiplicity, 4) &&
    PrivateMass({answersTrue, answersFalse}, 0, multiplicity, 3)
{
  var answersTrue := map[0 := true];
  var answersFalse := map[0 := false];
  var multiplicity := map[answersTrue := 3, answersFalse := 1];
  assert answersTrue[0] != answersFalse[0];
  assert answersTrue != answersFalse;
  WeightedMassPair(answersTrue, answersFalse, multiplicity);
  reveal PrivateMass();
  var privateCandidates :=
    set candidate | candidate in {answersTrue, answersFalse} &&
                    0 in candidate && candidate[0] :: candidate;
  assert privateCandidates == {answersTrue};
  WeightedMassSingleton(answersTrue, multiplicity);
  assert WeightedMass({answersTrue}, multiplicity, 3);
  assert WeightedMass(privateCandidates, multiplicity, 3);
  assert (set candidate | candidate in {answersTrue, answersFalse} &&
                          0 in candidate && candidate[0] :: candidate)
         == privateCandidates;
  assert WeightedMass(
    set candidate | candidate in {answersTrue, answersFalse} &&
                    0 in candidate && candidate[0] :: candidate,
    multiplicity, 3);
  PrivateMassDefinition(
    {answersTrue, answersFalse}, 0, multiplicity, 3, privateCandidates);
  assert PrivateMass({answersTrue, answersFalse}, 0, multiplicity, 3);
}

lemma EmptyPopulationIsMalformed()
  ensures !CDPCValidInstance<int>(
    map[], map[], {}, 0.0, 1.0, 0.0, 1.0)
{
  reveal CDPCValidInstance();
}

lemma ZeroWeightIsMalformed()
  ensures
    var candidate := map[0 := true];
    !CDPCValidInstance<int>(
      map[candidate := true], map[candidate := 0], {},
      0.0, 1.0, 0.0, 1.0)
{
  reveal CDPCValidInstance();
}

lemma InclusiveThresholdRegression()
  ensures
    var candidate := map[0 := true];
    CDPCValidInstance<int>(
      map[candidate := true], map[candidate := 3], {0},
      1.0, 1.0, 0.0, 1.0) &&
      CDPC<int>(
        map[candidate := true], map[candidate := 3], {0},
        1.0, 1.0, 0.0, 1.0)
{
  var candidate := map[0 := true];
  var fitness := map[candidate := true];
  var multiplicity := map[candidate := 3];
  assert fitness.Keys == {candidate};
  assert multiplicity.Keys == {candidate};
  assert candidate.Keys == {0};
  assert candidate in fitness.Keys;
  assert fitness.Keys != {};
  assert multiplicity[candidate] > 0;
  assert CDPCValidInstance(
    fitness, multiplicity, {0}, 1.0, 1.0, 0.0, 1.0) by {
    reveal CDPCValidInstance();
  }
  assert InterviewFits(End, {0}) by {
    reveal InterviewFits();
  }
  WeightedMassSingleton(candidate, multiplicity);
  assert WeightedMass({candidate}, multiplicity, 3);
  var privateCandidates := set c | c in {candidate} && 0 in c && c[0] :: c;
  var fitCandidates :=
    set c | c in {candidate} && c in fitness && fitness[c] :: c;
  assert privateCandidates == {candidate};
  assert fitCandidates == {candidate};
  assert WeightedMass(privateCandidates, multiplicity, 3);
  assert WeightedMass(fitCandidates, multiplicity, 3);
  assert (set c | c in {candidate} && 0 in c && c[0] :: c)
         == privateCandidates;
  assert (set c | c in {candidate} && c in fitness && fitness[c] :: c)
         == fitCandidates;
  assert WeightedMass(
    set c | c in {candidate} && 0 in c && c[0] :: c,
    multiplicity, 3);
  assert WeightedMass(
    set c | c in {candidate} && c in fitness && fitness[c] :: c,
    multiplicity, 3);
  PrivateMassDefinition({candidate}, 0, multiplicity, 3, privateCandidates);
  FitMassDefinition({candidate}, fitness, multiplicity, 3, fitCandidates);
  assert PrivateMass({candidate}, 0, multiplicity, 3);
  assert FitMass({candidate}, fitness, multiplicity, 3);
  assert PrivateSafe({candidate}, multiplicity, {0}, 1.0, 1.0) by {
    reveal PrivateSafe();
  }
  assert ClassificationDecided(
    {candidate}, fitness, multiplicity, 0.0, 1.0) by {
    reveal ClassificationDecided();
  }
  assert CDPCCertificate(
    fitness, multiplicity, {0}, 1.0, 1.0, 0.0, 1.0,
    {candidate}, End) by {
    reveal CDPCCertificate();
  }
  reveal CDPC();
}

lemma RepeatedQuestionStructureRejected()
  ensures
    var repeated := Ask(0, Ask(0, End, End), End);
    !InterviewFits(repeated, {0})
{
  reveal InterviewFits();
}

*/
