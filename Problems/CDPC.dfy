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
