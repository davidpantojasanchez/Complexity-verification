include "../Problems/SetCover.dfy"
include "../Problems/CDPC.dfy"

/*
Reduccion matemática Set Cover -> CDPC

Las preguntas son los propios conjuntos de S. Tras eliminar el conjunto vacío de S, {} queda reservado como pregunta privada
*/

ghost function SetCoverToCDPC<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
    : (r:(set<set<T>>, map<Candidate<set<T>>, bool>, map<Candidate<set<T>>, nat>, set<set<T>>, real, real, real, real))
  requires SetCoverValidInstance(U, S)
  ensures CDPCValidInstance(r.0, r.1, r.2, r.3, r.4, r.5, r.6, r.7)
{
  var nonemptySets := S - {{}};
  SetCoverWithoutEmpty(U, S, k);
  if |nonemptySets| <= k then
    SetCoverToCDPCPositiveInstance<T>()
  else
    SetCoverToCDPCNontrivial(U, nonemptySets, k)
}

ghost function SetCoverToCDPCPositiveInstance<T(!new)>()
    : (r:(set<set<T>>, map<Candidate<set<T>>, bool>, map<Candidate<set<T>>, nat>, set<set<T>>, real, real, real, real))
  ensures CDPCValidInstance(r.0, r.1, r.2, r.3, r.4, r.5, r.6, r.7)
  ensures CDPC(r.0, r.1, r.2, r.3, r.4, r.5, r.6, r.7)
{
  var candidate:Candidate<set<T>> := map[{} := false];
  var fitness := map[candidate := true];
  var multiplicity:map<Candidate<set<T>>, nat> := map[candidate := 1];
  SetCoverToCDPCPositiveInstanceCorrect<T>();
  ({{}}, fitness, multiplicity, {}, 0.0, 1.0, 0.0, 1.0)
}

ghost function SetCoverToCDPCNontrivial<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
    : (r:(set<set<T>>, map<Candidate<set<T>>, bool>, map<Candidate<set<T>>, nat>, set<set<T>>, real, real, real, real))
  requires SetCoverValidInstance(U, S)
  requires {} !in S
  requires k < |S|
  ensures CDPCValidInstance(r.0, r.1, r.2, r.3, r.4, r.5, r.6, r.7)
  ensures r.0 == S + {{}}
  ensures r.3 == {{}}
{
  assert IsCover(U, S);
  assert U != {} by {
    var s :| s in S;
    assert s != {} && s <= U;
  }
  var omega := 2 * |U| * |S|;
  assert omega > 0;
  var a := SetCoverToCDPCPrivateLower(|U|, |S|, k, omega);
  var y := SetCoverToCDPCFitnessUpper(|S|, omega);

  var elementCandidates := set u | u in U :: SetCoverToCDPCElementCandidate(S, u);
  var setCandidates := set s | s in S :: SetCoverToCDPCSetCandidate(S, s);
  var nullCandidate := SetCoverToCDPCNullCandidate(S);
  var candidates := elementCandidates + setCandidates + {nullCandidate};

  // La cobertura separa los elementos del tipo nulo.
  // La pregunta privada separa los tipos de conjunto de los otros dos grupos.
  forall u | u in U
    ensures SetCoverToCDPCElementCandidate(S, u) != nullCandidate
  {
    var s :| s in S && u in s;
    assert SetCoverToCDPCElementCandidate(S, u)[s];
    assert !nullCandidate[s];
  }
  assert nullCandidate !in elementCandidates;
  assert elementCandidates * setCandidates == {};
  assert nullCandidate !in setCandidates;

  var fitness := map c | c in candidates :: c == nullCandidate;
  // Varios elementos pueden generar el mismo mapa: conservar toda su suma.
  var multiplicity := map c | c in candidates :: SetCoverToCDPCCandidateMultiplicity(U, S, omega, c);

  assert fitness.Keys == multiplicity.Keys == candidates;
  assert forall c | c in candidates :: multiplicity[c] > 0;
  assert forall c | c in candidates :: c.Keys == S + {{}};
  CDPCValidInstanceDefinition(
    S + {{}}, fitness, multiplicity, {{}}, a, 1.0, 0.0, y);
  (S + {{}}, fitness, multiplicity, {{}}, a, 1.0, 0.0, y)
}

// Generadores de tipos de candidato
ghost function {:opaque} SetCoverToCDPCElementCandidate<T(!new)>(S:set<set<T>>, u:T) : (c:Candidate<set<T>>)
  ensures c.Keys == S + {{}}
  ensures !c[{}]
  ensures forall s | s in S :: c[s] == (u in s)
{
  map s | s in S + {{}} :: u in s
}

ghost function {:opaque} SetCoverToCDPCSetCandidate<T(!new)>(S:set<set<T>>, selected:set<T>) : (c:Candidate<set<T>>)
  requires {} !in S
  requires selected in S
  ensures c.Keys == S + {{}}
  ensures c[{}]
  ensures forall s | s in S :: c[s] == (s == selected)
{
  map s | s in S + {{}} :: s == {} || s == selected
}

ghost function {:opaque} SetCoverToCDPCNullCandidate<T(!new)>(S:set<set<T>>) : (c:Candidate<set<T>>)
  ensures c.Keys == S + {{}}
  ensures forall s | s in c.Keys :: !c[s]
{
  map s | s in S + {{}} :: false
}

// La opacidad separa la aritmetica de las obligaciones sobre mapas.
// Revelar estas definiciones al demostrar las identidades de sumas y umbrales.
// Null    -> Omega^2
// Element -> Omega
// Set     -> 1
ghost function {:opaque} SetCoverToCDPCCandidateMultiplicity<T(!new)>(U:set<T>, S:set<set<T>>, omega:nat, candidate:Candidate<set<T>>) : (multiplicity:nat)
  requires omega > 0
  ensures multiplicity > 0
{
  if candidate == SetCoverToCDPCNullCandidate(S) then omega * omega
  else
    var elements := set u | u in U && SetCoverToCDPCElementCandidate(S, u) == candidate;
    if elements != {} then omega * |elements| else 1
}

// Solo buena formacion de umbrales; las desigualdades de correccion faltan.
ghost function {:opaque} SetCoverToCDPCPrivateLower(n:nat, s:nat, k:nat, omega:nat) : (a:real)
  requires 0 < n && k < s && 0 < omega
  ensures 0.0 < a <= 1.0
{
  ((s - k) as real) / ((n * omega + omega * omega + s - k) as real)
}

ghost function {:opaque} SetCoverToCDPCFitnessUpper(s:nat, omega:nat) : (y:real)
  requires 0 < s && 0 < omega
  ensures 0.0 < y < 1.0
{
  ((omega * omega) as real) / ((omega * omega + s) as real)
}

// Primer paso comun a las dos implicaciones de la reduccion.
lemma SetCoverWithoutEmpty<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures IsCover(U, S - {{}})
  ensures SetCover(U, S, k) == SetCover(U, S - {{}}, k)
{
  forall u | u in U
    ensures exists s | s in S - {{}} :: u in s
  {
    var s :| s in S && u in s;
    assert s != {};
  }
  if SetCover(U, S, k) {
    var cover :| SetCoverCertificate(U, S, k, cover);
    assert SetCoverCertificate(U, S, k, cover);
    forall u | u in U
      ensures exists s | s in cover - {{}} :: u in s
    {
      var s :| s in cover && u in s;
      assert s != {};
    }
    assert IsCover(U, cover - {{}});
    assert |cover - {{}}| <= |cover|;
    assert SetCoverCertificate(U, S - {{}}, k, cover - {{}});
  }
  if SetCover(U, S - {{}}, k) {
    var cover :| SetCoverCertificate(U, S - {{}}, k, cover);
    assert SetCoverCertificate(U, S - {{}}, k, cover);
    assert cover <= S;
    assert SetCoverCertificate(U, S, k, cover);
  }
}

lemma SetCoverToCDPCPositiveInstanceCorrect<T(!new)>()
  ensures
    var candidate:Candidate<set<T>> := map[{} := false];
    ghost var fitness := map[candidate := true];
    var multiplicity:map<Candidate<set<T>>, nat> := map[candidate := 1];
    CDPCValidInstance({{}}, fitness, multiplicity, {}, 0.0, 1.0, 0.0, 1.0) &&
      CDPC({{}}, fitness, multiplicity, {}, 0.0, 1.0, 0.0, 1.0)
{
  var candidate:Candidate<set<T>> := map[{} := false];
  var fitness := map[candidate := true];
  var multiplicity:map<Candidate<set<T>>, nat> := map[candidate := 1];

  assert fitness.Keys == {candidate};
  assert multiplicity[candidate] == 1;
  MultiplicitySumSingleton(candidate, multiplicity);
  FitSumDefinition({candidate}, fitness, multiplicity, 1, {candidate});
  assert MultiplicitySum({candidate}, multiplicity, 1);
  assert FitSum({candidate}, fitness, multiplicity, 1);
  assert MultiplicitySum(fitness.Keys, multiplicity, 1);
  assert FitSum(fitness.Keys, fitness, multiplicity, 1);
  assert ClassificationDecided(fitness.Keys, fitness, multiplicity, 0.0, 1.0);
  assert PrivateSafe(fitness.Keys, multiplicity, {}, 0.0, 1.0);
  // End es un testigo de la existencia de una entrevista aceptada por CDPC.
  var questions:set<set<T>> := {{}};
  reveal InterviewFits();
  assert InterviewFits(End, questions);
  reveal CDPCInterviewSemantics();
  assert CDPCInterviewSemantics(fitness, multiplicity, {}, 0.0, 1.0, 0.0, 1.0, fitness.Keys, End);
  assert CDPCCertificate(questions, fitness, multiplicity, {}, 0.0, 1.0, 0.0, 1.0, End);
}

// Su validez estructural esta probada, pero todavia no su aceptacion por CDPCInterviewSemantics.
ghost function SetCoverToCDPCInterview<T(!new)>(cover:set<set<T>>, available:set<set<T>>) : (tree:InterviewModel<set<T>>)
  requires cover <= available
  requires {} !in cover
  ensures InterviewFits(tree, available)
  decreases |cover|
{
  reveal InterviewFits();
  if cover == {} then End
  else
    var question :| question in cover;
    Ask(question, End, SetCoverToCDPCInterview(cover - {question}, available - {question}))
}





// Demonstración


lemma SetCoverToCDPCCorrect<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (questions, fitness, multiplicity, privateQuestions,
               privateLower, privateUpper, fitnessLower, fitnessUpper) :=
            SetCoverToCDPC(U, S, k);
          SetCover(U, S, k) <==> CDPC(
            questions, fitness, multiplicity, privateQuestions,
            privateLower, privateUpper, fitnessLower, fitnessUpper)
{
  SetCoverToCDPCForward(U, S, k);
  SetCoverToCDPCBackward(U, S, k);
}

lemma SetCoverToCDPCForward<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (questions, fitness, multiplicity, privateQuestions, privateLower, privateUpper, fitnessLower, fitnessUpper) :=
            SetCoverToCDPC(U, S, k);
          SetCover(U, S, k) ==> CDPC(
            questions, fitness, multiplicity, privateQuestions,
            privateLower, privateUpper, fitnessLower, fitnessUpper)
  // Caso trivial: usar la postcondicion de SetCoverToCDPCPositiveInstance.
  // Elegir cover <= S - {{}} con |cover| <= k y usar SetCoverToCDPCInterview.
  // Demostrar las sumas ponderadas despues de cada respuesta.
  // Con j respuestas false y r elementos compatibles: suma privada s-j, suma total r*omega + omega^2 + s-j.
  // Una rama true tiene aptitud cero y proporcion privada 1/(r*omega+1). Probar privacidad y clasificacion.


lemma SetCoverToCDPCBackward<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (questions, fitness, multiplicity, privateQuestions,
               privateLower, privateUpper, fitnessLower, fitnessUpper) :=
            SetCoverToCDPC(U, S, k);
          CDPC(questions, fitness, multiplicity, privateQuestions,
               privateLower, privateUpper,
               fitnessLower, fitnessUpper) ==> SetCover(U, S, k)
  // En el caso no trivial, seguir el camino false del tipo nulo.
  // La pregunta privada produciria proporcion privada cero, menor que a.
  // Tras k+1 preguntas de conjuntos, la privacidad tambien falla; acotar solo este camino, sin afirmar una cota global para todo el arbol.
  // Si queda un elemento, la aptitud esta estrictamente entre x e y.
  // Deducir que las preguntas de ese camino cubren U y son a lo sumo k.
