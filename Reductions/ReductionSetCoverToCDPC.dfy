include "../Arithmetic/Rationals.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Problems/SetCover.dfy"
include "../Problems/CDPCLemmas.dfy"
/*
Reduction Set Cover -> CDPC
The questions are the sets in S. After removing the empty set from S, {} is reserved as the private question
*/

// Correctness of the reduction


lemma set_cover_to_cdpc_correct<T(!new)>(instance:SetCoverModel<T>)
  requires SetCoverValidInstance(instance)
  ensures SetCover(instance) <==> CDPC(SetCoverToCDPC(instance))
{
  set_cover_to_cdpc_forward(instance);
  set_cover_to_cdpc_backward(instance);
}

lemma set_cover_to_cdpc_forward<T(!new)>(instance:SetCoverModel<T>)
  requires SetCoverValidInstance(instance)
  ensures SetCover(instance) ==> CDPC(SetCoverToCDPC(instance))
  // Unproved. Let source := S - {{}} and call set_cover_without_empty.
  // If |source| <= k, call set_cover_to_cdpc_trivial_correct.
  // Otherwise choose a SetCoverCertificate for source and call
  // set_cover_cdpc_cover_interview_certificate; its InterviewFits guarantee and
  // semantic result supply the existential witness required by CDPC.


lemma set_cover_to_cdpc_backward<T(!new)>(instance:SetCoverModel<T>)
  requires SetCoverValidInstance(instance)
  ensures CDPC(SetCoverToCDPC(instance)) ==> SetCover(instance)
  // Unproved. Let source := S - {{}} and call set_cover_without_empty.
  // If |source| <= k, call set_cover_to_cdpc_trivial_correct.
  // Otherwise choose an interview from CDPC and call
  // set_cover_cdpc_extract_cover to obtain a certificate over source; use
  // set_cover_without_empty to transfer SetCover back to S.

// The following declarations describe outstanding proof obligations. They have
// no bodies: their contracts are not established results and must not be used
// to claim that the reduction has been verified.

// After a fresh set question is answered false, update the null-path population.
lemma set_cover_cdpc_false_population_step<T(!new)>(U:set<T>, S:set<set<T>>, asked:set<set<T>>, question:set<T>)
  requires SetCoverFamilyValid(U, S)
  requires {} !in S
  requires asked <= S
  requires question in S - asked
  ensures FilterCandidates(SetCoverToCDPCFalsePopulation(U, S, asked), question, false) ==
          SetCoverToCDPCFalsePopulation(U, S, asked + {question})
  // Unproved. Reveal SetCoverToCDPCUncovered and use the candidate contracts
  // to show that each group survives exactly when it should.

// Combine the separate sums for the population reached along the false path.
lemma set_cover_cdpc_false_population_sums<T(!new)>(U:set<T>, S:set<set<T>>, asked:set<set<T>>, omega:nat,
    fitness:map<Candidate<set<T>>, bool>, multiplicity:map<Candidate<set<T>>, nat>)
  requires SetCoverFamilyValid(U, S) && {} !in S && asked <= S && 0 < omega
  requires fitness.Keys == multiplicity.Keys
  requires SetCoverToCDPCFalsePopulation(U, S, {}) <= fitness.Keys
  requires SetCoverToCDPCFalsePopulation(U, S, asked) <= multiplicity.Keys
  requires forall candidate | candidate in SetCoverToCDPCFalsePopulation(U, S, {}) ::
    fitness[candidate] == (candidate == SetCoverToCDPCNullCandidate(S)) &&
    multiplicity[candidate] == SetCoverToCDPCCandidateMultiplicity(U, S, omega, candidate)
  ensures var population := SetCoverToCDPCFalsePopulation(U, S, asked);
    MultiplicitySum(population, multiplicity,
      omega*|SetCoverToCDPCUncovered(U, asked)| + omega*omega + |S-asked|) &&
    FitSum(population, fitness, multiplicity, omega*omega) &&
    PrivateSum(population, {}, multiplicity, |S-asked|)
  // Unproved. Establish the nontrivial construction's map bindings; call
  // set_cover_cdpc_false_population_partition, set_cover_cdpc_remaining_element_sum,
  // set_cover_cdpc_remaining_set_sum and multiplicity_sum_singleton. Combine
  // disjoint groups with multiplicity_sum_disjoint_union, then use
  // fit_sum_definition and private_sum_definition. The combined proof previously
  // timed out; split its obligations if necessary without assuming their result.

// A source cover yields the specific interview used by the forward direction.
lemma set_cover_cdpc_cover_interview_certificate<T(!new)>(U:set<T>, S:set<set<T>>, k:nat, cover:set<set<T>>)
  requires SetCoverValidInstance(SetSystemModel(U, S, k))
  requires {} !in S
  requires k < |S|
  requires SetCoverCertificate(SetSystemModel(U, S, k), cover)
  ensures var r := SetCoverToCDPCNontrivial(SetSystemModel(U, S, k));
    CDPCCertificate(r,
      SetCoverToCDPCInterview(cover, r.questions))
  // Unproved. Induct over the constructed interview and generalize over asked
  // questions and the remaining cover. Use set_cover_cdpc_false_population_step
  // and set_cover_cdpc_false_population_sums for false branches; derive true
  // branch populations and sums separately. Apply set_cover_cdpc_omega_bounds,
  // set_cover_cdpc_false_privacy, set_cover_cdpc_true_privacy and
  // set_cover_cdpc_false_classification as appropriate. Prove privacy even on
  // branches ending immediately, and classification at every reached leaf.

// Extract a small cover by following only the null candidate's false path.
lemma set_cover_cdpc_extract_cover<T(!new)>(U:set<T>, S:set<set<T>>, k:nat, interview:InterviewModel<set<T>>)
  requires SetCoverValidInstance(SetSystemModel(U, S, k))
  requires {} !in S
  requires k < |S|
  requires var r := SetCoverToCDPCNontrivial(SetSystemModel(U, S, k));
    CDPCCertificate(r, interview)
  ensures exists cover:set<set<T>> :: SetCoverCertificate(SetSystemModel(U, S, k), cover)
  // Unproved. Induct along the false branch using InterviewFits to avoid
  // repeated questions. Use set_cover_cdpc_false_population_step and
  // set_cover_cdpc_false_population_sums to track the null candidate's path.
  // Exclude the private question via PrivateSafe and its positive lower bound;
  // use set_cover_cdpc_omega_bounds and set_cover_cdpc_false_privacy_limit to
  // bound the number of set questions. At End, combine
  // set_cover_cdpc_false_classification with sum uniqueness to show that no
  // element remains uncovered. Do not infer a bound on the whole tree.

ghost function SetCoverToCDPC<T(!new)>(instance:SetCoverModel<T>)
    : (r:CDPCModel<set<T>>)
  requires SetCoverValidInstance(instance)
  ensures CDPCValidInstance(r)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var nonemptySets := S - {{}};
  set_cover_without_empty(U, S, k);
  if |nonemptySets| <= k then
    SetCoverToCDPCPositiveInstance<T>()
  else
    SetCoverToCDPCNontrivial(SetSystemModel(U, nonemptySets, k))
}

ghost function SetCoverToCDPCPositiveInstance<T(!new)>()
    : (r:CDPCModel<set<T>>)
  ensures CDPCValidInstance(r)
  ensures CDPC(r)
{
  var candidate:Candidate<set<T>> := map[{} := false];
  var fitness := map[candidate := true];
  var multiplicity:map<Candidate<set<T>>, nat> := map[candidate := 1];
  set_cover_to_cdpc_positive_instance_correct<T>();
  CDPCModel({{}}, fitness, multiplicity, {}, CDPCThresholds(0.0, 1.0, 0.0, 1.0))
}

ghost function {:isolate_assertions} SetCoverToCDPCNontrivial<T(!new)>(instance:SetCoverModel<T>)
    : (r:CDPCModel<set<T>>)
  requires SetCoverValidInstance(instance)
  requires {} !in instance.sets
  requires instance.k < |instance.sets|
  ensures CDPCValidInstance(r)
  ensures r.questions == instance.sets + {{}}
  ensures r.privateQuestions == {{}}
{
  var U, S, k := instance.universe, instance.sets, instance.k;
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
  var result := CDPCModel(S + {{}}, fitness, multiplicity, {{}}, CDPCThresholds(a, 1.0, 0.0, y));
  cdpc_valid_instance_definition(result);
  result
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

// Threshold definitions; their privacy and classification bounds are proved below.
ghost function {:opaque} SetCoverToCDPCPrivateLower(n:nat, s:nat, k:nat, omega:nat) : (a:real)
  requires 0 < n && k < s && 0 < omega
  ensures 0.0 < a <= 1.0
{
  ((s - k) as real) / ((n * omega + omega * omega + s - k) as real)
}

// Set candidates are distinct even when source sets overlap. The private answer
// separates them from every element candidate and from the null candidate.
lemma set_cover_cdpc_set_candidate_distinct<T(!new)>(S:set<set<T>>, first:set<T>, second:set<T>)
  requires {} !in S && first in S && second in S
  ensures (SetCoverToCDPCSetCandidate(S,first) == SetCoverToCDPCSetCandidate(S,second)) == (first == second)
{
  assert SetCoverToCDPCSetCandidate(S,first)[first];
  assert SetCoverToCDPCSetCandidate(S,second)[first] == (first == second);
}

ghost function SetCoverToCDPCSetTypes<T(!new)>(S:set<set<T>>, selected:set<set<T>>):set<Candidate<set<T>>>
  requires {} !in S && selected <= S
{ set question | question in selected :: SetCoverToCDPCSetCandidate(S,question) }

lemma set_cover_cdpc_remaining_set_sum<T(!new)>(U:set<T>, S:set<set<T>>, selected:set<set<T>>,
    omega:nat, multiplicity:map<Candidate<set<T>>,nat>)
  requires {} !in S && selected <= S && omega > 0
  requires SetCoverToCDPCSetTypes(S,selected) <= multiplicity.Keys
  requires forall candidate | candidate in SetCoverToCDPCSetTypes(S,selected) ::
    multiplicity[candidate] == SetCoverToCDPCCandidateMultiplicity(U,S,omega,candidate)
  ensures |SetCoverToCDPCSetTypes(S,selected)| == |selected|
  ensures MultiplicitySum(SetCoverToCDPCSetTypes(S,selected),multiplicity,|selected|)
{
  var encode := (question:set<T>) => if question in S then SetCoverToCDPCSetCandidate(S,question) else SetCoverToCDPCNullCandidate(S);
  forall first, second | first in selected && second in selected
    ensures encode(first) == encode(second) ==> first == second
  { set_cover_cdpc_set_candidate_distinct(S,first,second); }
  injective_image_cardinality_set(selected,encode);
  assert Image_set(selected,encode) == SetCoverToCDPCSetTypes(S,selected);
  assert (set question | question in selected :: encode(question)) == SetCoverToCDPCSetTypes(S,selected);
  forall candidate | candidate in SetCoverToCDPCSetTypes(S,selected)
    ensures multiplicity[candidate] == 1
  {
    var question :| question in selected && SetCoverToCDPCSetCandidate(S,question) == candidate;
    assert candidate[{}];
    assert !SetCoverToCDPCNullCandidate(S)[{}];
    assert forall element | element in U :: !SetCoverToCDPCElementCandidate(S,element)[{}];
    assert (set element | element in U && SetCoverToCDPCElementCandidate(S,element) == candidate) == {};
    reveal SetCoverToCDPCCandidateMultiplicity();
  }
  multiplicity_sum_constant(SetCoverToCDPCSetTypes(S,selected),multiplicity,1);
}

ghost function {:opaque} SetCoverToCDPCFitnessUpper(s:nat, omega:nat) : (y:real)
  requires 0 < s && 0 < omega
  ensures 0.0 < y < 1.0
{
  ((omega * omega) as real) / ((omega * omega + s) as real)
}

// Primer paso comun a las dos implicaciones de la reduccion.
lemma set_cover_without_empty<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(SetSystemModel(U, S, k))
  ensures IsCover(U, S - {{}})
  ensures SetCover(SetSystemModel(U, S, k)) == SetCover(SetSystemModel(U, S - {{}}, k))
{
  forall u | u in U
    ensures exists s | s in S - {{}} :: u in s
  {
    var s :| s in S && u in s;
    assert s != {};
  }
  if SetCover(SetSystemModel(U, S, k)) {
    var cover :| SetCoverCertificate(SetSystemModel(U, S, k), cover);
    assert SetCoverCertificate(SetSystemModel(U, S, k), cover);
    forall u | u in U
      ensures exists s | s in cover - {{}} :: u in s
    {
      var s :| s in cover && u in s;
      assert s != {};
    }
    assert IsCover(U, cover - {{}});
    assert |cover - {{}}| <= |cover|;
    assert SetCoverCertificate(SetSystemModel(U, S - {{}}, k), cover - {{}});
  }
  if SetCover(SetSystemModel(U, S - {{}}, k)) {
    var cover :| SetCoverCertificate(SetSystemModel(U, S - {{}}, k), cover);
    assert SetCoverCertificate(SetSystemModel(U, S - {{}}, k), cover);
    assert cover <= S;
    assert SetCoverCertificate(SetSystemModel(U, S, k), cover);
  }
}

lemma set_cover_to_cdpc_positive_instance_correct<T(!new)>()
  ensures
    var candidate:Candidate<set<T>> := map[{} := false];
    ghost var fitness := map[candidate := true];
    var multiplicity:map<Candidate<set<T>>, nat> := map[candidate := 1];
    var instance := CDPCModel({{}}, fitness, multiplicity, {}, CDPCThresholds(0.0, 1.0, 0.0, 1.0));
    CDPCValidInstance(instance) && CDPC(instance)
{
  var candidate:Candidate<set<T>> := map[{} := false];
  var fitness := map[candidate := true];
  var multiplicity:map<Candidate<set<T>>, nat> := map[candidate := 1];

  assert fitness.Keys == {candidate};
  assert multiplicity[candidate] == 1;
  multiplicity_sum_singleton(candidate, multiplicity);
  fit_sum_definition({candidate}, fitness, multiplicity, 1, {candidate});
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
  var thresholds := CDPCThresholds(0.0, 1.0, 0.0, 1.0);
  assert CDPCInterviewSemantics(fitness, multiplicity, {}, thresholds, fitness.Keys, End);
  assert CDPCCertificate(CDPCModel(questions, fitness, multiplicity, {}, thresholds), End);
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





// The trivial branch also covers an empty universe and a set of empty sets.
lemma set_cover_to_cdpc_trivial_correct<T(!new)>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(SetSystemModel(U, S, k))
  requires |S-{{}}| <= k
  ensures SetCover(SetSystemModel(U, S, k))
  ensures var r := SetCoverToCDPC(SetSystemModel(U, S, k));
    CDPC(r)
{
  set_cover_without_empty(U, S, k);
  assert SetCoverCertificate(SetSystemModel(U, S, k), S-{{}});
}

// Scalar facts used by both directions; they do not assume an interview or
// a candidate enumeration. omega=2*n*s satisfies these strict margins.
lemma set_cover_cdpc_omega_bounds(n:nat, s:nat)
  requires 0 < n && 0 < s
  ensures n*s < 2*n*s && s < 2*n*s
{
  nonnegative_product_monotonic(1, s, n, s);
  multiplication_associative(2, n, s);
}

// After j false answers, r original elements and s-j set types remain.
lemma set_cover_cdpc_false_privacy(n:nat, s:nat, k:nat, omega:nat, j:nat, r:nat)
  requires 0 < n && k < s && 0 < omega
  requires j <= k && r <= n
  ensures var total := r*omega+omega*omega+(s-j);
    SetCoverToCDPCPrivateLower(n,s,k,omega)*(total as real) <= ((s-j) as real) <= (total as real)
{
  var a := s-k;
  var remaining := s-j;
  var denominator := n*omega+omega*omega+a;
  var total := r*omega+omega*omega+remaining;
  nonnegative_product_monotonic(r, omega, n, omega);
  nonnegative_product_monotonic(a, r*omega+omega*omega, remaining, n*omega+omega*omega);
  assert a*total <= denominator*remaining;
  nat_rational_comparison(remaining, total, a, denominator);
  reveal SetCoverToCDPCPrivateLower();
}

// A true answer leaves one set type and r element generators, all unfit.
lemma set_cover_cdpc_true_privacy(n:nat, s:nat, k:nat, omega:nat, r:nat)
  requires 0 < n && k < s && 0 < omega
  requires r <= n && n*s <= omega
  ensures var total := r*omega+1;
    SetCoverToCDPCPrivateLower(n,s,k,omega)*(total as real) <= 1.0 <= (total as real)
{
  var a := s-k;
  var denominator := n*omega+omega*omega+a;
  var total := r*omega+1;
  nonnegative_product_monotonic(a, r, s, n);
  nonnegative_product_monotonic(a*r, omega, omega, omega);
  multiplication_associative(a, r, omega);
  multiplication_distributive(a, r*omega, 1);
  assert a*total <= denominator;
  nat_rational_comparison(1, total, a, denominator);
  reveal SetCoverToCDPCPrivateLower();
}

// More than k distinct false answers violate privacy, even when r is zero.
lemma set_cover_cdpc_false_privacy_limit(n:nat, s:nat, k:nat, omega:nat, j:nat, r:nat)
  requires 0 < n && k < j <= s && 0 < omega
  requires n*s < omega
  ensures var total := r*omega+omega*omega+(s-j);
    ((s-j) as real) < SetCoverToCDPCPrivateLower(n,s,k,omega)*(total as real)
{
  var a := s-k;
  var remaining := s-j;
  var denominator := n*omega+omega*omega+a;
  var total := r*omega+omega*omega+remaining;
  nonnegative_product_monotonic(n, remaining, n, s);
  assert n*remaining < omega;
  positive_nat_product_strict(omega, n*remaining, omega);
  assert (n*remaining)*omega < omega*omega;
  multiplication_associative(n, omega, remaining);
  multiplication_associative(n, remaining, omega);
  set_cover_cdpc_privacy_gap(omega*omega, n*omega, a, remaining);
  nat_multiplication_monotonic(a, omega*omega+remaining, total);
  assert denominator*remaining < a*total;
  nat_rational_comparison(remaining, total, a, denominator);
  reveal SetCoverToCDPCPrivateLower();
}

// On the null candidate's path classification is possible exactly when every
// original element has been eliminated. Only this path needs a k-question bound.
lemma set_cover_cdpc_false_classification(s:nat, omega:nat, j:nat, r:nat)
  requires 0 < s && s < omega && j <= s
  ensures var total := r*omega+omega*omega+(s-j);
    (SetCoverToCDPCFitnessUpper(s,omega)*(total as real) <= ((omega*omega) as real)) == (r == 0)
  ensures 0 < omega*omega
{
  var square := omega*omega;
  var total := r*omega+square+(s-j);
  if r > 0 {
    nonnegative_product_monotonic(1, omega, r, omega);
    assert square+s < total;
    assert square*(square+s) < square*total;
  } else {
    assert total <= square+s;
    nat_multiplication_monotonic(square, total, square+s);
  }
  nat_rational_comparison(square, total, square, square+s);
  reveal SetCoverToCDPCFitnessUpper();
}

lemma set_cover_cdpc_privacy_gap(base:nat, extra:nat, a:nat, remaining:nat)
  requires remaining < a && extra*remaining < base
  ensures (extra+base+a)*remaining < a*(base+remaining)
{
  nonnegative_product_monotonic(1, base, a-remaining, base);
  multiplication_distributive(base, a-remaining, remaining);
  multiplication_distributive(a, base, remaining);
  multiplication_distributive(remaining, extra+base, a);
  multiplication_distributive(remaining, extra, base);
}

// Original elements compatible with a sequence of false answers. Using a set
// of asked questions is sound because InterviewFits forbids repetitions.
ghost function {:opaque} SetCoverToCDPCUncovered<T(!new)>(U:set<T>, asked:set<set<T>>):(remaining:set<T>)
  ensures remaining <= U
{ set element | element in U && (forall question | question in asked :: element !in question) }

ghost function SetCoverToCDPCElementTypes<T(!new)>(U:set<T>, S:set<set<T>>):set<Candidate<set<T>>>
{ set element | element in U :: SetCoverToCDPCElementCandidate(S,element) }

ghost function SetCoverToCDPCFalsePopulation<T(!new)>(U:set<T>, S:set<set<T>>, asked:set<set<T>>):set<Candidate<set<T>>>
  requires {} !in S && asked <= S
{
  SetCoverToCDPCElementTypes(SetCoverToCDPCUncovered(U,asked),S) +
  SetCoverToCDPCSetTypes(S,S-asked) + {SetCoverToCDPCNullCandidate(S)}
}

// Separate the surviving population by its private bit and fitness label.
lemma set_cover_cdpc_false_population_partition<T(!new)>(U:set<T>, S:set<set<T>>, asked:set<set<T>>,
    fitness:map<Candidate<set<T>>,bool>)
  requires SetCoverFamilyValid(U, S) && {} !in S && asked <= S
  requires SetCoverToCDPCFalsePopulation(U,S,{}) <= fitness.Keys
  requires forall candidate | candidate in SetCoverToCDPCFalsePopulation(U,S,{}) ::
    fitness[candidate] == (candidate == SetCoverToCDPCNullCandidate(S))
  ensures SetCoverToCDPCFalsePopulation(U,S,asked) <= fitness.Keys
  ensures SetCoverToCDPCElementTypes(SetCoverToCDPCUncovered(U,asked),S) !! SetCoverToCDPCSetTypes(S,S-asked)
  ensures (SetCoverToCDPCElementTypes(SetCoverToCDPCUncovered(U,asked),S)+SetCoverToCDPCSetTypes(S,S-asked)) !! {SetCoverToCDPCNullCandidate(S)}
  ensures (set candidate | candidate in SetCoverToCDPCFalsePopulation(U,S,asked) && candidate in fitness && fitness[candidate]) == {SetCoverToCDPCNullCandidate(S)}
  ensures (set candidate | candidate in SetCoverToCDPCFalsePopulation(U,S,asked) && {} in candidate && candidate[{}]) == SetCoverToCDPCSetTypes(S,S-asked)
{
  var elements := SetCoverToCDPCElementTypes(SetCoverToCDPCUncovered(U,asked),S);
  var sets := SetCoverToCDPCSetTypes(S,S-asked);
  var nullCandidate := SetCoverToCDPCNullCandidate(S);
  var population := SetCoverToCDPCFalsePopulation(U,S,asked);
  assert SetCoverToCDPCUncovered(U,{}) == U by { reveal SetCoverToCDPCUncovered(); }
  assert population <= SetCoverToCDPCFalsePopulation(U,S,{});
  forall candidate | candidate in elements
    ensures !candidate[{}] && candidate != nullCandidate
  {
    var element :| element in SetCoverToCDPCUncovered(U,asked) && SetCoverToCDPCElementCandidate(S,element) == candidate;
    var question :| question in S && element in question;
    assert candidate[question] && !nullCandidate[question];
  }
  forall candidate | candidate in sets
    ensures candidate[{}]
  {
    var question :| question in S-asked && SetCoverToCDPCSetCandidate(S,question) == candidate;
  }
}
// A surviving answer type retains its entire original fiber: identical maps
// cannot be separated by asking more source questions. This is what makes the
// aggregated multiplicity omega*|fiber| agree with the number of original elements.
lemma set_cover_cdpc_remaining_element_sum<T(!new)>(U:set<T>, S:set<set<T>>, asked:set<set<T>>,
    omega:nat, multiplicity:map<Candidate<set<T>>, nat>)
  requires SetCoverFamilyValid(U, S) && asked <= S && 0 < omega
  requires (set element | element in U :: SetCoverToCDPCElementCandidate(S, element)) <= multiplicity.Keys
  requires forall candidate | candidate in (set element | element in U :: SetCoverToCDPCElementCandidate(S, element)) ::
    multiplicity[candidate] == SetCoverToCDPCCandidateMultiplicity(U,S,omega,candidate)
  ensures MultiplicitySum(SetCoverToCDPCElementTypes(SetCoverToCDPCUncovered(U,asked),S),
    multiplicity, omega*|SetCoverToCDPCUncovered(U,asked)|)
{
  reveal SetCoverToCDPCUncovered();
  var remaining := SetCoverToCDPCUncovered(U,asked);
  var encode := (element:T) => SetCoverToCDPCElementCandidate(S,element);
  var image := set element | element in remaining :: encode(element);
  forall candidate | candidate in image
    ensures multiplicity[candidate] == omega*|set element | element in remaining && encode(element) == candidate|
  {
    var element :| element in remaining && encode(element) == candidate;
    var question :| question in S && element in question;
    assert candidate[question] && !SetCoverToCDPCNullCandidate(S)[question];
    assert candidate != SetCoverToCDPCNullCandidate(S);
    var fiber := set other | other in U && encode(other) == candidate;
    assert element in fiber;
    forall other | other in fiber
      ensures other in remaining
    {
      forall askedQuestion | askedQuestion in asked
        ensures other !in askedQuestion
      {
        assert !candidate[askedQuestion];
        assert encode(other)[askedQuestion] == (other in askedQuestion);
      }
    }
    assert fiber == (set other | other in remaining && encode(other) == candidate);
    reveal SetCoverToCDPCCandidateMultiplicity();
    assert fiber == (set other | other in U && SetCoverToCDPCElementCandidate(S,other) == candidate);
    assert candidate in (set other | other in U :: SetCoverToCDPCElementCandidate(S,other));
    assert multiplicity[candidate] == SetCoverToCDPCCandidateMultiplicity(U,S,omega,candidate);
  }
  multiplicity_sum_fibers(remaining, encode, multiplicity, omega);
  assert image == (set element | element in remaining :: SetCoverToCDPCElementCandidate(S,element));
}
