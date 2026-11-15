include "../Problems/CDPCRepresentation.dfy"
include "../Problems/CDPCCollections.dfy"
include "../Problems/CDPCLemmas.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Problems/SetCover.dfy"
include "../Collections/Interview.dfy"
include "../Collections/Set.dfy"
include "../Collections/Map.dfy"
include "../Foundations/PolynomialBounds.dfy"
include "../Foundations/CollectionSizes.dfy"
include "../Foundations/Collections.dfy"
include "../Foundations/LoopCosts.dfy"
include "../Arithmetic/CostedArithmetic.dfy"
// Complexity models and polynomial bounds for CDPC verification,
// incoming transformation, certificate size and output representation.
// These proofs depend on problem models and collection interfaces, not algorithms.


// Principal polynomial-time, certificate-size and transformation results

lemma budget_verify_cdpc_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetVerifyCDPC, VerifyCDPCBudgetCoefficient, 21)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetVerifyCDPC)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetVerifyCDPC, VerifyCDPCBudgetCoefficient, 21);
}

lemma cdpc_certificate_size_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BoundCDPCCertificateSize, CDPCCertificateSizeCoefficient, 3)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BoundCDPCCertificateSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BoundCDPCCertificateSize, CDPCCertificateSizeCoefficient, 3);
}

lemma budget_transform_set_cover_to_cdpc_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetTransformSetCoverToCDPC, SetCoverToCDPCBudgetCoefficient, 56)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetTransformSetCoverToCDPC)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetTransformSetCoverToCDPC, SetCoverToCDPCBudgetCoefficient, 56);
}

lemma set_cover_to_cdpc_output_size_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BoundSetCoverToCDPCOutputSize, SetCoverToCDPCOutputSizeCoefficient, 20)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BoundSetCoverToCDPCOutputSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BoundSetCoverToCDPCOutputSize, SetCoverToCDPCOutputSizeCoefficient, 20);
}


// Auxiliary lemmas

// This corollary is included for completeness and is not needed by the complexity analyses.
// It expresses the verifier budget in terms of the instance size for a short certificate.
lemma budget_verify_cdpc_short_input_bound<Q(!new)>(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>,
    thresholds:(Rational, Rational, Rational, Rational), interview:Interview<Q>, weight:Q -> nat)
  requires CDPCCertificateSize(interview.Model(), weight) <= BoundCDPCCertificateSize(
    CDPCInstanceSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, weight))
  ensures BudgetVerifyCDPC(CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, interview.Model(), weight)) <=
    VerifyCDPCBudgetCoefficient*NatPower(5, 21)*NatPower(CDPCInstanceSize(questions.Model(), fitness.Model(), multiplicity.Model(),
        privateQuestions.Model(), thresholds, weight)+1, 63)
{
  var instance := CDPCInstanceSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, weight);
  polynomial_degree_weaken(instance, instance, 1, 1, 3);
  polynomial_size_substitution(CDPCInstanceSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, weight),
    CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, interview.Model(), weight),
    BudgetVerifyCDPC(CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, interview.Model(), weight)),
    4, 3, VerifyCDPCBudgetCoefficient, 21);
}

lemma budget_verify_cdpc_input_bound<Q(!new)>(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>,
    thresholds:(Rational, Rational, Rational, Rational), interview:Interview<Q>, weight:Q -> nat)
  ensures BudgetVerifyCDPCPhase(CDPCOperandSizeBound(questions, fitness, multiplicity, privateQuestions, thresholds, interview, weight)) <=
    BudgetVerifyCDPC(CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, interview.Model(), weight))
{
  var n := CDPCOperandSizeBound(questions, fitness, multiplicity, privateQuestions, thresholds, interview, weight);
  cdpc_phase_size_bound(questions, fitness, multiplicity, privateQuestions, thresholds, interview, weight);
  cdpc_budget_polynomial(n);
  polynomial_size_substitution(CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, interview.Model(), weight),
    n, BudgetVerifyCDPCPhase(n), 32, 3, 12000, 7);
}

lemma {:isolate_assertions} cdpc_certificate_instance_size_bound<Q(!new)>(questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    thresholds:(Rational, Rational, Rational, Rational), certificate:InterviewModel<Q>, weight:Q -> nat)
  requires InterviewFits(certificate, questions)
  requires InterviewNodes(certificate) <= PolynomialCDPCCertificateVolume(|fitness|+|questions|+1)
  ensures CDPCCertificateSize(certificate, weight) <=
    BoundCDPCCertificateSize(CDPCInstanceSize(questions, fitness, multiplicity, privateQuestions, thresholds, weight))
{
  var n := CDPCInstanceSize(questions, fitness, multiplicity, privateQuestions, thresholds, weight);
  var structural := |fitness|+|questions|+1;
  size_properties_set(questions, weight);
  size_properties_map(fitness, (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), BoolBits);
  cdpc_short_node_count_bound(n, structural, InterviewNodes(certificate));
  cdpc_short_certificate_size_bound(certificate, questions, weight, InterviewNodes(certificate));
  polynomial_product_bound(n, InterviewNodes(certificate), 1+MaxBy(questions, weight), 3, 1, 2, 1);
}

lemma budget_transform_set_cover_to_cdpc_input_bound(U:Set<int>, S:SetSet<int>, k:nat)
  requires U.Init() && S.Init()
  ensures BudgetTransformSetCoverToCDPCPhase(U.Cardinality()+S.Cardinality()+1, CDPCConstructionLeafBound(U,S,k)) <=
      BudgetTransformSetCoverToCDPC(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
{
  cdpc_construction_phase_size_bound(U, S, k);
  cdpc_construction_budget_polynomial(U.Cardinality()+S.Cardinality()+1, CDPCConstructionLeafBound(U,S,k));
  polynomial_size_substitution(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits), CDPCConstructionInputPhaseSizeBound(U, S, k),
    BudgetTransformSetCoverToCDPCPhase(U.Cardinality()+S.Cardinality()+1, CDPCConstructionLeafBound(U,S,k)), 12, 4, 2000000, 14);
}

lemma {:isolate_assertions} cdpc_construction_output_input_bound(U:Set<int>, S:SetSet<int>, k:nat, r:CDPCSetIntInstance)
  requires U.Init() && S.Init()
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires CDPCConstructionOutputBounds(r, U.Cardinality()+S.Cardinality()+1, S.Model()+{{}})
  ensures CDPCInstanceSize(r.0.Model(), r.1.Model(), r.2.Model(), r.3.Model(), (r.4, r.5, r.6, r.7), Size_setint) <=
    BoundSetCoverToCDPCOutputSize(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
{
  var n := U.Cardinality()+S.Cardinality()+1;
  var bits := CDPCConstructionLeafBound(U, S, k);
  forall question | question in S.Model()+{{}}
    ensures |question| <= n
    ensures forall value | value in question :: IntBits(value) <= bits
  {
    if question in S.Model() {
      subset_cardinality_bound_set(question, U.Model());
      representation_member_setset(S.Model(), IntBits, question);
      forall value | value in question
        ensures IntBits(value) <= bits
      { representation_member_set(question, IntBits, value); }
    }
  }
  cdpc_construction_output_size_bound(r, n, bits, S.Model()+{{}});
  cdpc_construction_phase_size_bound(U, S, k);
  polynomial_size_substitution(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits), CDPCConstructionInputPhaseSizeBound(U, S, k),
    CDPCInstanceSize(r.0.Model(), r.1.Model(), r.2.Model(), r.3.Model(), (r.4, r.5, r.6, r.7), Size_setint), 12, 4, 64, 5);
}


// Bridge the current phase budget to explicit input representation, including
// rejected interviews and foreign labels. No certificate correctness is assumed.
lemma {:isolate_assertions} cdpc_phase_size_bound<Q(!new)>(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>,
    thresholds:(Rational, Rational, Rational, Rational), interview:Interview<Q>, weight:Q -> nat)
  ensures CDPCOperandSizeBound(questions, fitness, multiplicity, privateQuestions, thresholds, interview, weight) <=
    32*NatPower(CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, interview.Model(), weight)+1, 3)
{
  var input := CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(), privateQuestions.Model(), thresholds, interview.Model(), weight);
  var fv := Size_map(fitness.Model(), (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), BoolBits);
  var mv := Size_map(multiplicity.Model(), (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), NatBits);
  representation_bound_set(questions.Model(), weight);
  representation_bound_set(privateQuestions.Model(), weight);
  cdpc_population_representation_bound(fitness.Model(), weight, BoolBits);
  cdpc_population_representation_bound(multiplicity.Model(), weight, NatBits);
  interview_representation_bound(interview.Model(), weight);
  multiplicity_bits_size_bound(multiplicity.Model(), weight);
  assert fitness.Size(weight, BoolBits, BoolBits) <= 7*NatPower(fv+1, 3);
  assert multiplicity.Size(weight, BoolBits, NatBits) <= 7*NatPower(mv+1, 3);
  assert {:split_here} true;
  polynomial_base_monotonic(Size_set(questions.Model(), weight)+1, input+1, 2);
  polynomial_base_monotonic(Size_set(privateQuestions.Model(), weight)+1, input+1, 2);
  polynomial_base_monotonic(fv+1, input+1, 3);
  polynomial_base_monotonic(mv+1, input+1, 3);
  polynomial_base_monotonic(InterviewSize(interview.Model(), weight)+1, input+1, 2);
  polynomial_degree_weaken(input, questions.Size(weight), 4, 2, 3);
  polynomial_degree_weaken(input, privateQuestions.Size(weight), 4, 2, 3);
  polynomial_degree_weaken(input, interview.Size(weight), 2, 2, 3);
  polynomial_degree_weaken(input, input+1, 2, 1, 3);
  reveal CDPCOperandSizeBound();
}

// Match the problem's answer-map weight with the generic nested-map measure.
lemma {:isolate_assertions} cdpc_population_representation_bound<Q(!new), V>(population:map<Candidate<Q>, V>, weight:Q -> nat, valueWeight:V -> nat)
  ensures var size := Size_map(population, (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), valueWeight);
    |population| <= size && MaxCardinality_map(population.Keys) <= size &&
    StructuralSize(StructuralVolume_map_map_t(population), MaxLeafBits_map_map_t(population, weight, BoolBits, valueWeight)) <=
      7*NatPower(size+1, 3)
{
  representation_bound_map_map_t(population, weight, BoolBits, valueWeight);
  size_extensional_map(population,
    candidate => Size_map_t_bool(candidate, weight),
    candidate => Size_map(candidate, weight, BoolBits), valueWeight, valueWeight);
}

lemma multiplicity_bits_size_bound<Q(!new)>(population:map<Candidate<Q>, nat>, weight:Q -> nat)
  ensures NatBits(MultiplicityMaximum(population)) <=
    1+Size_map(population, (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), NatBits)
{
  if population == map[] {
    assert MultiplicityMaximum(population) == 0;
    assert NatBits(0) == 1 by { reveal NatBits(); }
  } else {
    max_by_properties(population.Values, (value:nat) => value);
    var maximum :| maximum in population.Values && maximum == MultiplicityMaximum(population);
    var candidate :| candidate in population && population[candidate] == maximum;
    size_member_map(population, (candidate:Candidate<Q>) => Size_map_t_bool(candidate, weight), NatBits, candidate);
  }
}

lemma {:isolate_assertions} cdpc_budget_polynomial(n:nat)
  ensures BudgetVerifyCDPCPhase(n) <= 12000*NatPower(n+1, 7)
{
  reveal BudgetVerifyCDPCPhase();
  cdpc_helper_budget_polynomial(n);
  polynomial_product_bound(n, n, n, 1, 1, 1, 1);
  multiplication_associative(2, n, n);
  nat_multiplication_monotonic(2, n*n, NatPower(n+1, 2));
  monomial_bound(0, n, 0, 2);
  assert 2*n*n+1 <= 3*NatPower(n+1, 2);
  assert 2*n*n+2 <= 4*NatPower(n+1, 2);
  polynomial_product_bound(n, 2*n*n+2, 3*BudgetPrimitiveStep(n), 4, 66, 2, 3);
  polynomial_product_bound(n, 2*n*n+1, 6*BudgetPrimitiveStep(n), 3, 132, 2, 3);
  polynomial_product_bound(n, 2*(2*n*n+1), BudgetCDPCNode(n), 6, 1682, 2, 5);
  var scan := (2*n*n+2)*(3*BudgetPrimitiveStep(n));
  var fits := (2*n*n+1)*(6*BudgetPrimitiveStep(n));
  var tree := (2*(2*n*n+1))*BudgetCDPCNode(n);
  polynomial_sum_bound(n,2*BudgetPrimitiveStep(n),scan,44,264,3,5,5);
  polynomial_sum_bound(n,2*BudgetPrimitiveStep(n)+scan,382*NatPower(n+1,5),308,382,5,5,5);
  polynomial_sum_bound(n,2*BudgetPrimitiveStep(n)+scan+382*NatPower(n+1,5),fits,690,396,5,5,5);
  polynomial_sum_bound(n,2*BudgetPrimitiveStep(n)+scan+382*NatPower(n+1,5)+fits,tree,1086,10092,5,7,7);
}

// Fixed polynomial bounds for the helper phase, independent of the input.
lemma {:isolate_assertions} cdpc_helper_budget_polynomial(n:nat)
  ensures BudgetPrimitiveStep(n) <= 22*NatPower(n+1, 3)
  ensures BudgetCDPCSum(n) <= 220*NatPower(n+1, 4)
  ensures BudgetCDPCFilter(n) <= 198*NatPower(n+1, 4)
  ensures BudgetCDPCClassification(n) <= 544*NatPower(n+1, 4)
  ensures BudgetCDPCPrivateQuestion(n) <= 324*NatPower(n+1, 4)
  ensures BudgetCDPCPrivacy(n) <= 632*NatPower(n+1, 5)
  ensures BudgetCDPCNode(n) <= 1682*NatPower(n+1, 5)
{
  reveal BudgetCDPCSum(), BudgetCDPCFilter(),
    BudgetCDPCClassification(), BudgetCDPCPrivateQuestion(), BudgetCDPCPrivacy(), BudgetCDPCNode();
  budget_primitive_step_polynomial(n);
  polynomial_product_bound(n, n, 7*BudgetPrimitiveStep(n), 1, 154, 1, 3);
  polynomial_product_bound(n, n, 6*BudgetPrimitiveStep(n), 1, 132, 1, 3);
  polynomial_sum_bound(n,3*BudgetPrimitiveStep(n),n*(7*BudgetPrimitiveStep(n)),66,154,3,4,4);
  polynomial_sum_bound(n,3*BudgetPrimitiveStep(n),n*(6*BudgetPrimitiveStep(n)),66,132,3,4,4);
  polynomial_product_bound(n, 2*n+1, n, 2, 1, 1, 1);
  multiplication_associative(2, 2*n+1, n);
  nat_multiplication_monotonic(2, (2*n+1)*n, 2*NatPower(n+1, 2));
  polynomial_degree_weaken(n, 4+4*(3*n+1), 12, 1, 2);
  polynomial_degree_weaken(n, 4 + 2*(2*n+1)*n + 4*(3*n+1), 26, 2, 3);
  assert BudgetCDPCComparisonArithmetic(n) <= 26*NatPower(n+1, 3);
  polynomial_sum_bound(n,2*BudgetCDPCSum(n),2*BudgetCDPCComparisonArithmetic(n),440,52,4,3,4);
  polynomial_sum_bound(n,BudgetCDPCSum(n),2*BudgetCDPCComparisonArithmetic(n),220,52,4,3,4);
  polynomial_sum_bound(n,BudgetCDPCPrivateQuestion(n),3*BudgetPrimitiveStep(n),324,66,4,3,4);
  polynomial_product_bound(n, n, BudgetCDPCPrivateQuestion(n)+3*BudgetPrimitiveStep(n), 1, 390, 1, 4);
  polynomial_sum_bound(n,BudgetCDPCSum(n),BudgetPrimitiveStep(n),220,22,4,3,4);
  polynomial_sum_bound(n,BudgetCDPCSum(n)+BudgetPrimitiveStep(n),n*(BudgetCDPCPrivateQuestion(n)+3*BudgetPrimitiveStep(n)),242,390,4,5,5);
  polynomial_sum_bound(n,5*BudgetPrimitiveStep(n),2*BudgetCDPCFilter(n)+BudgetCDPCClassification(n),110,940,3,4,4);
  polynomial_sum_bound(n,5*BudgetPrimitiveStep(n)+2*BudgetCDPCFilter(n)+BudgetCDPCClassification(n),BudgetCDPCPrivacy(n),1050,632,4,5,5);
}

lemma cdpc_short_node_count_bound(n:nat, structural:nat, nodes:nat)
  requires structural <= n && nodes <= 2*structural*structural+1
  ensures n+nodes <= 3*NatPower(n+1, 2)
{
  polynomial_product_bound(n, structural, structural, 1, 1, 1, 1);
  multiplication_associative(2, structural, structural);
  nat_multiplication_monotonic(2, structural*structural, NatPower(n+1, 2));
  polynomial_degree_weaken(n, n+1, 1, 1, 2);
}

// Correct interviews have instance labels. Arbitrary candidates are measured
// separately by CDPCInputSize; node bounds alone never bound a foreign label's length.
lemma cdpc_short_certificate_size_bound<Q>(tree:InterviewModel<Q>, questions:set<Q>, weight:Q -> nat, nodes:nat)
  requires InterviewFits(tree, questions) && InterviewNodes(tree) <= nodes
  ensures InterviewSize(tree, weight) <= nodes*(1+MaxBy(questions, weight))
{
  interview_questions_bound(tree, questions);
  max_by_properties(questions, weight);
  interview_size_bound(tree, weight, MaxBy(questions, weight));
  nonnegative_product_monotonic(InterviewNodes(tree), 1+MaxBy(questions, weight), nodes, 1+MaxBy(questions, weight));
}

// Initialization identifies the ghost universes used by the phase leaf bound
// with actual input contents. No value bound on k or integer labels is assumed.
lemma {:isolate_assertions} cdpc_construction_phase_size_bound(U:Set<int>, S:SetSet<int>, k:nat)
  requires U.Init() && S.Init()
  ensures CDPCConstructionInputPhaseSizeBound(U, S, k) <=
    12*NatPower(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits)+1, 4)
{
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits);
  var n := U.Cardinality()+S.Cardinality()+1;
  representation_bound_set(U.Model(), IntBits);
  representation_bound_setset(S.Model(), IntBits);
  assert n <= input;
  assert U.ULeafBits(IntBits)+S.ULeafBits(IntBits)+NatBits(k) <= input;
  cdpc_construction_value_polynomial_bound(n);
  nat_bits_linear_bound(CDPCConstructionValueBound(n));
  polynomial_base_monotonic(n+1, input+1, 4);
  polynomial_degree_weaken(input, 2*input+1, 3, 1, 4);
  reveal CDPCConstructionLeafBound();
}

lemma cdpc_construction_value_polynomial_bound(n:nat)
  ensures CDPCConstructionValueBound(n) <= 8*NatPower(n+1, 4)
{
  assert {:fuel NatPower, 5} CDPCConstructionValueBound(n) ==
    4*NatPower(n, 4)+2*NatPower(n, 3)+NatPower(n, 1)+1;
  weighted_monomial_bound(n, n, 4, 4, 4);
  weighted_monomial_bound(n, n, 3, 4, 2);
  weighted_monomial_bound(n, n, 1, 4, 1);
  weighted_monomial_bound(n, n, 0, 4, 1);
}

// Keep the construction dimensions and leaf widths independent; combine them
// only for the scalar polynomial envelope, without changing primitive prices.
lemma {:isolate_assertions} cdpc_construction_budget_polynomial(n:nat, bits:nat)
  requires NatBits(CDPCConstructionValueBound(n)) <= bits
  ensures BudgetTransformSetCoverToCDPCPhase(n,bits) <= 2000000*NatPower(n+bits+1, 14)
{
  var m := n+bits;
  var primitiveBudget := BudgetCDPCConstructionPrimitive(n, bits);
  cdpc_construction_primitive_polynomial(n, bits);
  reveal BudgetNontrivialCase(), BudgetCandidateStep();
  polynomial_product_bound(m, n, BudgetQuestionStep(n,bits), 1, 100000, 1, 12);
  polynomial_sum_bound(m, 12*primitiveBudget, n*BudgetQuestionStep(n,bits), 240000, 100000, 12, 13, 13);
  polynomial_product_bound(m, 2*n, BudgetCandidateStep(n,bits), 2, 340000, 1, 13);
  polynomial_product_bound(m, 24+5*n, primitiveBudget, 29, 20000, 1, 12);
  polynomial_sum_bound(m, (24+5*n)*primitiveBudget, 2*n*BudgetCandidateStep(n,bits), 580000, 680000, 13, 14, 14);
  polynomial_sum_bound(m, 14*primitiveBudget, BudgetNontrivialCase(n,bits), 280000, 1260000, 12, 14, 14);
}

lemma {:isolate_assertions} cdpc_construction_primitive_polynomial(n:nat, bits:nat)
  requires NatBits(CDPCConstructionValueBound(n)) <= bits
  ensures BudgetCDPCConstructionPrimitive(n, bits) <= 20000*NatPower(n+bits+1, 12)
{
  var m := n+bits;
  reveal BudgetCDPCConstructionPrimitive(), CDPCConstructionOperandSizeBound();
  polynomial_product_bound(m, n+1, n+1, 1, 1, 1, 1);
  polynomial_product_bound(m, n+1, 1+(n+1)*(1+n), 1, 2, 1, 2);
  assert CDPCConstructionDimension(n) <= 2*NatPower(m+1, 3);
  structural_size_polynomial(CDPCConstructionDimension(n), bits+1, m, 2, 3);
  polynomial_degree_weaken(m, bits, 1, 1, 4);
  var size := CDPCConstructionOperandSizeBound(n, bits);
  assert size <= 8*NatPower(m+1, 4);
  var representation := CostRepresentation(2*size+1, size, size);
  cost_representation_polynomial(2*size+1, size, size, size, 3, 1);
  polynomial_size_substitution(m, size, representation, 8, 4, 12, 3);
  assert {:fuel NatPower, 4} NatPower(9, 3) == 729;
  assert representation <= 8748*NatPower(m+1, 12);
  budget_nat_arithmetic_bits_bound(CDPCConstructionValueBound(n), m);
  polynomial_product_bound(m, m, m, 1, 1, 1, 1);
  polynomial_degree_weaken(m, 1+2*m, 3, 1, 2);
  var arithmetic := BudgetNatArithmetic(CDPCConstructionValueBound(n));
  polynomial_sum_bound(m, representation, arithmetic, 8748, 4, 12, 2, 12);
  polynomial_sum_bound(m, representation+arithmetic, 2*bits+1, 8752, 3, 12, 1, 12);
  assert BudgetCDPCConstructionPrimitive(n, bits) == representation+arithmetic+(2*bits+1);
  nat_multiplication_monotonic(NatPower(m+1, 12), 8755, 20000);
}

lemma {:isolate_assertions} cdpc_construction_output_size_bound(r:CDPCSetIntInstance, n:nat, bits:nat, source:set<set<int>>)
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires CDPCConstructionOutputBounds(r, n, source)
  requires forall question | question in source :: |question| <= n
  requires forall question | question in source :: forall value | value in question :: IntBits(value) <= bits
  ensures CDPCInstanceSize(r.0.Model(), r.1.Model(), r.2.Model(), r.3.Model(), (r.4, r.5, r.6, r.7), Size_setint) <= 64*NatPower(n+bits+1, 5)
{
  var m := n+bits;
  cdpc_construction_bits_bound(r, n, source);
  size_polynomial_bound_setsetint(r.0.Model(), m);
  size_polynomial_bound_setsetint(r.3.Model(), m);
  polynomial_degree_weaken(m, Size_setsetint(r.0.Model()), 4, 3, 5);
  polynomial_degree_weaken(m, Size_setsetint(r.3.Model()), 4, 3, 5);
  polynomial_degree_weaken(m, m, 1, 1, 4);
  forall candidate | candidate in r.1.Model()
    ensures |candidate| <= m && BoolBits(r.1.Model()[candidate]) <= 9*NatPower(m+1, 4)
  { max_by_member(r.1.Model().Keys, candidate, item => |item|); }
  forall candidate | candidate in r.2.Model()
    ensures |candidate| <= m && NatBits(r.2.Model()[candidate]) <= 9*NatPower(m+1, 4)
  { max_by_member(r.2.Model().Keys, candidate, item => |item|); }
  cdpc_construction_population_operand_bound(r.1.Model(), BoolBits, m);
  cdpc_construction_population_operand_bound(r.2.Model(), NatBits, m);
  assert RationalBits(r.4)+RationalBits(r.5)+RationalBits(r.6)+RationalBits(r.7) <= 8*bits;
  polynomial_degree_weaken(m, 5+8*bits, 13, 1, 5);
}

lemma cdpc_construction_bits_bound(r:CDPCSetIntInstance, n:nat, sourceQuestions:set<set<int>>)
  requires CDPCConstructionOutputBounds(r, n, sourceQuestions)
  ensures CDPCConstructionBitsBounds(r, n)
{
  forall candidate | candidate in r.2.Model()
    ensures NatBits(r.2.Model()[candidate]) <= NatBits(CDPCConstructionValueBound(n))
  {
    nat_bits_monotonic(r.2.Model()[candidate], CDPCConstructionValueBound(n));
  }
  forall threshold | threshold in {r.4, r.5, r.6, r.7}
    ensures NatBits(threshold.numerator) <= NatBits(CDPCConstructionValueBound(n))
    ensures NatBits(threshold.denominator) <= NatBits(CDPCConstructionValueBound(n))
  {
    nat_bits_monotonic(threshold.numerator, CDPCConstructionValueBound(n));
    nat_bits_monotonic(threshold.denominator, CDPCConstructionValueBound(n));
  }
}

lemma {:isolate_assertions} cdpc_construction_population_operand_bound<V>(population:map<map<set<int>, bool>, V>, valueWeight:V -> nat, n:nat)
  requires |population| <= n
  requires forall candidate | candidate in population :: |candidate| <= n && valueWeight(population[candidate]) <= 9*NatPower(n+1, 4)
  requires forall candidate | candidate in population :: forall question | question in candidate :: |question| <= n
  requires forall candidate | candidate in population :: forall question | question in candidate :: forall value | value in question :: IntBits(value) <= n
  ensures Size_map(population, (candidate:map<set<int>, bool>) => Size_map_t_bool(candidate, Size_setint), valueWeight) <= 16*NatPower(n+1, 5)
{
  forall candidate | candidate in population
    ensures forall question | question in candidate :: Size_setint(question) <= 1+n*(1+n)
  {
    forall question | question in candidate
      ensures Size_setint(question) <= 1+n*(1+n)
    {
      size_bound_setint(question, n, n);
    }
  }
  size_bound_map_map_t_bool_t(population, Size_setint, valueWeight, n, n, 1+n*(1+n), 9*NatPower(n+1, 4));
  polynomial_product_bound(n, n, 1+n, 1, 1, 1, 1);
  assert 3+n*(1+n) <= 4*NatPower(n+1, 2);
  polynomial_product_bound(n, n, 3+n*(1+n), 1, 4, 1, 2);
  polynomial_degree_weaken(n, n*(3+n*(1+n)), 4, 3, 4);
  assert 2+n*(3+n*(1+n))+9*NatPower(n+1, 4) <= 15*NatPower(n+1, 4);
  polynomial_product_bound(n, n, 2+n*(3+n*(1+n))+9*NatPower(n+1, 4), 1, 15, 1, 4);
}

lemma multiplicity_maximum_bound<Q(!new)>(multiplicity:map<Candidate<Q>, nat>)
  ensures forall candidate | candidate in multiplicity :: multiplicity[candidate] <= MultiplicityMaximum(multiplicity)
{
  forall candidate | candidate in multiplicity
    ensures multiplicity[candidate] <= MultiplicityMaximum(multiplicity)
  {
    max_by_member(multiplicity.Values, multiplicity[candidate], (value:nat) => value);
  }
}

// Separate scalar composition from the valid-instance quantifiers.
lemma {:isolate_assertions} cdpc_admissibility_counter_bound(population:nat, questions:nat, n:nat, volume:nat,
    base:nat, beforeCount:nat, afterCount:nat, counter:nat)
  requires population <= n && questions <= n
  requires base <= 2*BudgetPrimitiveStep(n)
  requires volume <= 2*population*questions+2
  requires beforeCount <= base+CostMultiplyNat(2, population)+CostMultiplyNat(2*population, questions)+
    CostAddNat(2*population*questions, 1)
  requires afterCount <= beforeCount+volume*BudgetCountInterviewNode(2*population*questions+2, n)
  requires counter <= afterCount+CostLessEqualNat(volume, 2*population*questions+1)
  ensures 2*population*questions+1 <= 2*n*n+1
  ensures counter <= 2*BudgetPrimitiveStep(n)+(2*n*n+2)*(3*BudgetPrimitiveStep(n))+382*NatPower(n+1, 5)
{
  var limit := 2*population*questions+1;
  nat_bits_monotonic(volume, limit+1);
  cost_less_equal_nat_monotonic(volume, limit, limit+1, limit);
  nat_multiplication_monotonic(BudgetCountInterviewNode(limit+1, n), volume, limit+1);
  cdpc_scan_counter_bound(population, questions, n, counter);
}

lemma cdpc_admissibility_expansion(population:nat, questions:nat, n:nat)
  ensures var limit := 2*population*questions+1;
    BudgetCDPCAdmissibility(population, questions, n) ==
      (limit+1)*(3*BudgetPrimitiveStep(n))+BudgetCDPCAdmissibilityArithmetic(population, questions)
{
  reveal BudgetCountInterviewNode();
  reveal BudgetCDPCAdmissibilityArithmetic();
  var limit := 2*population*questions+1;
  multiplication_distributive(limit+1, 3*BudgetPrimitiveStep(n), BudgetCountInterviewArithmetic(limit+1));
}

lemma {:isolate_assertions} cdpc_scan_counter_bound(population:nat, questions:nat, n:nat, counter:nat)
  requires population <= n && questions <= n
  requires counter <= 2*BudgetPrimitiveStep(n)+BudgetCDPCAdmissibility(population, questions, n)
  ensures 2*population*questions+1 <= 2*n*n+1
  ensures counter <= 2*BudgetPrimitiveStep(n)+(2*n*n+2)*(3*BudgetPrimitiveStep(n))+382*NatPower(n+1, 5)
{
  nonnegative_product_monotonic(population, questions, n, n);
  multiplication_associative(2, population, questions);
  multiplication_associative(2, n, n);
  budget_cdpc_admissibility_arithmetic_polynomial(population, questions, n);
  var limit := 2*population*questions+1;
  cdpc_admissibility_expansion(population, questions, n);
  nat_multiplication_monotonic(3*BudgetPrimitiveStep(n), limit+1, 2*n*n+2);
}

lemma budget_cdpc_tree_bound(nodes:nat, limit:nat, n:nat)
  requires nodes <= limit
  ensures BudgetCDPCTree(nodes, n) <= (2*limit)*BudgetCDPCNode(n)
{
  if nodes > 0 {
    nonnegative_product_monotonic(2*nodes-1, BudgetCDPCNode(n), 2*limit, BudgetCDPCNode(n));
  }
}

// Tree-cost arithmetic for recursive proofs, independent of quantified population facts.

lemma tree_budget_combine(
    nodes:nat, trueNodes:nat, falseNodes:nat, nodeBudget:nat, branchFactor:nat,
    counterBase:nat, setupCounter:nat, afterTrueCounter:nat, counter:nat)
  requires afterTrueCounter <= setupCounter + branchFactor * trueNodes * nodeBudget
  requires nodes == 1 + trueNodes + falseNodes
  requires setupCounter <= counterBase + nodeBudget
  requires counter <= afterTrueCounter + branchFactor * falseNodes * nodeBudget
  ensures counter <= counterBase + (branchFactor * (nodes - 1) + 1) * nodeBudget
  ensures branchFactor == 1 ==> counter <= counterBase + nodes*nodeBudget
  ensures branchFactor == 2 ==> counter <= counterBase + (2*nodes-1)*nodeBudget
{}

lemma branch_budget_own_fits(nodes:nat, nodeBudget:nat, counterBase:nat, counter:nat)
  requires 1 <= nodes
  requires counter <= counterBase + nodeBudget
  ensures counter <= counterBase + 2 * nodes * nodeBudget
{}

lemma branch_budget_combine(nodes:nat, nodeBudget:nat, counterBase:nat, setupCounter:nat, counter:nat)
  requires 1 <= nodes
  requires setupCounter <= counterBase + nodeBudget
  requires counter <= setupCounter + (2 * nodes - 1) * nodeBudget
  ensures counter <= counterBase + 2 * nodes * nodeBudget
{}

lemma cdpc_sum_bits_bound(count:nat, maximum:nat, n:nat)
  requires count <= n && NatBits(maximum) <= n
  ensures NatBits(count)+NatBits(maximum) <= 2*n+1
{ nat_bits_linear_bound(count); }

// Shared numeric invariant for all three sums; no collection or cost context is
// needed to prove the growth of a partial population and its representation.
lemma cdpc_sum_bits_from_count(sum:nat, count:nat, maximum:nat)
  requires sum <= count*maximum
  ensures NatBits(sum) <= NatBits(count)+NatBits(maximum)
{
  nat_bits_multiply(count, maximum);
  nat_bits_monotonic(sum, count*maximum);
}

lemma cdpc_sum_step_bound(sum:nat, previous:nat, processed:nat, count:nat, maximum:nat)
  requires processed < count
  requires previous <= LinearLoopBudget(0, maximum, processed) && sum <= previous+maximum
  ensures sum <= LinearLoopBudget(0, maximum, processed+1)
  ensures NatBits(sum) <= NatBits(count)+NatBits(maximum)
{
  linear_loop_budget_step(0, maximum, processed);
  linear_loop_budget_bound(0, maximum, processed+1, count);
  cdpc_sum_bits_from_count(sum, count, maximum);
}

lemma {:isolate_assertions} budget_cdpc_admissibility_arithmetic_polynomial(population:nat, questions:nat, n:nat)
  requires population <= n && questions <= n
  ensures BudgetCDPCAdmissibilityArithmetic(population, questions) <= 382*NatPower(n+1, 5)
{
  var limit := 2*population*questions+1;
  assert BudgetCDPCAdmissibilityArithmetic(population, questions) <= 382*NatPower(n+1, 4) by {
    reveal BudgetCDPCAdmissibilityArithmetic();
    polynomial_product_bound(n, population, questions, 1, 1, 1, 1);
    var square := NatPower(n+1, 2);
    assert 1 <= square;
    assert limit <= 2*square+1;
    nat_bits_linear_bound(population);
    nat_bits_linear_bound(2*population);
    nat_bits_linear_bound(questions);
    nat_bits_linear_bound(2*population*questions);
    nat_bits_linear_bound(limit);
    nat_bits_linear_bound(limit+1);
    assert NatBits(2) == 2 && NatBits(1) == 1 by { reveal NatBits(); }
    polynomial_product_bound(n, NatBits(2*population), NatBits(questions), 2, 1, 1, 1);
    assert CostMultiplyNat(2, population) <= 3*NatPower(n+1, 1);
    polynomial_degree_weaken(n, CostMultiplyNat(2, population), 3, 1, 2);
    assert CostMultiplyNat(2*population, questions) <= 3*square;
    assert CostAddNat(2*population*questions, 1) <= 7*square;
    assert CostMultiplyNat(2, population)+CostMultiplyNat(2*population, questions)+CostAddNat(2*population*questions, 1) <= 16*square;
    assert NatBits(limit+1) <= 5*square;
    assert BudgetCountInterviewArithmetic(limit+1) <= 89*square;
    assert limit+1 <= 4*square;
    polynomial_product_bound(n, limit+1, BudgetCountInterviewArithmetic(limit+1), 4, 89, 2, 2);
    assert NatBits(limit) <= 4*square;
    assert CostLessEqualNat(limit+1, limit) <= 10*square;
    polynomial_degree_weaken(n, CostMultiplyNat(2, population)+CostMultiplyNat(2*population, questions)+CostAddNat(2*population*questions, 1), 16, 2, 4);
    polynomial_degree_weaken(n, CostLessEqualNat(limit+1, limit), 10, 2, 4);
    assert BudgetCDPCAdmissibilityArithmetic(population, questions) <= 382*NatPower(n+1, 4);
  }
  polynomial_degree_weaken(n, BudgetCDPCAdmissibilityArithmetic(population, questions), 382, 4, 5);
}

// Bound the public comparison charge for all operands of at most bits bits.
lemma cdpc_construction_comparison_cost_bound(n:nat, bits:nat)
  ensures forall left:nat, right:nat {:trigger CostLessEqualNat(left,right)} |
    NatBits(left) <= bits && NatBits(right) <= bits ::
      CostLessEqualNat(left,right) <= BudgetCDPCConstructionPrimitive(n,bits)
{}

// Bound intermediate values, growing representations and primitive charges.
lemma cdpc_construction_bounds(n:nat, bits:nat)
  requires 1 <= n && 1 <= bits
  ensures NatBits(0) == 1 && NatBits(1) == 1
  ensures 2*n <= CDPCConstructionValueBound(n)
  ensures 2*n*n <= CDPCConstructionValueBound(n)
  ensures n*(2*n*n) <= CDPCConstructionValueBound(n)
  ensures n <= CDPCConstructionDimension(n)
  ensures n*(1+n) <= CDPCConstructionDimension(n)
  ensures n*(1+n*(1+n)) <= CDPCConstructionDimension(n)
  ensures forall volume:nat, leaf:nat | volume <= CDPCConstructionDimension(n) && 1 <= leaf <= bits ::
    StructuralSize(volume, leaf) <= CDPCConstructionOperandSizeBound(n, bits)-bits
  ensures forall work:nat, size:nat, operand:nat |
    work <= 2*CDPCConstructionOperandSizeBound(n, bits)+1 && size <= CDPCConstructionOperandSizeBound(n, bits) && operand <= CDPCConstructionOperandSizeBound(n, bits) ::
    CostRepresentation(work, size, operand) <= BudgetCDPCConstructionPrimitive(n, bits)
{
  reveal CDPCConstructionOperandSizeBound();
  assert NatBits(0) == 1 && NatBits(1) == 1 by { reveal NatBits(); }
  nonnegative_product_monotonic(n, 1+n, n+1, 1+n);
  nonnegative_product_monotonic(n, 1+n*(1+n), n+1, 1+(n+1)*(1+n));
  nonnegative_product_monotonic(2, n, 2*n, n);
  nonnegative_product_monotonic(1, 2*n*n, n, 2*n*n);
  var dimension := CDPCConstructionDimension(n);
  forall volume:nat, leaf:nat | volume <= dimension && 1 <= leaf <= bits
    ensures StructuralSize(volume, leaf) <= CDPCConstructionOperandSizeBound(n, bits)-bits
  { structural_size_monotonic(volume, leaf, dimension, bits+1); }
  var size := CDPCConstructionOperandSizeBound(n, bits);
  cost_representation_uniform_bound(2*size+1, size, size);
}

// Transport label provenance to a larger source set.
lemma cdpc_construction_output_source_bound(r:CDPCSetIntInstance, n:nat,
    source:set<set<int>>, larger:set<set<int>>)
  requires CDPCConstructionOutputBounds(r, n, source)
  requires source <= larger
  ensures CDPCConstructionOutputBounds(r, n, larger)
{}

lemma cdpc_construction_multiplicity_bound(previous:nat, omega:nat, processed:nat, n:nat)
  requires processed < n && omega <= 2*n*n
  requires previous <= processed*omega
  ensures previous+omega <= (processed+1)*omega
  ensures previous+omega <= CDPCConstructionValueBound(n)
  ensures omega <= CDPCConstructionValueBound(n)
{
  nonnegative_product_monotonic(processed+1, omega, n, 2*n*n);
}

// Functions and predicates

ghost function BudgetVerifyCDPC(n:nat):(bound:nat)
  ensures bound <= VerifyCDPCBudgetCoefficient*NatPower(n+1, 21)
{ VerifyCDPCBudgetCoefficient*NatPower(n+1, 21) }

ghost function BoundCDPCCertificateSize(n:nat):(bound:nat)
  ensures bound <= CDPCCertificateSizeCoefficient*NatPower(n+1, 3)
{ CDPCCertificateSizeCoefficient*NatPower(n+1, 3) }

ghost function BudgetTransformSetCoverToCDPC(n:nat):(bound:nat)
  ensures bound <= SetCoverToCDPCBudgetCoefficient*NatPower(n+1, 56)
{ SetCoverToCDPCBudgetCoefficient*NatPower(n+1, 56) }

ghost function BoundSetCoverToCDPCOutputSize(n:nat):(bound:nat)
  ensures bound <= SetCoverToCDPCOutputSizeCoefficient*NatPower(n+1, 20)
{ SetCoverToCDPCOutputSizeCoefficient*NatPower(n+1, 20) }

ghost function {:opaque} {:isolate_assertions} BudgetVerifyCDPCPhase(n:nat):(budget:nat)
  ensures 2*BudgetPrimitiveStep(n)+(2*n*n+2)*(3*BudgetPrimitiveStep(n))+382*NatPower(n+1, 5) <= budget
  ensures 2*BudgetPrimitiveStep(n)+(2*n*n+2)*(3*BudgetPrimitiveStep(n))+382*NatPower(n+1, 5)+
    (2*n*n+1)*(6*BudgetPrimitiveStep(n)) <= budget
  ensures 2*BudgetPrimitiveStep(n)+(2*n*n+2)*(3*BudgetPrimitiveStep(n))+382*NatPower(n+1, 5)+
    (2*n*n+1)*(6*BudgetPrimitiveStep(n))+(2*(2*n*n+1))*BudgetCDPCNode(n) <= budget
{
  var limit:nat := 2*n*n+1;
  2*BudgetPrimitiveStep(n)+(limit+1)*(3*BudgetPrimitiveStep(n))+382*NatPower(n+1, 5)+
  limit*(6*BudgetPrimitiveStep(n))+(2*limit)*BudgetCDPCNode(n)
}

ghost function {:opaque} BudgetCDPCNode(n:nat):(budget:nat)
  ensures 5*BudgetPrimitiveStep(n)+2*BudgetCDPCFilter(n)+BudgetCDPCClassification(n)+BudgetCDPCPrivacy(n) <= budget
{ 5*BudgetPrimitiveStep(n)+2*BudgetCDPCFilter(n)+BudgetCDPCClassification(n)+BudgetCDPCPrivacy(n) }

ghost function {:opaque} BudgetCDPCFilter(n:nat):(budget:nat)
  ensures 3*BudgetPrimitiveStep(n)+n*(6*BudgetPrimitiveStep(n)) <= budget
{ 3*BudgetPrimitiveStep(n)+n*(6*BudgetPrimitiveStep(n)) }

ghost function {:opaque} BudgetCDPCClassification(n:nat):(budget:nat)
  ensures 2*BudgetCDPCSum(n)+2*BudgetCDPCComparisonArithmetic(n) <= budget
{ 2*BudgetCDPCSum(n)+2*BudgetCDPCComparisonArithmetic(n) }

ghost function {:opaque} BudgetCDPCSum(n:nat):(budget:nat)
  ensures 3*BudgetPrimitiveStep(n)+n*(7*BudgetPrimitiveStep(n)) <= budget
{ 3*BudgetPrimitiveStep(n)+n*(7*BudgetPrimitiveStep(n)) }

// Rational comparison includes cross-products and comparisons at their actual
// operand lengths. n bounds both stored thresholds and population lengths.
ghost function BudgetCDPCComparisonArithmetic(n:nat):nat
{ 4 + 2*(2*n+1)*n + 4*(3*n+1) }

ghost function {:opaque} BudgetCDPCPrivacy(n:nat):(budget:nat)
  ensures BudgetCDPCSum(n)+BudgetPrimitiveStep(n)+n*(BudgetCDPCPrivateQuestion(n)+3*BudgetPrimitiveStep(n)) <= budget
{ BudgetCDPCSum(n)+BudgetPrimitiveStep(n)+n*(BudgetCDPCPrivateQuestion(n)+3*BudgetPrimitiveStep(n)) }

ghost function {:opaque} BudgetCDPCPrivateQuestion(n:nat):(budget:nat)
  ensures BudgetCDPCSum(n)+2*BudgetCDPCComparisonArithmetic(n) <= budget
{ BudgetCDPCSum(n)+2*BudgetCDPCComparisonArithmetic(n) }

// The current helper phase measures actual inputs, including foreign interview
// labels. Model sizes suffice even when a filtered map has a wider universe.
ghost function {:opaque} CDPCOperandSizeBound<Q(!new)>(questions:Set<Q>, fitness:Map_Map_T<Q, bool, bool>,
    multiplicity:Map_Map_T<Q, bool, nat>, privateQuestions:Set<Q>,
    thresholds:(Rational, Rational, Rational, Rational), interview:Interview<Q>, weight:Q -> nat):(size:nat)
  ensures questions.Size(weight) <= size
  ensures fitness.Size(weight, BoolBits, BoolBits) <= size
  ensures multiplicity.Size(weight, BoolBits, NatBits) <= size
  ensures privateQuestions.Size(weight) <= size
  ensures interview.Size(weight) <= size && fitness.CardinalityKeys() <= size
  ensures fitness.Cardinality() <= size && questions.Cardinality() <= size
  ensures NatBits(MultiplicityMaximum(multiplicity.Model())) <= size
  ensures CDPCThresholdsBits(thresholds) <= size
{
  questions.Size(weight)+fitness.Size(weight, BoolBits, BoolBits)+
  multiplicity.Size(weight, BoolBits, NatBits)+privateQuestions.Size(weight)+
  interview.Size(weight)+
  NatBits(MultiplicityMaximum(multiplicity.Model()))+CDPCThresholdsBits(thresholds)+1
}

// The maximum is ghost: neither computing it nor measuring lengths adds an
// executable scan. Native real thresholds have no bit-cost interpretation.
ghost function MultiplicityMaximum<Q(!new)>(multiplicity:map<Candidate<Q>, nat>):nat
{ MaxBy(multiplicity.Values, (value:nat) => value) }

// Node count includes End leaves and counts both child positions, even when equal.
// This structural bound does not bound the stored bit lengths of question labels.
ghost function PolynomialCDPCCertificateVolume(n:nat):nat
{ 2*n*n + 1 }

ghost function BudgetTransformSetCoverToCDPCPhase(n:nat, bits:nat):nat
{ 14*BudgetCDPCConstructionPrimitive(n, bits)+BudgetNontrivialCase(n, bits) }

ghost function {:opaque} BudgetCDPCConstructionPrimitive(n:nat, bits:nat):(budget:nat)
  ensures CostRepresentation(2*CDPCConstructionOperandSizeBound(n, bits)+1,
    CDPCConstructionOperandSizeBound(n, bits), CDPCConstructionOperandSizeBound(n, bits)) <= budget
  ensures CostNew_SetFamily() <= budget
  ensures CostNew_MapFamily() <= budget
  ensures BudgetNatArithmetic(CDPCConstructionValueBound(n)) <= budget
  ensures 2*bits+1 <= budget
{
  var size := CDPCConstructionOperandSizeBound(n,bits);
  cost_representation_monotonic(1,1,0,2*size+1,size,size);
  CostRepresentation(2*size+1,size,size)+
    BudgetNatArithmetic(CDPCConstructionValueBound(n))+2*bits+1
}

// Operand size bound for growing collections and numeric fields.
ghost function {:opaque} CDPCConstructionOperandSizeBound(n:nat, bits:nat):(size:nat)
  ensures bits+1 <= size
{ StructuralSize(CDPCConstructionDimension(n), bits+1)+bits }

ghost function CDPCConstructionDimension(n:nat):nat
{ (n+1)*(1+(n+1)*(1+n)) }

// Bounds all constructed numbers; lengths, not these values, enter arithmetic costs.
ghost function CDPCConstructionValueBound(n:nat):nat
{ n*(2*n*n) + (2*n*n)*(2*n*n) + n + 1 }

ghost function {:opaque} BudgetNontrivialCase(n:nat, bits:nat):(budget:nat)
  ensures 22*BudgetCDPCConstructionPrimitive(n, bits)+
    2*(n*BudgetCandidateStep(n, bits))+n*BudgetQuestionStep(n, bits) <= budget
{
  multiplication_associative(n, 5, BudgetCDPCConstructionPrimitive(n, bits));
  multiplication_associative(2, n, BudgetCandidateStep(n, bits));
  (24+5*n)*BudgetCDPCConstructionPrimitive(n, bits)+2*n*BudgetCandidateStep(n, bits)
}

ghost function {:opaque} BudgetCandidateStep(n:nat, bits:nat):(budget:nat)
  ensures 12*BudgetCDPCConstructionPrimitive(n, bits)+n*BudgetQuestionStep(n, bits) <= budget
{ 12*BudgetCDPCConstructionPrimitive(n, bits)+n*BudgetQuestionStep(n, bits) }

ghost function BudgetQuestionStep(n:nat, bits:nat):nat
{ 5*BudgetCDPCConstructionPrimitive(n, bits) }

ghost function {:opaque} CDPCConstructionLeafBound(U:Set<int>, S:SetSet<int>, k:nat):(bits:nat)
  ensures U.ULeafBits(IntBits) <= bits && S.ULeafBits(IntBits) <= bits
  ensures NatBits(k) <= bits
  ensures NatBits(CDPCConstructionValueBound(U.Cardinality()+S.Cardinality()+1)) <= bits
{
  U.ULeafBits(IntBits)+S.ULeafBits(IntBits)+NatBits(k)+
  NatBits(CDPCConstructionValueBound(U.Cardinality()+S.Cardinality()+1))
}

// Combines source dimensions and constructed leaf widths; its canonical-source
// bound is proved by cdpc_construction_phase_size_bound.
ghost function CDPCConstructionInputPhaseSizeBound(U:Set<int>, S:SetSet<int>, k:nat):nat
{ U.Cardinality()+S.Cardinality()+1 + CDPCConstructionLeafBound(U, S, k) }

// Structure, numeric fields and the source of all compound labels are separate
// from functional correctness of the still-unfinished mathematical reduction.
ghost predicate CDPCConstructionOutputBounds(r:CDPCSetIntInstance, n:nat, sourceQuestions:set<set<int>>)
{
  r.0.Valid() && r.1.Valid() && r.2.Valid() && r.3.Valid() &&
  r.0.Cardinality() <= n && r.0.Cardinality1() <= n && r.0.Model() <= sourceQuestions &&
  r.3.Cardinality() <= 1 && r.3.Model() <= sourceQuestions &&
  r.1.UCardinality() <= n && r.2.UCardinality() <= n &&
  r.1.UCardinalityKeys() <= n && r.2.UCardinalityKeys() <= n &&
  r.1.UCardinalityKeysKeys() <= n && r.2.UCardinalityKeysKeys() <= n &&
  CDPCQuestionsWithin(r.1.Model(), sourceQuestions) && CDPCQuestionsWithin(r.2.Model(), sourceQuestions) &&
  (forall candidate | candidate in r.2.Model() :: r.2.Model()[candidate] <= CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.4, CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.5, CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.6, CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.7, CDPCConstructionValueBound(n))
}

// Every compound question label is reused from the source set of sets (or is empty).
ghost predicate CDPCQuestionsWithin<T(!new)>(population:map<map<set<int>, bool>, T>, questions:set<set<int>>)
{ forall candidate | candidate in population :: candidate.Keys <= questions }

ghost predicate RationalFieldsWithin(threshold:Rational, maximum:nat)
{ threshold.numerator <= maximum && threshold.denominator <= maximum }

ghost predicate CDPCConstructionBitsBounds(r:CDPCSetIntInstance, n:nat)
{
  (forall candidate | candidate in r.2.Model() ::
    NatBits(r.2.Model()[candidate]) <= NatBits(CDPCConstructionValueBound(n))) &&
  (forall threshold | threshold in {r.4, r.5, r.6, r.7} ::
    NatBits(threshold.numerator) <= NatBits(CDPCConstructionValueBound(n)) &&
    NatBits(threshold.denominator) <= NatBits(CDPCConstructionValueBound(n)))
}

// Three tree accesses and a conservative budget for local scalar arithmetic.
ghost function {:opaque} BudgetCountInterviewNode(bound:nat, n:nat):(budget:nat)
  ensures BudgetCountInterviewArithmetic(bound)+3*BudgetPrimitiveStep(n) <= budget
{ 3*BudgetPrimitiveStep(n)+BudgetCountInterviewArithmetic(bound) }

ghost function BudgetCountInterviewArithmetic(bound:nat):nat
{ 1 + 8*(1+2*NatBits(bound)) }

ghost function BudgetCDPCAdmissibility(population:nat, questions:nat, n:nat):nat
{
  var limit := 2*population*questions+1;
  CostMultiplyNat(2, population)+CostMultiplyNat(2*population, questions)+
  CostAddNat(2*population*questions, 1)+
  (limit+1)*BudgetCountInterviewNode(limit+1, n)+CostLessEqualNat(limit+1, limit)
}

ghost function {:opaque} BudgetCDPCAdmissibilityArithmetic(population:nat, questions:nat):nat
{
  var limit := 2*population*questions+1;
  CostMultiplyNat(2, population) + CostMultiplyNat(2*population, questions) +
  CostAddNat(2*population*questions, 1) +
  (limit+1)*BudgetCountInterviewArithmetic(limit+1) + CostLessEqualNat(limit+1, limit)
}

// One core check per node and one branch check per nonroot node.
// The zero case keeps the scalar budget total on nat.
ghost function BudgetCDPCTree(nodes:nat, n:nat):nat
{
  if nodes == 0 then 0 else
    nat_multiplication_monotonic(2*nodes-1, 0, BudgetCDPCNode(n));
    (2*nodes-1)*BudgetCDPCNode(n)
}

ghost function BudgetPrepareSourceSets(n:nat, bits:nat):nat
{ 3*BudgetCDPCConstructionPrimitive(n, bits) }

ghost function BudgetBuildOutputQuestionSets(n:nat, bits:nat):nat
{ 3*BudgetCDPCConstructionPrimitive(n, bits) }

ghost function BudgetHandlePositiveCase(n:nat, bits:nat):nat
{ 10*BudgetCDPCConstructionPrimitive(n, bits) }

// Constants

// Fixed cost envelope in canonical verifier input size, including the candidate.
ghost const VerifyCDPCBudgetCoefficient:nat := 12000*NatPower(33, 7)

// Fixed cost envelope in canonical source instance size.
ghost const SetCoverToCDPCBudgetCoefficient:nat := 2000000*NatPower(13, 14)

// Fixed output-size envelope in canonical source instance size.
ghost const SetCoverToCDPCOutputSizeCoefficient:nat := 64*NatPower(13, 5)

// Fixed certificate-size envelope in canonical instance size.
ghost const CDPCCertificateSizeCoefficient:nat := 3
