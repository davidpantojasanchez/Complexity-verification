include "../Foundations/RepresentationBounds.dfy"
include "../Problems/CDPCRepresentation.dfy"
include "../Problems/CDPCLemmas.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Problems/SetCover.dfy"
include "../Collections/Interview.dfy"
include "../Collections/Set.dfy"
include "../Collections/Map.dfy"
include "../Arithmetic/PolynomialBounds.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Foundations/CollectionLaws.dfy"
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
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetCDPCCertificateSize, CDPCCertificateSizeCoefficient, 3)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetCDPCCertificateSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetCDPCCertificateSize, CDPCCertificateSizeCoefficient, 3);
}

lemma budget_transform_set_cover_to_cdpc_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetTransformSetCoverToCDPC, SetCoverToCDPCBudgetCoefficient, 56)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetTransformSetCoverToCDPC)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetTransformSetCoverToCDPC, SetCoverToCDPCBudgetCoefficient, 56);
}

lemma set_cover_to_cdpc_output_size_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetSetCoverToCDPCOutputSize, SetCoverToCDPCOutputSizeCoefficient, 20)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetSetCoverToCDPCOutputSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetSetCoverToCDPCOutputSize, SetCoverToCDPCOutputSizeCoefficient, 20);
}


// Auxiliary lemmas

// This corollary is included for completeness and is not needed by the complexity analyses.
// It expresses the verifier budget in terms of the instance size for a short certificate.
lemma budget_verify_cdpc_short_input_bound<Q(!new)>(instance:CDPCInstance<Q>, interview:Interview<Q>, weight:Q -> nat)
  requires CDPCCertificateSize(interview.Model(), weight) <= BudgetCDPCCertificateSize(
    CDPCInstanceSize(instance.questions.Model(), instance.fitness.Model(), instance.multiplicity.Model(),
      instance.privateQuestions.Model(), instance.thresholds, weight))
  ensures var instanceSize := CDPCInstanceSize(instance.questions.Model(), instance.fitness.Model(), instance.multiplicity.Model(),
      instance.privateQuestions.Model(), instance.thresholds, weight);
    var input := CDPCInputSize(instance.questions.Model(), instance.fitness.Model(), instance.multiplicity.Model(),
      instance.privateQuestions.Model(), instance.thresholds, interview.Model(), weight);
    BudgetVerifyCDPC(input) <= VerifyCDPCBudgetCoefficient*NatPower(5, 21)*NatPower(instanceSize+1, 63)
{
  var questions, fitness, multiplicity, privateQuestions, thresholds :=
    instance.questions, instance.fitness, instance.multiplicity, instance.privateQuestions, instance.thresholds;
  var instanceSize := CDPCInstanceSize(questions.Model(), fitness.Model(), multiplicity.Model(),
    privateQuestions.Model(), thresholds, weight);
  var input := CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(),
    privateQuestions.Model(), thresholds, interview.Model(), weight);
  weighted_monomial_bound(instanceSize, instanceSize, 1, 3, 1);
  polynomial_size_substitution(instanceSize, input, BudgetVerifyCDPC(input), 4, 3, VerifyCDPCBudgetCoefficient, 21);
}

lemma budget_verify_cdpc_input_bound<Q(!new)>(instance:CDPCInstance<Q>, interview:Interview<Q>, weight:Q -> nat)
  ensures var size := CDPCInputSizeBound(instance, interview, weight);
    NatBits(MultiplicityMaximum(instance.multiplicity.Model())) <= size &&
    BudgetVerifyCDPCPhase(size) <= BudgetVerifyCDPC(CDPCInputSize(instance.questions.Model(), instance.fitness.Model(),
      instance.multiplicity.Model(), instance.privateQuestions.Model(), instance.thresholds, interview.Model(), weight))
{
  var questions, fitness, multiplicity, privateQuestions, thresholds :=
    instance.questions, instance.fitness, instance.multiplicity, instance.privateQuestions, instance.thresholds;
  var input := CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(),
    privateQuestions.Model(), thresholds, interview.Model(), weight);
  var size := CDPCInputSizeBound(instance, interview, weight);
  var model := multiplicity.Model();
  assert NatBits(MultiplicityMaximum(model)) <= multiplicity.SizeBound(weight, BoolBits, NatBits) by {
    if model == map[] {
      assert NatBits(0) == 1 by { reveal NatBits(); }
    } else {
      max_by_properties(model.Values, (value:nat) => value);
      var maximum :| maximum in model.Values && maximum == MultiplicityMaximum(model);
      var candidate :| candidate in model && model[candidate] == maximum;
      representation_member_map_map_t(model, weight, BoolBits, NatBits, candidate);
    }
  }
  cdpc_input_size_bound_polynomial(instance, interview, weight);
  cdpc_budget_polynomial(size);
  polynomial_size_substitution(input, size, BudgetVerifyCDPCPhase(size), 32, 3, 12000, 7);
}

lemma cdpc_certificate_instance_size_bound<Q(!new)>(questions:set<Q>, fitness:map<Candidate<Q>, bool>,
    multiplicity:map<Candidate<Q>, nat>, privateQuestions:set<Q>,
    thresholds:CDPCThresholds<Rational>, certificate:InterviewModel<Q>, weight:Q -> nat)
  requires InterviewFits(certificate, questions)
  requires InterviewNodes(certificate) <= CDPCCertificateNodeCountBound(|fitness|+|questions|+1)
  ensures CDPCCertificateSize(certificate, weight) <=
    BudgetCDPCCertificateSize(CDPCInstanceSize(questions, fitness, multiplicity, privateQuestions, thresholds, weight))
{
  var n := CDPCInstanceSize(questions, fitness, multiplicity, privateQuestions, thresholds, weight);
  var structural := |fitness|+|questions|+1;
  var nodes := InterviewNodes(certificate);
  var bits := MaxBy(questions, weight);
  size_properties_set(questions, weight);
  size_properties_map(fitness, (candidate:Candidate<Q>) => Size_map(candidate, weight, BoolBits), BoolBits);
  cdpc_short_node_count_bound(n, structural, nodes);
  // Fitting interviews use only labels already present in the instance.
  interview_questions_bound(certificate, questions);
  max_by_properties(questions, weight);
  interview_size_bound(certificate, weight, bits);
  polynomial_product_bound(n, nodes, 1+bits, 3, 1, 2, 1);
}

lemma budget_transform_set_cover_to_cdpc_input_bound<T(!new)>(instance:SetSystemInstance<T>, weight:T -> nat)
  requires instance.universe.Init() && instance.sets.Init()
  ensures BudgetTransformSetCoverToCDPCPhase(instance.universe.Cardinality()+instance.sets.Cardinality()+1,
    CDPCConstructionLeafBound(instance.universe, instance.sets, instance.k, weight)) <=
      BudgetTransformSetCoverToCDPC(SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  var n := U.Cardinality()+S.Cardinality()+1;
  var bits := CDPCConstructionLeafBound(U, S, k, weight);
  cdpc_construction_scale_polynomial(instance, weight);
  cdpc_construction_budget_polynomial(n, bits);
  polynomial_size_substitution(input, n+bits, BudgetTransformSetCoverToCDPCPhase(n, bits), 12, 4, 2000000, 14);
}

lemma {:isolate_assertions} cdpc_construction_output_input_bound<T(!new)>(
    instance:SetSystemInstance<T>, r:CDPCSetInstance<T>, weight:T -> nat)
  requires instance.universe.Init() && instance.sets.Init()
  requires SetCoverValidInstance(instance.Model())
  requires CDPCConstructionOutputBounds(r, instance.universe.Cardinality()+instance.sets.Cardinality()+1, instance.sets.Model()+{{}})
  ensures CDPCInstanceSize(r.questions.Model(), r.fitness.Model(), r.multiplicity.Model(),
    r.privateQuestions.Model(), r.thresholds, member => Size_set(member, weight)) <=
    BudgetSetCoverToCDPCOutputSize(SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
{
  var U:Set<T>, S:SetSet<T>, k := instance.universe, instance.sets, instance.k;
  var n := U.Cardinality()+S.Cardinality()+1;
  var bits := CDPCConstructionLeafBound(U, S, k, weight);
  var source := S.Model()+{{}};
  forall question | question in source
    ensures |question| <= n
    ensures forall value | value in question :: weight(value) <= bits
  {
    if question in S.Model() {
      subset_cardinality_bound_set(question, U.Model());
      representation_member_setset(S.Model(), weight, question);
      forall value | value in question
        ensures weight(value) <= bits
      { representation_member_set(question, weight, value); }
    }
  }
  assert CDPCConstructionOutputBounds(r, n, source);
  assert NatBits(CDPCConstructionValueBound(n)) <= bits;
  assert forall question | question in source :: |question| <= n;
  assert forall question | question in source :: forall value | value in question :: weight(value) <= bits;
  cdpc_construction_output_size_bound(r, n, bits, source, weight);
  cdpc_construction_scale_polynomial(instance, weight);
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  var output := CDPCInstanceSize(r.questions.Model(), r.fitness.Model(), r.multiplicity.Model(),
    r.privateQuestions.Model(), r.thresholds, member => Size_set(member, weight));
  polynomial_size_substitution(input, n+bits, output, 12, 4, 64, 5);
}


// Bound the internal scale in the exact size of the entire supplied input.
lemma cdpc_input_size_bound_polynomial<Q(!new)>(instance:CDPCInstance<Q>, interview:Interview<Q>, weight:Q -> nat)
  ensures var input := CDPCInputSize(instance.questions.Model(), instance.fitness.Model(), instance.multiplicity.Model(),
      instance.privateQuestions.Model(), instance.thresholds, interview.Model(), weight);
    input <= CDPCInputSizeBound(instance, interview, weight) <=
      32*NatPower(input+1, 3)
{
  var questions, fitness, multiplicity, privateQuestions, thresholds :=
    instance.questions, instance.fitness, instance.multiplicity, instance.privateQuestions, instance.thresholds;
  var input := CDPCInputSize(questions.Model(), fitness.Model(), multiplicity.Model(),
    privateQuestions.Model(), thresholds, interview.Model(), weight);
  var fitnessSize := Size_map(fitness.Model(), (candidate:Candidate<Q>) => Size_map(candidate, weight, BoolBits), BoolBits);
  var multiplicitySize := Size_map(multiplicity.Model(), (candidate:Candidate<Q>) => Size_map(candidate, weight, BoolBits), NatBits);
  representation_bound_set(questions.Model(), weight);
  representation_bound_set(privateQuestions.Model(), weight);
  representation_bound_map_map_t(fitness.Model(), weight, BoolBits, BoolBits);
  representation_bound_map_map_t(multiplicity.Model(), weight, BoolBits, NatBits);
  interview_representation_bound(interview.Model(), weight);
  weighted_monomial_bound(Size_set(questions.Model(), weight)+1, input, 2, 3, 4);
  weighted_monomial_bound(Size_set(privateQuestions.Model(), weight)+1, input, 2, 3, 4);
  weighted_monomial_bound(fitnessSize+1, input, 3, 3, 7);
  weighted_monomial_bound(multiplicitySize+1, input, 3, 3, 7);
  weighted_monomial_bound(InterviewSize(interview.Model(), weight)+1, input, 2, 3, 2);
  weighted_monomial_bound(5+CDPCThresholdsBits(thresholds), input, 1, 3, 1);
  reveal CDPCInputSizeBound();
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

// Initialization identifies the ghost universes used by the construction leaf bound
// with actual input contents. No value bound on k or integer labels is assumed.
lemma cdpc_construction_scale_polynomial<T(!new)>(instance:SetSystemInstance<T>, weight:T -> nat)
  requires instance.universe.Init() && instance.sets.Init()
  ensures var n := instance.universe.Cardinality()+instance.sets.Cardinality()+1;
    var input := SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight);
    n+CDPCConstructionLeafBound(instance.universe, instance.sets, instance.k, weight) <= 12*NatPower(input+1, 4)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  var n := U.Cardinality()+S.Cardinality()+1;
  representation_bound_set(U.Model(), weight);
  representation_bound_setset(S.Model(), weight);
  assert n <= input;
  assert U.ULeafBits(weight)+S.ULeafBits(weight)+NatBits(k) <= input;
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
lemma cdpc_construction_budget_polynomial(n:nat, bits:nat)
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

lemma cdpc_construction_primitive_polynomial(n:nat, bits:nat)
  requires NatBits(CDPCConstructionValueBound(n)) <= bits
  ensures BudgetCDPCConstructionPrimitive(n, bits) <= 20000*NatPower(n+bits+1, 12)
{
  var m := n+bits;
  reveal BudgetCDPCConstructionPrimitive(), CDPCConstructionSizeBound();
  polynomial_product_bound(m, n+1, n+1, 1, 1, 1, 1);
  polynomial_product_bound(m, n+1, 1+(n+1)*(1+n), 1, 2, 1, 2);
  assert CDPCConstructionVolumeBound(n) <= 2*NatPower(m+1, 3);
  representation_size_bound_polynomial(CDPCConstructionVolumeBound(n), bits+1, m, 2, 3);
  polynomial_degree_weaken(m, bits, 1, 1, 4);
  var size := CDPCConstructionSizeBound(n, bits);
  assert size <= 8*NatPower(m+1, 4);
  var representation := CostRepresentation(2*size+1, size, size);
  cost_representation_polynomial(2*size+1, size, size, size, 3, 1);
  polynomial_size_substitution(m, size, representation, 8, 4, 12, 3);
  assert {:fuel NatPower, 4} NatPower(9, 3) == 729;
  assert representation <= 8748*NatPower(m+1, 12);
  var valueBits := NatBits(CDPCConstructionValueBound(n));
  nonnegative_product_monotonic(valueBits, valueBits, m, m);
  polynomial_product_bound(m, m, m, 1, 1, 1, 1);
  polynomial_degree_weaken(m, 1+2*m, 3, 1, 2);
  var arithmetic := BudgetNatArithmetic(CDPCConstructionValueBound(n));
  polynomial_sum_bound(m, representation, arithmetic, 8748, 4, 12, 2, 12);
  polynomial_sum_bound(m, representation+arithmetic, 2*bits+1, 8752, 3, 12, 1, 12);
  assert BudgetCDPCConstructionPrimitive(n, bits) == representation+arithmetic+(2*bits+1);
  nat_multiplication_monotonic(NatPower(m+1, 12), 8755, 20000);
}

lemma cdpc_construction_output_size_bound<T(!new)>(r:CDPCSetInstance<T>, n:nat, bits:nat, source:set<set<T>>, weight:T -> nat)
  requires 1 <= n && NatBits(CDPCConstructionValueBound(n)) <= bits
  requires CDPCConstructionOutputBounds(r, n, source)
  requires forall question | question in source :: |question| <= n
  requires forall question | question in source :: forall value | value in question :: weight(value) <= bits
  ensures CDPCInstanceSize(r.questions.Model(), r.fitness.Model(), r.multiplicity.Model(),
    r.privateQuestions.Model(), r.thresholds, member => Size_set(member, weight)) <= 64*NatPower(n+bits+1, 5)
{
  var m := n+bits;
  cdpc_construction_bits_bound(r, n, source);
  cdpc_construction_question_family_size_bound(r.questions.Model(), weight, m);
  cdpc_construction_question_family_size_bound(r.privateQuestions.Model(), weight, m);
  polynomial_degree_weaken(m, Size_set(r.questions.Model(), member => Size_set(member, weight)), 4, 3, 5);
  polynomial_degree_weaken(m, Size_set(r.privateQuestions.Model(), member => Size_set(member, weight)), 4, 3, 5);
  polynomial_degree_weaken(m, m, 1, 1, 4);
  forall candidate | candidate in r.fitness.Model()
    ensures |candidate| <= m && BoolBits(r.fitness.Model()[candidate]) <= 9*NatPower(m+1, 4)
  { max_by_member(r.fitness.Model().Keys, candidate, item => |item|); }
  forall candidate | candidate in r.multiplicity.Model()
    ensures |candidate| <= m && NatBits(r.multiplicity.Model()[candidate]) <= 9*NatPower(m+1, 4)
  { max_by_member(r.multiplicity.Model().Keys, candidate, item => |item|); }
  cdpc_construction_population_operand_bound(r.fitness.Model(), weight, BoolBits, m);
  cdpc_construction_population_operand_bound(r.multiplicity.Model(), weight, NatBits, m);
  assert CDPCThresholdsBits(r.thresholds) <= 8*bits;
  polynomial_degree_weaken(m, 5+8*bits, 13, 1, 5);
}

lemma cdpc_construction_bits_bound<T(!new)>(r:CDPCSetInstance<T>, n:nat, sourceQuestions:set<set<T>>)
  requires CDPCConstructionOutputBounds(r, n, sourceQuestions)
  ensures CDPCConstructionBitsBounds(r, n)
{
  forall candidate | candidate in r.multiplicity.Model()
    ensures NatBits(r.multiplicity.Model()[candidate]) <= NatBits(CDPCConstructionValueBound(n))
  {
    nat_bits_monotonic(r.multiplicity.Model()[candidate], CDPCConstructionValueBound(n));
  }
  forall threshold | threshold in {r.thresholds.privateLower, r.thresholds.privateUpper, r.thresholds.fitnessLower, r.thresholds.fitnessUpper}
    ensures NatBits(threshold.numerator) <= NatBits(CDPCConstructionValueBound(n))
    ensures NatBits(threshold.denominator) <= NatBits(CDPCConstructionValueBound(n))
  {
    nat_bits_monotonic(threshold.numerator, CDPCConstructionValueBound(n));
    nat_bits_monotonic(threshold.denominator, CDPCConstructionValueBound(n));
  }
}

// Exact size of the question families, using the full size of each set-valued question.
lemma cdpc_construction_question_family_size_bound<T>(questions:set<set<T>>, weight:T -> nat, n:nat)
  requires |questions| <= n
  requires forall question | question in questions :: |question| <= n
  requires forall question | question in questions :: forall element | element in question :: weight(element) <= n
  ensures Size_set(questions, question => Size_set(question, weight)) <= 4*NatPower(n+1, 3)
{
  var questionWeight := (question:set<T>) => Size_set(question, weight);
  forall question | question in questions
    ensures questionWeight(question) <= 1+n*(1+n)
  {
    size_bound_set(question, weight, n);
    nonnegative_product_monotonic(|question|, 1+n, n, 1+n);
  }
  size_bound_set(questions, questionWeight, 1+n*(1+n));
  nonnegative_product_monotonic(|questions|, 2+n*(1+n), n, 2+n*(1+n));
  polynomial_product_bound(n, n, 1+n, 1, 1, 1, 1);
  assert 2+n*(1+n) <= 3*NatPower(n+1, 2);
  polynomial_product_bound(n, n, 2+n*(1+n), 1, 3, 1, 2);
}

lemma cdpc_construction_population_operand_bound<T, V>(population:map<map<set<T>, bool>, V>,
    weight:T -> nat, valueWeight:V -> nat, n:nat)
  requires |population| <= n
  requires forall candidate | candidate in population :: |candidate| <= n && valueWeight(population[candidate]) <= 9*NatPower(n+1, 4)
  requires forall candidate | candidate in population :: forall question | question in candidate :: |question| <= n
  requires forall candidate | candidate in population :: forall question | question in candidate :: forall value | value in question :: weight(value) <= n
  ensures Size_map(population, (candidate:map<set<T>, bool>) => Size_map(candidate, question => Size_set(question, weight), BoolBits), valueWeight) <=
    16*NatPower(n+1, 5)
{
  var questionWeight := (question:set<T>) => Size_set(question, weight);
  forall candidate | candidate in population
    ensures forall question | question in candidate :: questionWeight(question) <= 1+n*(1+n)
  {
    forall question | question in candidate
      ensures questionWeight(question) <= 1+n*(1+n)
    {
      size_bound_set(question, weight, n);
      nonnegative_product_monotonic(|question|, 1+n, n, 1+n);
    }
  }
  size_bound_map_map_t_bool_t(population, questionWeight, valueWeight, n, n, 1+n*(1+n), 9*NatPower(n+1, 4));
  size_extensional_map(population, candidate => Size_map_t_bool(candidate, questionWeight),
    candidate => Size_map(candidate, questionWeight, BoolBits), valueWeight, valueWeight);
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
lemma {:isolate_assertions} cdpc_admissibility_counter_bound(population:nat, questions:nat, n:nat, countedNodes:nat,
    base:nat, beforeCount:nat, afterCount:nat, counter:nat)
  requires population <= n && questions <= n
  requires base <= 2*BudgetPrimitiveStep(n)
  requires countedNodes <= 2*population*questions+2
  requires beforeCount <= base+CostMultiplyNat(2, population)+CostMultiplyNat(2*population, questions)+
    CostAddNat(2*population*questions, 1)
  requires afterCount <= beforeCount+countedNodes*BudgetCountInterviewNode(2*population*questions+2, n)
  requires counter <= afterCount+CostLessEqualNat(countedNodes, 2*population*questions+1)
  ensures 2*population*questions+1 <= 2*n*n+1
  ensures counter <= 2*BudgetPrimitiveStep(n)+(2*n*n+2)*(3*BudgetPrimitiveStep(n))+382*NatPower(n+1, 5)
{
  var limit := 2*population*questions+1;
  nat_bits_monotonic(countedNodes, limit+1);
  nat_multiplication_monotonic(BudgetCountInterviewNode(limit+1, n), countedNodes, limit+1);
  var primitiveBudget := BudgetPrimitiveStep(n);
  assert counter <= 2*primitiveBudget+BudgetCDPCAdmissibility(population, questions, n);
  assert BudgetCDPCAdmissibility(population, questions, n) ==
    (limit+1)*(3*primitiveBudget)+BudgetCDPCAdmissibilityArithmetic(population, questions) by {
    reveal BudgetCountInterviewNode(), BudgetCDPCAdmissibilityArithmetic();
  }
  nonnegative_product_monotonic(population, questions, n, n);
  nat_multiplication_monotonic(3*primitiveBudget, limit+1, 2*n*n+2);
  budget_cdpc_admissibility_arithmetic_polynomial(population, questions, n);
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

// Bound intermediate values, growing representations and primitive charges.
lemma cdpc_construction_bounds(n:nat, bits:nat)
  requires 1 <= n && 1 <= bits
  ensures NatBits(0) == 1 && NatBits(1) == 1
  ensures 2*n <= CDPCConstructionValueBound(n)
  ensures 2*n*n <= CDPCConstructionValueBound(n)
  ensures n*(2*n*n) <= CDPCConstructionValueBound(n)
  ensures n <= CDPCConstructionVolumeBound(n)
  ensures n*(1+n) <= CDPCConstructionVolumeBound(n)
  ensures n*(1+n*(1+n)) <= CDPCConstructionVolumeBound(n)
  ensures forall volume:nat, leaf:nat | volume <= CDPCConstructionVolumeBound(n) && 1 <= leaf <= bits ::
    RepresentationSizeBound(volume, leaf) <= CDPCConstructionSizeBound(n, bits)-bits
  ensures forall work:nat, size:nat, operand:nat |
    work <= 2*CDPCConstructionSizeBound(n, bits)+1 &&
    size <= CDPCConstructionSizeBound(n, bits) && operand <= CDPCConstructionSizeBound(n, bits) ::
    CostRepresentation(work, size, operand) <= BudgetCDPCConstructionPrimitive(n, bits)
{
  reveal CDPCConstructionSizeBound();
  assert NatBits(0) == 1 && NatBits(1) == 1 by { reveal NatBits(); }
  nonnegative_product_monotonic(n, 1+n, n+1, 1+n);
  nonnegative_product_monotonic(n, 1+n*(1+n), n+1, 1+(n+1)*(1+n));
  nonnegative_product_monotonic(2, n, 2*n, n);
  nonnegative_product_monotonic(1, 2*n*n, n, 2*n*n);
  var volumeBound := CDPCConstructionVolumeBound(n);
  forall volume:nat, leaf:nat | volume <= volumeBound && 1 <= leaf <= bits
    ensures RepresentationSizeBound(volume, leaf) <= CDPCConstructionSizeBound(n, bits)-bits
  { representation_size_bound_monotonic(volume, leaf, volumeBound, bits+1); }
  var size := CDPCConstructionSizeBound(n, bits);
  cost_representation_uniform_bound(2*size+1, size, size);
}

// Transport label provenance to a larger source set.
lemma cdpc_construction_output_source_bound<T(!new)>(r:CDPCSetInstance<T>, n:nat,
    source:set<set<T>>, larger:set<set<T>>)
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

ghost function BudgetCDPCCertificateSize(n:nat):(bound:nat)
  ensures bound <= CDPCCertificateSizeCoefficient*NatPower(n+1, 3)
{ CDPCCertificateSizeCoefficient*NatPower(n+1, 3) }

ghost function BudgetTransformSetCoverToCDPC(n:nat):(bound:nat)
  ensures bound <= SetCoverToCDPCBudgetCoefficient*NatPower(n+1, 56)
{ SetCoverToCDPCBudgetCoefficient*NatPower(n+1, 56) }

ghost function BudgetSetCoverToCDPCOutputSize(n:nat):(bound:nat)
  ensures bound <= SetCoverToCDPCOutputSizeCoefficient*NatPower(n+1, 20)
{ SetCoverToCDPCOutputSizeCoefficient*NatPower(n+1, 20) }

ghost function {:opaque} BudgetVerifyCDPCPhase(n:nat):(budget:nat)
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

// The maximum is ghost: neither computing it nor measuring lengths adds an
// executable scan. Native real thresholds have no bit-cost interpretation.
ghost function MultiplicityMaximum<Q(!new)>(multiplicity:map<Candidate<Q>, nat>):nat
{ MaxBy(multiplicity.Values, (value:nat) => value) }

// Node count includes End leaves and counts both child positions, even when equal.
// This structural bound does not bound the stored bit lengths of question labels.
ghost function CDPCCertificateNodeCountBound(n:nat):nat
{ 2*n*n + 1 }

ghost function BudgetTransformSetCoverToCDPCPhase(n:nat, bits:nat):nat
{ 14*BudgetCDPCConstructionPrimitive(n, bits)+BudgetNontrivialCase(n, bits) }

ghost function {:opaque} BudgetCDPCConstructionPrimitive(n:nat, bits:nat):(budget:nat)
  ensures CostRepresentation(2*CDPCConstructionSizeBound(n, bits)+1,
    CDPCConstructionSizeBound(n, bits), CDPCConstructionSizeBound(n, bits)) <= budget
  ensures CostNew_SetFamily() <= budget
  ensures CostNew_MapFamily() <= budget
  ensures BudgetNatArithmetic(CDPCConstructionValueBound(n)) <= budget
  ensures 2*bits+1 <= budget
{
  var size := CDPCConstructionSizeBound(n,bits);
  cost_representation_monotonic(1,1,0,2*size+1,size,size);
  CostRepresentation(2*size+1,size,size)+
    BudgetNatArithmetic(CDPCConstructionValueBound(n))+2*bits+1
}

// Bounds receiver sizes and the total external operand size of each operation.
// The extra bits cover the value inserted alongside a compound key.
ghost function {:opaque} CDPCConstructionSizeBound(n:nat, bits:nat):(size:nat)
  ensures bits+1 <= size
{ RepresentationSizeBound(CDPCConstructionVolumeBound(n), bits+1)+bits }

ghost function CDPCConstructionVolumeBound(n:nat):nat
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

ghost function {:opaque} CDPCConstructionLeafBound<T(!new)>(U:Set<T>, S:SetSet<T>, k:nat, weight:T -> nat):(bits:nat)
  ensures U.ULeafBits(weight) <= bits && S.ULeafBits(weight) <= bits
  ensures NatBits(k) <= bits
  ensures NatBits(CDPCConstructionValueBound(U.Cardinality()+S.Cardinality()+1)) <= bits
{
  U.ULeafBits(weight)+S.ULeafBits(weight)+NatBits(k)+
  NatBits(CDPCConstructionValueBound(U.Cardinality()+S.Cardinality()+1))
}

// Structure, numeric fields and the source of all compound labels are separate
// from functional correctness of the still-unfinished mathematical reduction.
ghost predicate CDPCConstructionOutputBounds<T(!new)>(r:CDPCSetInstance<T>, n:nat, sourceQuestions:set<set<T>>)
{
  r.questions.Valid() && r.fitness.Valid() && r.multiplicity.Valid() && r.privateQuestions.Valid() &&
  r.questions.Cardinality() <= n && r.questions.Cardinality1() <= n && r.questions.Model() <= sourceQuestions &&
  r.privateQuestions.Cardinality() <= 1 && r.privateQuestions.Model() <= sourceQuestions &&
  r.fitness.UCardinality() <= n && r.multiplicity.UCardinality() <= n &&
  r.fitness.UCardinalityKeys() <= n && r.multiplicity.UCardinalityKeys() <= n &&
  r.fitness.UCardinalityKeysKeys() <= n && r.multiplicity.UCardinalityKeysKeys() <= n &&
  CDPCQuestionsWithin(r.fitness.Model(), sourceQuestions) && CDPCQuestionsWithin(r.multiplicity.Model(), sourceQuestions) &&
  (forall candidate | candidate in r.multiplicity.Model() :: r.multiplicity.Model()[candidate] <= CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.thresholds.privateLower, CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.thresholds.privateUpper, CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.thresholds.fitnessLower, CDPCConstructionValueBound(n)) &&
  RationalFieldsWithin(r.thresholds.fitnessUpper, CDPCConstructionValueBound(n))
}

// Every compound question label is reused from the source set of sets (or is empty).
ghost predicate CDPCQuestionsWithin<T(!new), V(!new)>(population:map<map<set<T>, bool>, V>, questions:set<set<T>>)
{ forall candidate | candidate in population :: candidate.Keys <= questions }

ghost predicate RationalFieldsWithin(threshold:Rational, maximum:nat)
{ threshold.numerator <= maximum && threshold.denominator <= maximum }

ghost predicate CDPCConstructionBitsBounds<T(!new)>(r:CDPCSetInstance<T>, n:nat)
{
  (forall candidate | candidate in r.multiplicity.Model() ::
    NatBits(r.multiplicity.Model()[candidate]) <= NatBits(CDPCConstructionValueBound(n))) &&
  (forall threshold | threshold in {r.thresholds.privateLower, r.thresholds.privateUpper, r.thresholds.fitnessLower, r.thresholds.fitnessUpper} ::
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
