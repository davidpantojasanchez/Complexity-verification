include "../Foundations/RepresentationBounds.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Problems/SetCover.dfy"
include "../Problems/HittingSet.dfy"
include "../Arithmetic/PolynomialBounds.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"
include "../Arithmetic/CostedArithmetic.dfy"
// Complexity models and polynomial bounds for SetCover verification,
// incoming transformation, certificate size and output representation.
// These proofs depend on problem models and collection interfaces, not algorithms.


// Principal polynomial-time, certificate-size and transformation results

lemma budget_verify_set_cover_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetVerifySetCover, VerifySetCoverBudgetCoefficient, 15)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetVerifySetCover)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetVerifySetCover, VerifySetCoverBudgetCoefficient, 15);
}

lemma set_cover_certificate_size_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetSetCoverCertificateSize, SetCoverCertificateSizeCoefficient, 1)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetSetCoverCertificateSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetSetCoverCertificateSize, SetCoverCertificateSizeCoefficient, 1);
}

lemma budget_transform_hitting_set_to_set_cover_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetTransformHittingSetToSetCover, HittingSetToSetCoverBudgetCoefficient, 42)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetTransformHittingSetToSetCover)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetTransformHittingSetToSetCover, HittingSetToSetCoverBudgetCoefficient, 42);
}

lemma hitting_set_to_set_cover_output_size_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetHittingSetToSetCoverOutputSize, HittingSetToSetCoverOutputSizeCoefficient, 12)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetHittingSetToSetCoverOutputSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetHittingSetToSetCoverOutputSize, HittingSetToSetCoverOutputSizeCoefficient, 12);
}


// Auxiliary lemmas

// This corollary is included for completeness and is not needed by the complexity analyses.
// It expresses the verifier budget in terms of the instance size for a short certificate.
lemma budget_verify_set_cover_short_input_bound<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat)
  requires SetCoverCertificateSize(certificate.Model(), weight) <=
           BudgetSetCoverCertificateSize(SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
  ensures var instanceSize := SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight);
    var input := SetCoverInputSize(instance.universe.Model(), instance.sets.Model(), instance.k, certificate.Model(), weight);
    BudgetVerifySetCover(input) <= VerifySetCoverBudgetCoefficient*NatPower(3, 15)*NatPower(instanceSize+1, 15)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), weight);
  var instanceSize := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  assert input <= 2*instanceSize;
  polynomial_size_substitution(instanceSize, input, BudgetVerifySetCover(input), 2, 1, VerifySetCoverBudgetCoefficient, 15);
}

lemma budget_verify_set_cover_input_bound<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat)
  ensures BudgetVerifySetCoverPhase(SetCoverInputSizeBound(instance, certificate, weight)) <=
          BudgetVerifySetCover(SetCoverInputSize(instance.universe.Model(), instance.sets.Model(), instance.k, certificate.Model(), weight))
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), weight);
  var size := SetCoverInputSizeBound(instance, certificate, weight);
  set_cover_input_size_bound_polynomial(instance, certificate, weight);
  set_cover_budget_polynomial(size);
  polynomial_size_substitution(input, size, BudgetVerifySetCoverPhase(size), 21, 3, 364, 5);
}

// Every correct certificate is a subset of S. This exact linear result needs
// neither a universe-cardinality estimate nor a bound on the numeric value of k.
lemma set_cover_certificate_instance_size_bound<T>(universe:set<T>, sets:set<set<T>>, k:nat,
    certificate:set<set<T>>, weight:T -> nat)
  requires certificate <= sets
  ensures SetCoverCertificateSize(certificate, weight) <=
          BudgetSetCoverCertificateSize(SetSystemInstanceSize(universe, sets, k, weight))
{
  size_subset_set(certificate, sets, member => Size_set(member, weight));
}

lemma budget_transform_hitting_set_to_set_cover_input_bound<T>(instance:SetSystemInstance<T>, weight:T -> nat)
  ensures BudgetTransformHittingSetToSetCoverPhase(SetSystemInstanceSizeBound(instance, weight)) <=
    BudgetTransformHittingSetToSetCover(SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  var size := SetSystemInstanceSizeBound(instance, weight);
  set_system_instance_size_bound_polynomial(instance, weight);
  hitting_set_budget_polynomial(size);
  polynomial_size_substitution(input, size, BudgetTransformHittingSetToSetCoverPhase(size), 17, 3, 258048, 14);
}

lemma hitting_set_output_input_bound<T>(instance:SetSystemInstance<T>, r:SetCoverSetInstance<T>, weight:T -> nat)
  requires r.universe.Model() == instance.sets.Model()
  requires r.sets.SizeBound(weight) <= HittingSetConstructionSizeBound(SetSystemInstanceSizeBound(instance, weight))
  requires NatBits(r.k) <= NatBits(instance.k)
  ensures SetSystemInstanceSize(r.universe.Model(), r.sets.Model(), r.k, member => Size_set(member, weight)) <=
    BudgetHittingSetToSetCoverOutputSize(SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  var n := SetSystemInstanceSizeBound(instance, weight);
  var output := SetSystemInstanceSize(r.universe.Model(), r.sets.Model(), r.k, member => Size_set(member, weight));
  representation_bound_setset(r.universe.Model(), weight);
  representation_bound_setsetset(r.sets.Model(), weight);
  assert output <= 1+r.universe.SizeBound(weight)+r.sets.SizeBound(weight)+NatBits(r.k);
  assert r.universe.SizeBound(weight) == S.SizeBound(weight);
  hitting_set_construction_size_bound_polynomial(n);
  polynomial_degree_weaken(n, 1+2*n, 3, 1, 4);
  set_system_instance_size_bound_polynomial(instance, weight);
  polynomial_size_substitution(input, n, output, 17, 3, 10, 4);
}


lemma set_cover_input_size_bound_polynomial<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, weight:T -> nat)
  ensures var input := SetCoverInputSize(instance.universe.Model(), instance.sets.Model(), instance.k, certificate.Model(), weight);
    input <= SetCoverInputSizeBound(instance, certificate, weight) <= 21*NatPower(input+1, 3)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), weight);
  var instanceSize := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  var certificateSize := SetCoverCertificateSize(certificate.Model(), weight);
  set_system_instance_size_bound_polynomial(instance, weight);
  representation_bound_setset(certificate.Model(), weight);
  weighted_monomial_bound(instanceSize+1, input, 3, 3, 12);
  weighted_monomial_bound(certificateSize+1, input, 3, 3, 7);
  reveal SetCoverInputSizeBound();
}

lemma set_system_instance_size_bound_polynomial<T>(instance:SetSystemInstance<T>, weight:T -> nat)
  ensures var input := SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight);
    input <= SetSystemInstanceSizeBound(instance, weight) <= 12*NatPower(input+1, 3)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, weight);
  var universeSize := Size_set(U.Model(), weight);
  var familySize := Size_set(S.Model(), member => Size_set(member, weight));
  representation_bound_set(U.Model(), weight);
  representation_bound_setset(S.Model(), weight);
  weighted_monomial_bound(universeSize+1, input, 2, 3, 4);
  weighted_monomial_bound(familySize+1, input, 3, 3, 7);
  weighted_monomial_bound(1+NatBits(k), input, 1, 3, 1);
  reveal SetSystemInstanceSizeBound();
}

// Polynomial primitive work in the public size envelope; no structural-only
// bound is reused as a bit-cost theorem.
lemma set_cover_budget_polynomial(n:nat)
  ensures BudgetVerifySetCoverPhase(n) <= 364*NatPower(n+1,5)
{
  reveal BudgetVerifySetCoverCore(), BudgetCheckSetCoverCertificateAdmissible(), BudgetIsSubset(), BudgetCheckUniverseElement();
  budget_primitive_step_polynomial(n);
  var primitiveBudget := BudgetPrimitiveStep(n);
  polynomial_product_bound(n,n,5*primitiveBudget,1,70,1,3);
  polynomial_sum_bound(n,5*primitiveBudget,n*(5*primitiveBudget),70,70,3,4,4);
  polynomial_product_bound(n,n,BudgetIsSubsetStep(n),1,56,1,3);
  polynomial_sum_bound(n,primitiveBudget,n*BudgetIsSubsetStep(n),14,56,3,4,4);
  polynomial_sum_bound(n,4*primitiveBudget,n*BudgetCheckCoverSet(n),56,56,3,4,4);
  polynomial_product_bound(n,n,BudgetCheckUniverseElement(n),1,112,1,4);
  polynomial_sum_bound(n,3*primitiveBudget,BudgetIsSubset(n),42,70,3,4,4);
  polynomial_sum_bound(n,3*primitiveBudget+BudgetIsSubset(n),n*BudgetCheckUniverseElement(n),112,112,4,5,5);
  polynomial_sum_bound(n,BudgetCheckSetCoverCertificateAdmissible(n),BudgetVerifySetCoverCore(n),140,224,4,5,5);
}

lemma {:isolate_assertions} hitting_set_budget_polynomial(n:nat)
  ensures BudgetTransformHittingSetToSetCoverPhase(n) <= 258048*NatPower(n+1,14)
{
  var size := HittingSetConstructionSizeBound(n);
  var primitiveBudget := BudgetPrimitiveStep(size);
  reveal BudgetBuildIncidenceSet();
  hitting_set_primitive_polynomial(n);
  polynomial_product_bound(n,4,primitiveBudget,4,12288,0,12);
  polynomial_product_bound(n,n,6*primitiveBudget,1,6*12288,1,12);
  polynomial_product_bound(n,n,5*primitiveBudget,1,5*12288,1,12);
  polynomial_sum_bound(n,4*primitiveBudget,n*(5*primitiveBudget),4*12288,5*12288,12,13,13);
  polynomial_sum_bound(n,4*primitiveBudget+n*(5*primitiveBudget),2*primitiveBudget,9*12288,2*12288,13,12,13);
  polynomial_product_bound(n,n,BudgetBuildIncidenceSet(n),1,11*12288,1,13);
  polynomial_sum_bound(n,4*primitiveBudget,n*BudgetAddSingletonSourceSet(size),
    4*12288,6*12288,12,13,14);
  polynomial_sum_bound(n,4*primitiveBudget+n*BudgetAddSingletonSourceSet(size),
    n*BudgetBuildIncidenceSet(n),10*12288,11*12288,14,14,14);
}

lemma hitting_set_primitive_polynomial(n:nat)
  ensures BudgetPrimitiveStep(HittingSetConstructionSizeBound(n)) <= 12288*NatPower(n+1,12)
{
  var size := HittingSetConstructionSizeBound(n);
  budget_primitive_step_polynomial(size);
  hitting_set_construction_size_bound_polynomial(n);
  polynomial_size_substitution(n,size,BudgetPrimitiveStep(size),7,4,24,3);
  assert {:fuel NatPower,4} NatPower(8,3) == 512;
}

// Bound the construction's representation sizes in the source scale.
lemma hitting_set_construction_size_bound_polynomial(n:nat)
  ensures HittingSetConstructionSizeBound(n) <= 7*NatPower(n+1,4)
{
  reveal HittingSetConstructionSizeBound();
  polynomial_product_bound(n,n,1+n,1,1,1,1);
  structural_volume_bound_polynomial(n,n*(1+n),n,1,2);
  representation_size_bound_polynomial(n*(1+n*(1+n)),n+1,n,2,3);
}

// A fixed output universe may contain repeated or empty incidence sets of sets.
// Bound its dimensions and all leaves once, before the executable traversal.
lemma hitting_set_output_size_bound<T>(S:SetSet<T>, SS:SetSetSet<T>, weight:T -> nat, n:nat)
  requires S.Valid() && SS.Valid()
  requires SS.UCardinality() <= n && S.Cardinality() <= n && S.Cardinality1() <= n
  requires S.LeafBits(weight) <= n+1
  requires forall setSet | setSet in SS.Universe() :: setSet <= S.Model()
  ensures SS.USizeBound(weight) <= HittingSetConstructionSizeBound(n)
{
  forall setSet | setSet in SS.Universe()
    ensures |setSet| <= n && MaxCardinality_set(setSet) <= n
    ensures MaxLeafBits_setset(setSet,weight) <= n+1
  {
    subset_cardinality_bound_set(setSet,S.Model());
    max_by_monotonic(setSet,S.Model(),item => |item|);
    representation_subset_setset(setSet,S.Model(),weight);
  }
  SS.u_cardinality1_bound(n);
  SS.u_cardinality2_bound(n);
  SS.u_volume_bound(n,n,n);
  SS.u_leaf_bits_bound(n+1,weight);
  SS.u_size_bound(n*(1+n*(1+n)),n+1,weight);
  reveal HittingSetConstructionSizeBound();
}

lemma hitting_set_singleton_universe_bounds<T>(S:SetSet<T>, SS:SetSetSet<T>)
  requires S.Valid() && SS.Valid()
  requires SS.Universe() == (set s | s in S.Model() :: {s})
  ensures SS.UVolumeBound1() <= 1 + S.UVolumeBound1()
  ensures SS.UCardinality1() <= 1
  ensures SS.UCardinality2() <= S.UCardinality1()
  ensures SS.UVolumeBound2() <= S.UVolumeBound1()
{
  forall child | child in SS.Universe()
    ensures |child| <= 1
    ensures MaxCardinality_set(child) <= S.UVolumeBound1()
  {
    var s :| s in S.Model() && child == {s};
    reveal S.UCardinality1();
    max_by_member(S.Universe(), s, item => |item|);
    max_by_insert({}, s, item => |item|);
  }
  SS.u_cardinality1_bound(1);
  SS.u_cardinality2_bound(S.UCardinality1());
}

lemma hitting_set_incidence_universe_bounds<T>(U:Set<T>, S:SetSet<T>, SS:SetSetSet<T>)
  requires S.Valid() && SS.Valid()
  requires SS.Universe() == (set u | u in U.Model() :: (set s | s in S.Model() && u in s))
  ensures SS.UVolumeBound1() <= S.UVolumeBound()
  ensures SS.UCardinality1() <= S.UCardinality()
  ensures SS.UCardinality2() <= S.UCardinality1()
  ensures SS.UVolumeBound2() <= S.UVolumeBound1()
{
  forall child | child in SS.Universe()
    ensures |child| <= S.UCardinality()
    ensures MaxCardinality_set(child) <= S.UVolumeBound1()
  {
    assert child <= S.Model();
    subset_cardinality_bound_set(child, S.Model());
    max_by_monotonic(child, S.Model(), item => |item|);
  }
  SS.u_cardinality1_bound(S.UCardinality());
  SS.u_cardinality2_bound(S.UCardinality1());
  nonnegative_product_monotonic(SS.UCardinality1(), 1+SS.UCardinality2(), S.UCardinality(), 1+S.UCardinality1());
}

// Functions and predicates

ghost function BudgetVerifySetCover(n:nat):(bound:nat)
  ensures bound <= VerifySetCoverBudgetCoefficient*NatPower(n+1, 15)
{ VerifySetCoverBudgetCoefficient*NatPower(n+1, 15) }

ghost function BudgetSetCoverCertificateSize(n:nat):(bound:nat)
  ensures bound <= SetCoverCertificateSizeCoefficient*NatPower(n+1, 1)
{ n }

ghost function BudgetTransformHittingSetToSetCover(n:nat):(bound:nat)
  ensures bound <= HittingSetToSetCoverBudgetCoefficient*NatPower(n+1, 42)
{ HittingSetToSetCoverBudgetCoefficient*NatPower(n+1, 42) }

ghost function BudgetHittingSetToSetCoverOutputSize(n:nat):(bound:nat)
  ensures bound <= HittingSetToSetCoverOutputSizeCoefficient*NatPower(n+1, 12)
{ HittingSetToSetCoverOutputSizeCoefficient*NatPower(n+1, 12) }

ghost function BudgetVerifySetCoverPhase(n:nat):nat
{ BudgetCheckSetCoverCertificateAdmissible(n)+BudgetVerifySetCoverCore(n) }

ghost function {:opaque} BudgetCheckSetCoverCertificateAdmissible(n:nat):(budget:nat)
  ensures 5*BudgetPrimitiveStep(n) <= budget
  ensures 5*BudgetPrimitiveStep(n)+n*(5*BudgetPrimitiveStep(n)) <= budget
{ 5*BudgetPrimitiveStep(n)+n*(5*BudgetPrimitiveStep(n)) }

ghost function {:opaque} BudgetVerifySetCoverCore(n:nat):(budget:nat)
  ensures 2*BudgetPrimitiveStep(n)+BudgetIsSubset(n) <= budget
  ensures 3*BudgetPrimitiveStep(n)+BudgetIsSubset(n)+n*BudgetCheckUniverseElement(n) <= budget
{ 3*BudgetPrimitiveStep(n)+BudgetIsSubset(n)+n*BudgetCheckUniverseElement(n) }

ghost function {:opaque} BudgetIsSubset(n:nat):(budget:nat)
  ensures BudgetPrimitiveStep(n)+n*BudgetIsSubsetStep(n) <= budget
{ BudgetPrimitiveStep(n)+n*BudgetIsSubsetStep(n) }

ghost function BudgetIsSubsetStep(n:nat):nat { 4*BudgetPrimitiveStep(n) }

ghost function {:opaque} BudgetCheckUniverseElement(n:nat):(budget:nat)
  ensures 4*BudgetPrimitiveStep(n)+n*BudgetCheckCoverSet(n) <= budget
{ 4*BudgetPrimitiveStep(n)+n*BudgetCheckCoverSet(n) }

ghost function BudgetCheckCoverSet(n:nat):nat { 4*BudgetPrimitiveStep(n) }

ghost function BudgetTransformHittingSetToSetCoverPhase(n:nat):(budget:nat)
  ensures var size := HittingSetConstructionSizeBound(n);
    4*BudgetPrimitiveStep(size)+n*BudgetAddSingletonSourceSet(size) <= budget
  ensures var size := HittingSetConstructionSizeBound(n);
    4*BudgetPrimitiveStep(size)+n*BudgetBuildIncidenceSet(n) <= budget
{
  var size := HittingSetConstructionSizeBound(n);
  var setup := 4*BudgetPrimitiveStep(size);
  var singletons := n*BudgetAddSingletonSourceSet(size);
  var incidences := n*BudgetBuildIncidenceSet(n);
  assert setup+singletons <= setup+singletons+incidences;
  assert setup+incidences <= setup+singletons+incidences;
  setup+singletons+incidences
}

// Bounds receiver sizes and the total external operand size of each
// construction operation, including sets of sets of sets.
ghost function {:opaque} HittingSetConstructionSizeBound(n:nat):(size:nat)
  ensures n <= size && 1 <= size
{ RepresentationSizeBound(n*(1+n*(1+n)),n+1) }

ghost function BudgetAddSingletonSourceSet(size:nat):nat
{ 6*BudgetPrimitiveStep(size) }

ghost function {:opaque} BudgetBuildIncidenceSet(n:nat):(budget:nat)
  ensures var size := HittingSetConstructionSizeBound(n);
    4*BudgetPrimitiveStep(size)+n*BudgetAddIncidentSourceSet(size)+2*BudgetPrimitiveStep(size) <= budget
{
  var size := HittingSetConstructionSizeBound(n);
  4*BudgetPrimitiveStep(size)+n*BudgetAddIncidentSourceSet(size)+2*BudgetPrimitiveStep(size)
}

ghost function BudgetAddIncidentSourceSet(size:nat):nat
{ 5*BudgetPrimitiveStep(size) }

// Constants

// Fixed cost envelope in canonical verifier input size, including the candidate.
ghost const VerifySetCoverBudgetCoefficient:nat := 364*NatPower(22, 5)

// Fixed cost envelope in canonical source instance size.
ghost const HittingSetToSetCoverBudgetCoefficient:nat := 258048*NatPower(18, 14)

// Fixed output-size envelope in canonical source instance size.
ghost const HittingSetToSetCoverOutputSizeCoefficient:nat := 10*NatPower(18, 4)

ghost const SetCoverCertificateSizeCoefficient:nat := 1
