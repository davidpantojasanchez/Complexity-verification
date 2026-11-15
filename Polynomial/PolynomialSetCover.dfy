include "../Problems/SetSystemRepresentation.dfy"
include "../Problems/SetSystemCollections.dfy"
include "../Problems/SetCoverLemmas.dfy"
include "../Problems/HittingSetLemmas.dfy"
include "../Foundations/PolynomialBounds.dfy"
include "../Foundations/CollectionSizes.dfy"
include "../Foundations/Collections.dfy"
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
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BoundSetCoverCertificateSize, SetCoverCertificateSizeCoefficient, 1)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BoundSetCoverCertificateSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BoundSetCoverCertificateSize, SetCoverCertificateSizeCoefficient, 1);
}

lemma budget_transform_hitting_set_to_set_cover_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BudgetTransformHittingSetToSetCover, HittingSetToSetCoverBudgetCoefficient, 42)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BudgetTransformHittingSetToSetCover)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BudgetTransformHittingSetToSetCover, HittingSetToSetCoverBudgetCoefficient, 42);
}

lemma hitting_set_to_set_cover_output_size_is_polynomial()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, BoundHittingSetToSetCoverOutputSize, HittingSetToSetCoverOutputSizeCoefficient, 12)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, BoundHittingSetToSetCoverOutputSize)
{
  polynomial_witness((n:nat) => true, (n:nat) => n, BoundHittingSetToSetCoverOutputSize, HittingSetToSetCoverOutputSizeCoefficient, 12);
}


// Auxiliary lemmas

// This corollary is included for completeness and is not needed by the complexity analyses.
// It expresses the verifier budget in terms of the instance size for a short certificate.
lemma budget_verify_set_cover_short_input_bound(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>)
  requires SetCoverCertificateSize(certificate.Model(), IntBits) <=
           BoundSetCoverCertificateSize(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
  ensures BudgetVerifySetCover(SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), IntBits)) <=
          VerifySetCoverBudgetCoefficient*NatPower(3, 15)*NatPower(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits)+1, 15)
{
  var input := SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), IntBits);
  var instance := SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits);
  assert input <= 2*instance;
  polynomial_size_substitution(instance, input, BudgetVerifySetCover(input), 2, 1, VerifySetCoverBudgetCoefficient, 15);
}

lemma budget_verify_set_cover_input_bound(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>)
  ensures BudgetVerifySetCoverPhase(SetCoverOperandSizeBound(U,S,k,certificate)) <=
          BudgetVerifySetCover(SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), IntBits))
{
  set_cover_phase_size_bound(U,S,k,certificate);
  set_cover_budget_polynomial(SetCoverOperandSizeBound(U,S,k,certificate));
  polynomial_size_substitution(SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), IntBits),SetCoverOperandSizeBound(U,S,k,certificate),
    BudgetVerifySetCoverPhase(SetCoverOperandSizeBound(U,S,k,certificate)),21,3,364,5);
}

// Every correct certificate is a subset of S. This exact linear result needs
// neither a universe-cardinality estimate nor a bound on the numeric value of k.
lemma set_cover_certificate_instance_size_bound<T>(universe:set<T>, sets:set<set<T>>, k:nat,
    certificate:set<set<T>>, weight:T -> nat)
  requires certificate <= sets
  ensures SetCoverCertificateSize(certificate, weight) <=
          BoundSetCoverCertificateSize(SetSystemInstanceSize(universe, sets, k, weight))
{
  size_subset_set(certificate, sets, member => Size_set(member, weight));
}

lemma budget_transform_hitting_set_to_set_cover_input_bound(U:Set<int>, S:SetSet<int>, k:nat)
  ensures BudgetTransformHittingSetToSetCoverPhase(HittingSetPhaseSizeBound(U,S,k)) <= BudgetTransformHittingSetToSetCover(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
{
  hitting_set_phase_size_bound(U,S,k);
  hitting_set_budget_polynomial(HittingSetPhaseSizeBound(U,S,k));
  polynomial_size_substitution(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits),HittingSetPhaseSizeBound(U,S,k),
    BudgetTransformHittingSetToSetCoverPhase(HittingSetPhaseSizeBound(U,S,k)),17,3,258048,14);
}

lemma {:isolate_assertions} hitting_set_output_input_bound(U:Set<int>, S:SetSet<int>, k:nat, r:SetCoverSetIntInstance)
  requires r.0.Model() == S.Model()
  requires r.1.Size(IntBits) <= HittingSetOperandSizeBound(HittingSetPhaseSizeBound(U,S,k))
  requires NatBits(r.2) <= NatBits(k)
  ensures SetSystemInstanceSize(r.0.Model(), r.1.Model(), r.2, Size_setint) <= BoundHittingSetToSetCoverOutputSize(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
  ensures HittingSetOutputOperandSizeBound(r) <= BoundHittingSetToSetCoverOutputSize(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
{
  var n := HittingSetPhaseSizeBound(U,S,k);
  representation_bound_setset(r.0.Model(), IntBits);
  size_extensional_set(r.0.Model(), Size_setint, child => Size_set(child, IntBits));
  representation_bound_setsetset(r.1.Model(), IntBits);
  forall sets | sets in r.1.Model()
    ensures Size_setsetint(sets) == Size_set(sets, child => Size_set(child, IntBits))
  {
    size_extensional_set(sets, Size_setint, child => Size_set(child, IntBits));
  }
  size_extensional_set(r.1.Model(), Size_setsetint, sets => Size_set(sets, child => Size_set(child, IntBits)));
  size_extensional_set(r.1.Model(), Size_setsetint, sets => Size_set(sets, Size_setint));
  assert SetSystemInstanceSize(r.0.Model(), r.1.Model(), r.2, Size_setint) <=
    1+r.0.Size(IntBits)+r.1.Size(IntBits)+NatBits(r.2);
  hitting_set_operand_polynomial_bound(n);
  assert r.0.Size(IntBits) == S.Size(IntBits);
  polynomial_degree_weaken(n, 1+2*n, 3, 1, 4);
  assert HittingSetOutputOperandSizeBound(r) <= 10*NatPower(n+1,4);
  hitting_set_phase_size_bound(U,S,k);
  polynomial_size_substitution(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits), n, HittingSetOutputOperandSizeBound(r), 17,3,10,4);
}


lemma set_cover_phase_size_bound(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>)
  ensures SetCoverOperandSizeBound(U,S,k,certificate) <= 21*NatPower(SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), IntBits)+1,3)
{
  var input := SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), IntBits);
  representation_bound_set(U.Model(),IntBits);
  representation_bound_setset(S.Model(),IntBits);
  representation_bound_setset(certificate.Model(),IntBits);
  assert U.Size(IntBits) <= 4*NatPower(Size_setint(U.Model())+1,2);
  assert S.Size(IntBits) <= 7*NatPower(Size_setsetint(S.Model())+1,3);
  assert certificate.Size(IntBits) <= 7*NatPower(Size_setsetint(certificate.Model())+1,3);
  assert NatBits(k) <= input;
  polynomial_base_monotonic(Size_setint(U.Model())+1,input+1,2);
  polynomial_base_monotonic(Size_setsetint(S.Model())+1,input+1,3);
  polynomial_base_monotonic(Size_setsetint(certificate.Model())+1,input+1,3);
  polynomial_degree_weaken(input,U.Size(IntBits),4,2,3);
  polynomial_degree_weaken(input,input,1,1,3);
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

lemma hitting_set_phase_size_bound(U:Set<int>, S:SetSet<int>, k:nat)
  ensures HittingSetPhaseSizeBound(U,S,k) <= 17*NatPower(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits)+1,3)
{
  var input := SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits);
  representation_bound_set(U.Model(),IntBits);
  representation_bound_setset(S.Model(),IntBits);
  assert U.Size(IntBits) <= 4*NatPower(Size_setint(U.Model())+1,2);
  assert S.Size(IntBits) <= 7*NatPower(Size_setsetint(S.Model())+1,3);
  assert NatBits(k) <= input;
  assert {:split_here} true;
  polynomial_base_monotonic(Size_setint(U.Model())+1,input+1,2);
  polynomial_base_monotonic(Size_setsetint(S.Model())+1,input+1,3);
  polynomial_degree_weaken(input,U.Size(IntBits),4,2,3);
  polynomial_degree_weaken(input,input+2,3,1,3);
}

lemma {:isolate_assertions} hitting_set_budget_polynomial(n:nat)
  ensures BudgetTransformHittingSetToSetCoverPhase(n) <= 258048*NatPower(n+1,14)
{
  var size := HittingSetOperandSizeBound(n);
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

lemma {:isolate_assertions} hitting_set_primitive_polynomial(n:nat)
  ensures BudgetPrimitiveStep(HittingSetOperandSizeBound(n)) <= 12288*NatPower(n+1,12)
{
  var size := HittingSetOperandSizeBound(n);
  budget_primitive_step_polynomial(size);
  hitting_set_operand_polynomial_bound(n);
  polynomial_size_substitution(n,size,BudgetPrimitiveStep(size),7,4,24,3);
  assert {:fuel NatPower,4} NatPower(8,3) == 512;
}

// Weighted primitive work; constant control is absorbed by the source audit.
lemma {:isolate_assertions} hitting_set_operand_polynomial_bound(n:nat)
  ensures HittingSetOperandSizeBound(n) <= 7*NatPower(n+1,4)
{
  reveal HittingSetOperandSizeBound();
  polynomial_product_bound(n,n,1+n,1,1,1,1);
  structural_volume_polynomial(n,n*(1+n),n,1,2);
  structural_size_polynomial(n*(1+n*(1+n)),n+1,n,2,3);
}

// A fixed output universe may contain repeated or empty incidence sets of sets.
// Bound its dimensions and all leaves once, before the executable traversal.
lemma hitting_set_output_size_bound(S:SetSet<int>, SS:SetSetSet<int>, n:nat)
  requires S.Valid() && SS.Valid()
  requires SS.UCardinality() <= n && S.Cardinality() <= n && S.Cardinality1() <= n
  requires S.LeafBits(IntBits) <= n+1
  requires forall setSet | setSet in SS.Universe() :: setSet <= S.Model()
  ensures SS.USize(IntBits) <= HittingSetOperandSizeBound(n)
{
  forall setSet | setSet in SS.Universe()
    ensures |setSet| <= n && MaxCardinality_set(setSet) <= n
    ensures MaxLeafBits_setset(setSet,IntBits) <= n+1
  {
    subset_cardinality_bound_set(setSet,S.Model());
    max_by_monotonic(setSet,S.Model(),item => |item|);
    representation_subset_setset(setSet,S.Model(),IntBits);
  }
  SS.u_cardinality1_bound(n);
  SS.u_cardinality2_bound(n);
  SS.u_volume_bound(n,n,n);
  SS.u_leaf_bits_bound(n+1,IntBits);
  SS.u_size_bound(n*(1+n*(1+n)),n+1,IntBits);
  reveal HittingSetOperandSizeBound();
}

lemma hitting_set_singleton_universe_bounds(S:SetSet<int>, SS:SetSetSet<int>)
  requires S.Valid() && SS.Valid()
  requires SS.Universe() == (set s | s in S.Model() :: {s})
  ensures SS.UVolume1() <= 1 + S.UVolume1()
  ensures SS.UCardinality1() <= 1
  ensures SS.UCardinality2() <= S.UCardinality1()
  ensures SS.UVolume2() <= S.UVolume1()
{
  forall child | child in SS.Universe()
    ensures |child| <= 1
    ensures MaxCardinality_set(child) <= S.UVolume1()
  {
    var s :| s in S.Model() && child == {s};
    reveal S.UCardinality1();
    max_by_member(S.Universe(), s, item => |item|);
    max_by_insert({}, s, item => |item|);
  }
  SS.u_cardinality1_bound(1);
  SS.u_cardinality2_bound(S.UCardinality1());
}

lemma hitting_set_incidence_universe_bounds(U:Set<int>, S:SetSet<int>, SS:SetSetSet<int>)
  requires S.Valid() && SS.Valid()
  requires SS.Universe() == (set u | u in U.Model() :: (set s | s in S.Model() && u in s))
  ensures SS.UVolume1() <= S.UVolume()
  ensures SS.UCardinality1() <= S.UCardinality()
  ensures SS.UCardinality2() <= S.UCardinality1()
  ensures SS.UVolume2() <= S.UVolume1()
{
  forall child | child in SS.Universe()
    ensures |child| <= S.UCardinality()
    ensures MaxCardinality_set(child) <= S.UVolume1()
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

ghost function BoundSetCoverCertificateSize(n:nat):(bound:nat)
  ensures bound <= SetCoverCertificateSizeCoefficient*NatPower(n+1, 1)
{ n }

ghost function BudgetTransformHittingSetToSetCover(n:nat):(bound:nat)
  ensures bound <= HittingSetToSetCoverBudgetCoefficient*NatPower(n+1, 42)
{ HittingSetToSetCoverBudgetCoefficient*NatPower(n+1, 42) }

ghost function BoundHittingSetToSetCoverOutputSize(n:nat):(bound:nat)
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

// The phase bound includes labels of rejected certificates and the stored k.
ghost function SetCoverOperandSizeBound(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>):nat
{ U.Size(IntBits)+S.Size(IntBits)+certificate.Size(IntBits)+NatBits(k) }

ghost function {:isolate_assertions} BudgetTransformHittingSetToSetCoverPhase(n:nat):(budget:nat)
  ensures var size := HittingSetOperandSizeBound(n);
    4*BudgetPrimitiveStep(size)+n*BudgetAddSingletonSourceSet(size) <= budget
  ensures var size := HittingSetOperandSizeBound(n);
    4*BudgetPrimitiveStep(size)+n*BudgetBuildIncidenceSet(n) <= budget
{
  var size := HittingSetOperandSizeBound(n);
  var setup := 4*BudgetPrimitiveStep(size);
  var singletons := n*BudgetAddSingletonSourceSet(size);
  var incidences := n*BudgetBuildIncidenceSet(n);
  assert setup+singletons <= setup+singletons+incidences;
  assert setup+incidences <= setup+singletons+incidences;
  setup+singletons+incidences
}

// Bounds growing sets of sets of sets; construction may exceed input size.
ghost function {:opaque} HittingSetOperandSizeBound(n:nat):(size:nat)
  ensures n <= size && 1 <= size
{ StructuralSize(n*(1+n*(1+n)),n+1) }

ghost function BudgetAddSingletonSourceSet(size:nat):nat
{ 6*BudgetPrimitiveStep(size) }

ghost function {:opaque} BudgetBuildIncidenceSet(n:nat):(budget:nat)
  ensures var size := HittingSetOperandSizeBound(n);
    4*BudgetPrimitiveStep(size)+n*BudgetAddIncidentSourceSet(size)+2*BudgetPrimitiveStep(size) <= budget
{
  var size := HittingSetOperandSizeBound(n);
  4*BudgetPrimitiveStep(size)+n*BudgetAddIncidentSourceSet(size)+2*BudgetPrimitiveStep(size)
}

ghost function BudgetAddIncidentSourceSet(size:nat):nat
{ 5*BudgetPrimitiveStep(size) }

// Phase bound for input representation, dimensions, label weights and stored k.
// hitting_set_phase_size_bound relates it to canonical source instance size.
ghost function HittingSetPhaseSizeBound(U:Set<int>, S:SetSet<int>, k:nat):nat
{ U.Size(IntBits)+S.Size(IntBits)+2+NatBits(k) }

// Auxiliary representation bound used to primitiveBudget output operands; this is not an
// alternative instance size. It dominates the exact destination size below.
ghost function HittingSetOutputOperandSizeBound(r:SetCoverSetIntInstance):nat
{ 1+r.0.Size(IntBits)+r.1.Size(IntBits)+NatBits(r.2) }

// Constants

// Fixed cost envelope in canonical verifier input size, including the candidate.
ghost const VerifySetCoverBudgetCoefficient:nat := 364*NatPower(22, 5)

// Fixed cost envelope in canonical source instance size.
ghost const HittingSetToSetCoverBudgetCoefficient:nat := 258048*NatPower(18, 14)

// Fixed output-size envelope in canonical source instance size.
ghost const HittingSetToSetCoverOutputSizeCoefficient:nat := 10*NatPower(18, 4)

ghost const SetCoverCertificateSizeCoefficient:nat := 1
