include "../Polynomial/PolynomialSetCover.dfy"
include "../Foundations/CollectionSizes.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Arithmetic/CostedArithmetic.dfy"
include "../Collections/ConcreteSet.dfy"
include "../Problems/SetCoverLemmas.dfy"
include "../Collections/Set.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/Collections.dfy"
include "../Foundations/LoopCosts.dfy"

/*
The public verifier accepts exactly the initialized Set Cover certificates.
Weighted collection and arithmetic charges advance one counter. The source audit
absorbs constant control; the public exit returns the accumulated budget.
Its fixed input-size polynomial is conditional on the realization model;
binary decoding and bit-level implementation proofs remain separate. The native
_base/_simple variants retain structural counters and the same acceptance semantics.
*/

// Every positive instance has an initialized, correct certificate of linear size.
ghost method SetCoverHasShortCertificate(U:Set<int>, S:SetSet<int>, k:nat) returns (certificate:SetSet<int>)
  requires U.Init() && S.Init()
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires SetCover(U.Model(), S.Model(), k)
  ensures fresh(certificate)
  ensures certificate.Init()
  ensures SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model())
  ensures SetCoverCertificateSize(certificate.Model(), IntBits) <=
          BoundSetCoverCertificateSize(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
{
  var certificateModel :| certificateModel <= S.Model() && SetCoverCertificate(U.Model(), S.Model(), k, certificateModel);
  certificate := new ConcreteSetSet<int>(certificateModel, certificateModel);
  set_cover_certificate_instance_size_bound(U.Model(), S.Model(), k, certificate.Model(), IntBits);
}

// Collection and arithmetic primitives advance one weighted counter.
method VerifySetCover(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>) returns (accepted:bool, ghost counter:nat)
  requires U.Init() && S.Init() && certificate.Init()
  requires SetCoverValidInstance(U.Model(), S.Model())
  ensures accepted == SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model())
  ensures accepted ==> SetCover(U.Model(), S.Model(), k)
  ensures 0 < counter <= BudgetVerifySetCover(SetCoverInputSize(U.Model(), S.Model(), k, certificate.Model(), IntBits))
{
  budget_verify_set_cover_input_bound(U, S, k, certificate);
  ghost var n:nat := SetCoverOperandSizeBound(U, S, k, certificate);
  var admissible:bool;
  admissible, counter := CheckSetCoverCertificateAdmissible(U, S, certificate, n, 0);
  if admissible {
    accepted, counter := VerifySetCoverCore(U, S, k, certificate, n, counter);
  } else {
    accepted := false;
    if SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model()) {
      set_cover_certificate_volume_bound(U.Model(), S.Model(), k, certificate.Model());
      assert false;
    }
  }
}


// Check only structural admissibility; neither coverage nor membership in S is assumed.
// Initialization is a representation invariant of the supplied collection, as for U and S.
method CheckSetCoverCertificateAdmissible(U:Set<int>, S:SetSet<int>, certificate:SetSet<int>, ghost n:nat, ghost counter_in:nat)
    returns (admissible:bool, ghost counter:nat)
  // Representation in
  requires U.Size(IntBits) <= n && S.Size(IntBits) <= n && certificate.Size(IntBits) <= n
  requires U.Init() && S.Init() && certificate.Init()
  // State out
  ensures admissible == (certificate.Cardinality() <= S.Cardinality() &&
    forall member | member in certificate.Model() :: |member| <= U.Cardinality())
  ensures admissible ==> certificate.UVolume1() <= U.UVolume()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCheckSetCoverCertificateAdmissible(n)
{
  ghost var context := BitSetCost(IntBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  nat_multiplication_monotonic(S.Cardinality(), 1, 1+S.Cardinality1());
  nat_multiplication_monotonic(certificate.Cardinality(), 1, 1+certificate.Cardinality1());
  var count:nat;
  var limit:nat;
  var width:nat;
  count, counter := certificate.Count(counter_in, context);
  limit, counter := S.Count(counter, context);
  width, counter := U.Count(counter, context);
  assert count <= n && limit <= n && width <= n;
  assert counter <= counter_in + 3*primitiveBudget;
  var fits:bool;
  nat_bits_linear_bound(count);
  nat_bits_linear_bound(limit);
  nat_bits_linear_bound(width);
  fits, counter := LessEqualNat(count, limit, counter);
  assert counter <= counter_in + 4*primitiveBudget;
  if (!fits) {
    admissible := false;
    return;
  }
  var remaining:SetSet<int> := certificate;
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter, context);
  admissible := true;
  ghost var base := counter_in + 5*primitiveBudget;
  ghost var step := 5*primitiveBudget;
  assert counter <= base;
  linear_loop_budget_zero(base, step);
  while (!empty && admissible)
    // Progress
    decreases remaining.Cardinality()
    // Representation
    invariant remaining.UniverseWithin(certificate)
    invariant remaining.Universe() == certificate.Universe()
    // State
    invariant empty == (remaining.Model() == {})
    invariant admissible == (forall member | member in certificate.Model() - remaining.Model() :: |member| <= width)
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(base, step, certificate.Cardinality() - remaining.Cardinality())
  {
    ghost var before := counter;
    ghost var processed := certificate.Cardinality()-remaining.Cardinality();
    linear_loop_budget_step(base, step, certificate.Cardinality() - remaining.Cardinality());
    remaining.universe_within_bound(certificate, context);
    var member:Set<int>;
    member, counter := remaining.Pick(counter, context);
    var memberVolume:nat;
    memberVolume, counter := member.Count(counter, context);
    nat_bits_linear_bound(memberVolume);
    admissible, counter := LessEqualNat(memberVolume, width, counter);
    remaining, counter := remaining.Remove(member, counter, context);
    empty, counter := remaining.IsEmpty(counter, context);
    assert counter <= before + step;
    assert certificate.Cardinality()-remaining.Cardinality() == processed+1;
    assert counter <= LinearLoopBudget(base,step,processed)+step;
  }
  linear_loop_budget_bound(base, step, certificate.Cardinality() - remaining.Cardinality(), n);
  assert counter <= counter_in + BudgetCheckSetCoverCertificateAdmissible(n);
  if (admissible) {
    certificate.u_cardinality1_bound(U.Cardinality());
  }
}


// Verify coverage and cardinality after the public entry establishes admissibility.
method VerifySetCoverCore(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>, ghost n:nat, ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Representation in
  requires U.Size(IntBits) <= n && S.Size(IntBits) <= n && certificate.Size(IntBits) <= n
  requires NatBits(k) <= n
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires U.Init() && S.Init() && certificate.Init()
  requires certificate.UVolume1() <= U.UVolume()
  requires certificate.Cardinality() <= S.Cardinality()
  // State out
  ensures accepted == SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model())
  ensures accepted ==> SetCover(U.Model(), S.Model(), k)
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetVerifySetCoverCore(n)
{
  ghost var context := BitSetCost(IntBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  counter := counter_in;
  var certificateCardinality:nat;
  certificateCardinality, counter := certificate.Count(counter, context);
  var fits:bool;
  nat_bits_linear_bound(certificateCardinality);
  fits, counter := LessEqualNat(certificateCardinality, k, counter);
  assert counter <= counter_in + 2*primitiveBudget;
  if (!fits) {
    return false, counter;
  }
  var isSubset:bool;
  isSubset, counter := IsSubset(certificate, S, counter, n);
  assert counter <= counter_in + 2*primitiveBudget + BudgetIsSubset(n);
  if (!isSubset) {
    return false, counter;
  }
  var remainingUniverse:Set<int>;
  remainingUniverse := U;
  accepted := true;
  var remainingUniverseEmpty:bool;
  remainingUniverseEmpty, counter := remainingUniverse.IsEmpty(counter, context);
  
  ghost var loopBase := counter_in + 3*primitiveBudget + BudgetIsSubset(n);
  linear_loop_budget_zero(loopBase, BudgetCheckUniverseElement(n));
  while (!remainingUniverseEmpty && accepted)
    // Progress
    decreases remainingUniverse.Cardinality()
    invariant remainingUniverseEmpty == (remainingUniverse.Model() == {})
    // Representation
    invariant remainingUniverse.UniverseWithin(U)
    invariant certificate.Valid()
    invariant S.Valid()
    invariant certificate.Model() <= S.Model()
    invariant certificate.Cardinality() <= S.Cardinality()
    invariant certificate.UVolume1() <= U.UVolume()
    // State
    invariant accepted == IsCover(U.Model() - remainingUniverse.Model() , certificate.Model())
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(loopBase, BudgetCheckUniverseElement(n),
      U.Cardinality() - remainingUniverse.Cardinality())
  {
    linear_loop_budget_step(loopBase, BudgetCheckUniverseElement(n), U.Cardinality() - remainingUniverse.Cardinality());
    accepted, remainingUniverse, remainingUniverseEmpty, counter := CheckUniverseElement(U, S, k, certificate, remainingUniverse, counter, n);
  }
  assert accepted ==> U.Model() - remainingUniverse.Model() == U.Model();
  linear_loop_budget_bound(loopBase, BudgetCheckUniverseElement(n), U.Cardinality() - remainingUniverse.Cardinality(), n);
  assert counter <= loopBase + n*BudgetCheckUniverseElement(n);
  assert counter <= counter_in + BudgetVerifySetCoverCore(n);
}


method IsSubset(S1:SetSet<int>, S2:SetSet<int>, ghost counter_in:nat, ghost n:nat) returns (b:bool, ghost counter:nat)
  // Representation in
  requires S1.Size(IntBits) <= n && S2.Size(IntBits) <= n
  requires S1.Init() && S2.Valid()
  // State out
  ensures b == (S1.Model() <= S2.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetIsSubset(n)
{
  ghost var context := BitSetCost(IntBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  counter := counter_in;
  b := true;
  var S1':SetSet<int>;
  S1' := S1;
  var S1'_empty:bool;
  S1'_empty, counter := S1'.IsEmpty(counter, context);
  
  ghost var loopBase := counter_in + primitiveBudget;
  linear_loop_budget_zero(loopBase, BudgetIsSubsetStep(n));
  while (!S1'_empty)
  // Progress
  decreases S1'.Cardinality()
  invariant S1'_empty == (S1'.Model() == {})
  // Representation
  invariant S1'.Valid()
  invariant S1'.UniverseWithin(S1)
  // State
  invariant b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Cost
  invariant counter_in < counter
  invariant counter <= LinearLoopBudget(loopBase, BudgetIsSubsetStep(n),
    S1.Cardinality() - S1'.Cardinality())
  {
    linear_loop_budget_step(loopBase, BudgetIsSubsetStep(n), S1.Cardinality() - S1'.Cardinality());
    S1', S1'_empty, b, counter := IsSubsetStep(S1, S2, S1', counter, b, n);
  }
  linear_loop_budget_bound(loopBase, BudgetIsSubsetStep(n), S1.Cardinality() - S1'.Cardinality(), n);
}


method IsSubsetStep(S1:SetSet<int>, S2:SetSet<int>, S1':SetSet<int>, ghost counter_in:nat, b:bool, ghost n:nat)
    returns (S1'':SetSet<int>, S1'_empty:bool, b':bool, ghost counter:nat)
  // Progress in
  requires S1'.Model() != {}
  // Representation in
  requires S1.Size(IntBits) <= n && S2.Size(IntBits) <= n
  requires S1'.UniverseWithin(S1)
  requires S2.Valid()
  // State in
  requires b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Progress out
  ensures S1''.Cardinality() == S1'.Cardinality() - 1
  ensures S1'_empty == (S1''.Model() == {})
  // Representation out
  ensures S1''.UniverseWithin(S1)
  // State out
  ensures b' == ((S1.Model() - S1''.Model()) <= S2.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetIsSubsetStep(n)
{
  ghost var context := BitSetCost(IntBits, n);
  S1'.universe_within_bound(S1, context);
  counter := counter_in;
  var s:Set<int>;
  s, counter := S1'.Pick(counter, context);

  var s_in_S2:bool;
  s_in_S2, counter := S2.Contains(s, counter, context);
  b' := b && s_in_S2;

  S1'', counter := S1'.Remove(s, counter, context);
  S1'_empty, counter := S1''.IsEmpty(counter, context);
}


method CheckUniverseElement(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>, remainingUniverse:Set<int>, ghost counter_in:nat, ghost n:nat)
    returns (covered:bool, remainingUniverseOut:Set<int>, remainingUniverseOutEmpty:bool, ghost counter:nat)
  // Progress in
  requires remainingUniverse.Model() != {}
  // Representation in
  requires U.Size(IntBits) <= n && S.Size(IntBits) <= n && certificate.Size(IntBits) <= n
  requires U.Valid()
  requires S.Valid()
  requires certificate.Init()
  requires remainingUniverse.UniverseWithin(U)
  requires certificate.Model() <= S.Model()
  requires certificate.Cardinality() <= S.Cardinality()
  requires certificate.UVolume1() <= U.UVolume()
  // State in
  requires IsCover(U.Model() - remainingUniverse.Model(), certificate.Model())
  // Progress out
  ensures remainingUniverseOut.Cardinality() == remainingUniverse.Cardinality() - 1
  ensures remainingUniverseOutEmpty == (remainingUniverseOut.Model() == {})
  // Representation out
  ensures remainingUniverseOut.UniverseWithin(U)
  // State out
  ensures covered == IsCover(U.Model() - remainingUniverseOut.Model(), certificate.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCheckUniverseElement(n)
{
  ghost var context := BitSetCost(IntBits, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  remainingUniverse.universe_within_bound(U, context);
  counter := counter_in;
  var u:int;
  u, counter := remainingUniverse.Pick(counter, context);
  remainingUniverseOut, counter := remainingUniverse.Remove(u, counter, context);

  var remainingCertificate:SetSet<int>;
  remainingCertificate := certificate;

  var elementCovered:bool := false;
  var remainingCertificateEmpty:bool;
  remainingCertificateEmpty, counter := remainingCertificate.IsEmpty(counter, context);
  ghost var setup := counter_in+3*primitiveBudget;
  assert counter <= setup;
  linear_loop_budget_zero(setup, BudgetCheckCoverSet(n));
  while (!remainingCertificateEmpty && !elementCovered)
    // Progress
    decreases remainingCertificate.Cardinality()
    invariant remainingCertificateEmpty == (remainingCertificate.Model() == {})
    // Representation
    invariant IntBits(u) <= n
    invariant remainingCertificate.UniverseWithin(certificate)
    invariant certificate.Init()
    invariant S.Valid()
    invariant certificate.Cardinality() <= S.Cardinality()
    invariant certificate.UVolume1() <= U.UVolume()
    // State
    invariant elementCovered == (exists i' | i' in certificate.Model() - remainingCertificate.Model() :: u in i')
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(setup, BudgetCheckCoverSet(n),
      certificate.Cardinality()-remainingCertificate.Cardinality())
  {
    linear_loop_budget_step(setup, BudgetCheckCoverSet(n),
      certificate.Cardinality()-remainingCertificate.Cardinality());
    elementCovered, remainingCertificate, remainingCertificateEmpty, counter := CheckCoverSet(U, S, k, certificate, remainingCertificate, u, counter, n);
  }
  linear_loop_budget_bound(setup, BudgetCheckCoverSet(n), certificate.Cardinality()-remainingCertificate.Cardinality(), n);
  covered := elementCovered;

  remainingUniverseOut.universe_within_bound(U, context);
  remainingUniverseOutEmpty, counter := remainingUniverseOut.IsEmpty(counter, context);

  assert U.Model() - remainingUniverseOut.Model() == U.Model() - remainingUniverse.Model() + {u};
  assert counter <= counter_in + 3*primitiveBudget +
                       n*BudgetCheckCoverSet(n) +
                       primitiveBudget;
}


method CheckCoverSet(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>, remainingCertificate:SetSet<int>, u:int, ghost counter_in:nat, ghost n:nat)
    returns (elementCovered:bool, remainingCertificateOut:SetSet<int>, remainingCertificateOutEmpty:bool, ghost counter:nat)
  // Progress in
  requires remainingCertificate.Model() != {}
  // Representation in
  requires U.Size(IntBits) <= n && S.Size(IntBits) <= n && certificate.Size(IntBits) <= n
  requires IntBits(u) <= n
  requires U.Valid()
  requires S.Valid()
  requires certificate.Valid()
  requires remainingCertificate.UniverseWithin(certificate)
  requires certificate.Cardinality() <= S.Cardinality()
  requires certificate.UVolume1() <= U.UVolume()
  // State in
  requires !(exists i' | i' in certificate.Model() - remainingCertificate.Model() :: u in i')
  // Progress out
  ensures remainingCertificateOut.Cardinality() == remainingCertificate.Cardinality() - 1
  ensures remainingCertificateOutEmpty == (remainingCertificateOut.Model() == {})
  // Representation out
  ensures remainingCertificateOut.UniverseWithin(certificate)
  // State out
  ensures elementCovered == (exists i' | i' in certificate.Model() - remainingCertificateOut.Model() :: u in i')
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCheckCoverSet(n)
{
  ghost var context := BitSetCost(IntBits, n);
  remainingCertificate.universe_within_bound(certificate, context);
  counter := counter_in;
  var i:Set<int>;
  i, counter := remainingCertificate.Pick(counter, context);
  elementCovered, counter := i.Contains(u, counter, context);
  remainingCertificateOut, counter := remainingCertificate.Remove(i, counter, context);
  remainingCertificateOutEmpty, counter := remainingCertificateOut.IsEmpty(counter, context);
}
