include "../Polynomial/PolynomialSetCover.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Arithmetic/CostedArithmetic.dfy"
include "../Collections/ConcreteSet.dfy"
include "../Problems/SetCover.dfy"
include "../Collections/Set.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"

// Every positive instance has an initialized, correct certificate of linear size.
ghost method SetCoverHasShortCertificate<T>(instance:SetSystemInstance<T>) returns (certificate:SetSet<T>)
  requires instance.universe.Init() && instance.sets.Init()
  requires SetCoverValidInstance(instance.Model())
  requires SetCover(instance.Model())
  ensures fresh(certificate)
  ensures certificate.Init()
  ensures SetCoverCertificate(instance.Model(), certificate.Model())
  ensures forall weight:T -> nat ::
    SetCoverCertificateSize(certificate.Model(), weight) <= BudgetSetCoverCertificateSize(
      SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var certificateModel :| certificateModel <= S.Model() && SetCoverCertificate(instance.Model(), certificateModel);
  certificate := new ConcreteSetSet<T>(certificateModel, certificateModel);
  forall weight:T -> nat
    ensures SetCoverCertificateSize(certificate.Model(), weight) <=
      BudgetSetCoverCertificateSize(SetSystemInstanceSize(U.Model(), S.Model(), k, weight))
  {
    set_cover_certificate_instance_size_bound(U.Model(), S.Model(), k, certificate.Model(), weight);
  }
}

// Collection and arithmetic primitives advance one weighted counter.
method VerifySetCover<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, ghost weight:T -> nat)
    returns (accepted:bool, ghost counter:nat)
  requires instance.universe.Init() && instance.sets.Init() && certificate.Init()
  requires SetCoverValidInstance(instance.Model())
  ensures accepted == SetCoverCertificate(instance.Model(), certificate.Model())
  ensures accepted ==> SetCover(instance.Model())
  ensures 0 < counter <= BudgetVerifySetCover(SetCoverInputSize(
    instance.universe.Model(), instance.sets.Model(), instance.k, certificate.Model(), weight))
{
  var U, S := instance.universe, instance.sets;
  budget_verify_set_cover_input_bound(instance, certificate, weight);
  ghost var n := SetCoverInputSizeBound(instance, certificate, weight);
  var admissible:bool;
  admissible, counter := CheckSetCoverCertificateAdmissible(U, S, certificate, weight, n, 0);
  if admissible {
    accepted, counter := VerifySetCoverCore(instance, certificate, weight, n, counter);
  } else {
    accepted := false;
    if SetCoverCertificate(instance.Model(), certificate.Model()) {
      set_cover_certificate_cardinality_bounds(instance.Model(), certificate.Model());
      assert false;
    }
  }
}


// Check structural admissibility.
method CheckSetCoverCertificateAdmissible<T>(U:Set<T>, S:SetSet<T>, certificate:SetSet<T>,
    ghost weight:T -> nat, ghost n:nat, ghost counter_in:nat)
    returns (admissible:bool, ghost counter:nat)
  // Representation in
  requires U.SizeBound(weight) <= n && S.SizeBound(weight) <= n && certificate.SizeBound(weight) <= n
  requires U.Init() && S.Init() && certificate.Init()
  // State out
  ensures admissible == (certificate.Cardinality() <= S.Cardinality() &&
    forall member | member in certificate.Model() :: |member| <= U.Cardinality())
  ensures admissible ==> certificate.UVolumeBound1() <= U.UVolumeBound()
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetCheckSetCoverCertificateAdmissible(n)
{
  ghost var context := BitSetCost(weight, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
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
  var remaining:SetSet<T> := certificate;
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
    var member:Set<T>;
    member, counter := remaining.Pick(counter, context);
    var memberCount:nat;
    memberCount, counter := member.Count(counter, context);
    nat_bits_linear_bound(memberCount);
    admissible, counter := LessEqualNat(memberCount, width, counter);
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
method VerifySetCoverCore<T>(instance:SetSystemInstance<T>, certificate:SetSet<T>, ghost weight:T -> nat,
    ghost n:nat, ghost counter_in:nat)
    returns (accepted:bool, ghost counter:nat)
  // Representation in
  requires instance.universe.SizeBound(weight) <= n && instance.sets.SizeBound(weight) <= n && certificate.SizeBound(weight) <= n
  requires NatBits(instance.k) <= n
  requires SetCoverValidInstance(instance.Model())
  requires instance.universe.Init() && instance.sets.Init() && certificate.Init()
  requires certificate.UVolumeBound1() <= instance.universe.UVolumeBound()
  requires certificate.Cardinality() <= instance.sets.Cardinality()
  // State out
  ensures accepted == SetCoverCertificate(instance.Model(), certificate.Model())
  ensures accepted ==> SetCover(instance.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetVerifySetCoverCore(n)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  ghost var context := BitSetCost(weight, n);
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
  isSubset, counter := IsSubset(certificate, S, counter, weight, n);
  assert counter <= counter_in + 2*primitiveBudget + BudgetIsSubset(n);
  if (!isSubset) {
    return false, counter;
  }
  var remainingUniverse:Set<T>;
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
    invariant certificate.UVolumeBound1() <= U.UVolumeBound()
    // State
    invariant accepted == IsCover(U.Model() - remainingUniverse.Model() , certificate.Model())
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(loopBase, BudgetCheckUniverseElement(n),
      U.Cardinality() - remainingUniverse.Cardinality())
  {
    linear_loop_budget_step(loopBase, BudgetCheckUniverseElement(n), U.Cardinality() - remainingUniverse.Cardinality());
    accepted, remainingUniverse, remainingUniverseEmpty, counter := CheckUniverseElement(
      U, S, certificate, remainingUniverse, counter, weight, n);
  }
  assert accepted ==> U.Model() - remainingUniverse.Model() == U.Model();
  linear_loop_budget_bound(loopBase, BudgetCheckUniverseElement(n), U.Cardinality() - remainingUniverse.Cardinality(), n);
  assert counter <= loopBase + n*BudgetCheckUniverseElement(n);
  assert counter <= counter_in + BudgetVerifySetCoverCore(n);
}


method IsSubset<T>(S1:SetSet<T>, S2:SetSet<T>, ghost counter_in:nat, ghost weight:T -> nat, ghost n:nat)
    returns (b:bool, ghost counter:nat)
  // Representation in
  requires S1.SizeBound(weight) <= n && S2.SizeBound(weight) <= n
  requires S1.Init() && S2.Valid()
  // State out
  ensures b == (S1.Model() <= S2.Model())
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetIsSubset(n)
{
  ghost var context := BitSetCost(weight, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  counter := counter_in;
  b := true;
  var S1':SetSet<T>;
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
    S1', S1'_empty, b, counter := IsSubsetStep(S1, S2, S1', counter, b, weight, n);
  }
  linear_loop_budget_bound(loopBase, BudgetIsSubsetStep(n), S1.Cardinality() - S1'.Cardinality(), n);
}


method IsSubsetStep<T>(S1:SetSet<T>, S2:SetSet<T>, S1':SetSet<T>,
    ghost counter_in:nat, b:bool, ghost weight:T -> nat, ghost n:nat)
    returns (S1'':SetSet<T>, S1'_empty:bool, b':bool, ghost counter:nat)
  // Progress in
  requires S1'.Model() != {}
  // Representation in
  requires S1.SizeBound(weight) <= n && S2.SizeBound(weight) <= n
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
  ghost var context := BitSetCost(weight, n);
  S1'.universe_within_bound(S1, context);
  counter := counter_in;
  var s:Set<T>;
  s, counter := S1'.Pick(counter, context);

  var s_in_S2:bool;
  s_in_S2, counter := S2.Contains(s, counter, context);
  b' := b && s_in_S2;

  S1'', counter := S1'.Remove(s, counter, context);
  S1'_empty, counter := S1''.IsEmpty(counter, context);
}


method CheckUniverseElement<T>(U:Set<T>, S:SetSet<T>, certificate:SetSet<T>, remainingUniverse:Set<T>,
    ghost counter_in:nat, ghost weight:T -> nat, ghost n:nat)
    returns (covered:bool, remainingUniverseOut:Set<T>, remainingUniverseOutEmpty:bool, ghost counter:nat)
  // Progress in
  requires remainingUniverse.Model() != {}
  // Representation in
  requires U.SizeBound(weight) <= n && S.SizeBound(weight) <= n && certificate.SizeBound(weight) <= n
  requires U.Valid()
  requires S.Valid()
  requires certificate.Init()
  requires remainingUniverse.UniverseWithin(U)
  requires certificate.Model() <= S.Model()
  requires certificate.Cardinality() <= S.Cardinality()
  requires certificate.UVolumeBound1() <= U.UVolumeBound()
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
  ghost var context := BitSetCost(weight, n);
  ghost var primitiveBudget := BudgetPrimitiveStep(n);
  remainingUniverse.universe_within_bound(U, context);
  counter := counter_in;
  var u:T;
  u, counter := remainingUniverse.Pick(counter, context);
  remainingUniverseOut, counter := remainingUniverse.Remove(u, counter, context);

  var remainingCertificate:SetSet<T>;
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
    invariant weight(u) <= n
    invariant remainingCertificate.UniverseWithin(certificate)
    invariant certificate.Init()
    invariant S.Valid()
    invariant certificate.Cardinality() <= S.Cardinality()
    invariant certificate.UVolumeBound1() <= U.UVolumeBound()
    // State
    invariant elementCovered == (exists i' | i' in certificate.Model() - remainingCertificate.Model() :: u in i')
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(setup, BudgetCheckCoverSet(n),
      certificate.Cardinality()-remainingCertificate.Cardinality())
  {
    linear_loop_budget_step(setup, BudgetCheckCoverSet(n),
      certificate.Cardinality()-remainingCertificate.Cardinality());
    elementCovered, remainingCertificate, remainingCertificateEmpty, counter := CheckCoverSet(
      U, S, certificate, remainingCertificate, u, counter, weight, n);
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


method CheckCoverSet<T>(U:Set<T>, S:SetSet<T>, certificate:SetSet<T>, remainingCertificate:SetSet<T>, u:T,
    ghost counter_in:nat, ghost weight:T -> nat, ghost n:nat)
    returns (elementCovered:bool, remainingCertificateOut:SetSet<T>, remainingCertificateOutEmpty:bool, ghost counter:nat)
  // Progress in
  requires remainingCertificate.Model() != {}
  // Representation in
  requires U.SizeBound(weight) <= n && S.SizeBound(weight) <= n && certificate.SizeBound(weight) <= n
  requires weight(u) <= n
  requires U.Valid()
  requires S.Valid()
  requires certificate.Valid()
  requires remainingCertificate.UniverseWithin(certificate)
  requires certificate.Cardinality() <= S.Cardinality()
  requires certificate.UVolumeBound1() <= U.UVolumeBound()
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
  ghost var context := BitSetCost(weight, n);
  remainingCertificate.universe_within_bound(certificate, context);
  counter := counter_in;
  var i:Set<T>;
  i, counter := remainingCertificate.Pick(counter, context);
  elementCovered, counter := i.Contains(u, counter, context);
  remainingCertificateOut, counter := remainingCertificate.Remove(i, counter, context);
  remainingCertificateOutEmpty, counter := remainingCertificateOut.IsEmpty(counter, context);
}
