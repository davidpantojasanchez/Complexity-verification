include "../Lemmas/PolynomialBounds.dfy"
include "../Collections/ConcreteSet.dfy"
include "../Problems/SetCoverLemmas.dfy"
include "../Collections/Set.dfy"
include "../Lemmas/Lemmas.dfy"

/*
The verifier and its proofs establish a certificate characterization in the
initialized-collection, atomic-label, abstract-operation-cost model:

* Every positive instance has an initialized, correct, polynomially short certificate.
* Acceptance is equivalent to correctness of the supplied certificate.
* The operation counter has a polynomial bound for every initialized candidate,
  including rejected candidates, with an instance-only bound for short candidates.

An end-to-end bit-time NP theorem additionally requires a costed representation
of labels and certificates, decoding/validation, and a simulation of primitive
operations. Those obligations remain future work; they are not discharged by
the structural collection measures or the operation counter bounds.
*/


// SHORT-CERTIFICATE COMPLETENESS
// Every positive instance has an initialized, correct and polynomially short witness.
ghost method SetCoverHasShortCertificate(U:Set<int>, S:SetSet<int>, k:nat) returns (certificate:SetSet<int>)
  requires U.Init() && S.Init()
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires SetCover(U.Model(), S.Model(), k)
  ensures fresh(certificate)
  ensures certificate.Init()
  ensures SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model())
  ensures certificate.Cardinality() + certificate.Size() + 1 <=
    PolynomialSetCoverCertificateSize(U.Cardinality() + S.Cardinality() + 1)
{
  var certificateModel :| certificateModel <= S.Model() && SetCoverCertificate(U.Model(), S.Model(), k, certificateModel);
  certificate := new ConcreteSetSet<int>(certificateModel, certificateModel);
  set_cover_certificate_size_bound(U.Model(), S.Model(), k, certificateModel);
  family_subset_cardinality_bound(certificate.Universe(), U.Model());
  certificate.u_cardinality1_bound(U.USize());
  var n := U.Cardinality() + S.Cardinality() + 1;
  certificate.u_size_bound(n, n);
}

// POLYNOMIAL VERIFICATION

// Bounds PolynomialVerifySetCover by a fixed polynomial in the scalar instance size.
// This envelope applies to verification of polynomially short candidate certificates.
// Note that this does not directly depend on the instance of the problem; the relationship
// between PolynomialVerifySetCover and the verification of Set Cover is defined later.
lemma polynomial_verify_set_cover_bound()
  ensures HasPolynomialBound(
    (n:nat) => true,
    (n:nat) => n,
    PolynomialVerifySetCover, 63, 4)
  ensures IsPolynomial(
    (n:nat) => true,
    (n:nat) => n,
    PolynomialVerifySetCover)
{
  forall n:nat
    ensures PolynomialVerifySetCover(n) <= 63 * NatPower(n+1, 4)
  {
    assert {:fuel NatPower, 5} PolynomialVerifySetCover(n) ==
      16*NatPower(n, 0) + 17*NatPower(n, 1) + 18*NatPower(n, 2) +
      9*NatPower(n, 3) + 3*NatPower(n, 4);
    weighted_monomial_bound(n, n, 0, 4, 16);
    weighted_monomial_bound(n, n, 1, 4, 17);
    weighted_monomial_bound(n, n, 2, 4, 18);
    weighted_monomial_bound(n, n, 3, 4, 9);
    weighted_monomial_bound(n, n, 4, 4, 3);
  }
  polynomial_witness(
    (n:nat) => true,
    (n:nat) => n,
    PolynomialVerifySetCover,
    63, 4);
}

// Similar to polynomial_verify_set_cover_bound, but determines separately that the admissibility
// criterion is polynomial with respect to the certificate, and that the core of the verification
// is polynomial with respect to (only) the size of the instance.
// Not technically necessary for demonstrating that Set Cover is in NP.
lemma {:isolate_assertions} polynomial_verify_set_cover_general_bound()
  ensures HasPolynomialBound(
    (x:(nat,nat)) => true,
    (x:(nat,nat)) => x.0+x.1,
    (x:(nat,nat)) => PolynomialCheckSetCoverCertificateAdmissible(x.1)+PolynomialVerifySetCoverCore(x.0), 39, 4)
  ensures IsPolynomial(
    (x:(nat,nat)) => true,
    (x:(nat,nat)) => x.0+x.1,
    (x:(nat,nat)) => PolynomialCheckSetCoverCertificateAdmissible(x.1)+PolynomialVerifySetCoverCore(x.0))
{
  forall x:(nat,nat)
    ensures PolynomialCheckSetCoverCertificateAdmissible(x.1)+PolynomialVerifySetCoverCore(x.0) <=
      39 * NatPower(x.0+x.1+1, 4)
  {
    var n := x.0;
    var m := x.1;
    assert {:fuel NatPower, 5} PolynomialCheckSetCoverCertificateAdmissible(m)+PolynomialVerifySetCoverCore(n) ==
      10*NatPower(n, 0) + 9*NatPower(n, 1) + 8*NatPower(n, 2) +
      5*NatPower(n, 3) + NatPower(n, 4) + 4*NatPower(m, 1) + 2*NatPower(m, 2);
    weighted_monomial_bound(n, n+m, 0, 4, 10);
    weighted_monomial_bound(n, n+m, 1, 4, 9);
    weighted_monomial_bound(n, n+m, 2, 4, 8);
    weighted_monomial_bound(n, n+m, 3, 4, 5);
    weighted_monomial_bound(n, n+m, 4, 4, 1);
    weighted_monomial_bound(m, n+m, 1, 4, 4);
    weighted_monomial_bound(m, n+m, 2, 4, 2);
  }
  polynomial_witness(
    (x:(nat,nat)) => true,
    (x:(nat,nat)) => x.0+x.1,
    (x:(nat,nat)) => PolynomialCheckSetCoverCertificateAdmissible(x.1)+PolynomialVerifySetCoverCore(x.0),
    39, 4);
}

// Bounds the operation cost, including admissibility, polynomially in instance and certificate sizes.
// For polynomially short candidates, also exports a bound in the instance size alone.
lemma {:isolate_assertions} cost_verify_set_cover_is_polynomial(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>)
  requires U.Init() && S.Init() && certificate.Init()
  requires SetCoverValidInstance(U.Model(), S.Model())
  ensures CostVerifySetCover(U, S, k, certificate) <=
    PolynomialCheckSetCoverCertificateAdmissible(certificate.Cardinality() + certificate.Size() + 1) +
    PolynomialVerifySetCoverCore(U.Cardinality() + S.Cardinality() + 1)
  ensures CostVerifySetCover(U, S, k, certificate) <=
    39 * NatPower(U.Cardinality() + S.Cardinality() + certificate.Cardinality() + certificate.Size() + 3, 4)
  ensures certificate.Cardinality() + certificate.Size() + 1 <= PolynomialSetCoverCertificateSize(U.Cardinality() + S.Cardinality() + 1) ==>
    CostVerifySetCover(U, S, k, certificate) <= PolynomialVerifySetCover(U.Cardinality() + S.Cardinality() + 1)
  ensures certificate.Cardinality() + certificate.Size() + 1 <= PolynomialSetCoverCertificateSize(U.Cardinality() + S.Cardinality() + 1) ==>
    CostVerifySetCover(U, S, k, certificate) <= 63 * NatPower((U.Cardinality() + S.Cardinality() + 1)+1, 4)
{
  cost_check_set_cover_certificate_admissible_to_polynomial(certificate);
  if certificate.Cardinality() <= S.Cardinality() && certificate.USize1() <= U.USize() {
    family_subset_cardinality_bound(S.Universe(), U.Model());
    S.u_cardinality1_bound(|U.Model()|);
    cost_verify_set_cover_core_to_polynomial(U, S, k, certificate);
  }
  ghost var n := U.Cardinality() + S.Cardinality() + 1;
  ghost var size := certificate.Cardinality() + certificate.Size() + 1;
  polynomial_verify_set_cover_general_bound();
  apply_polynomial_bound<(nat,nat)>((x:(nat,nat)) => true, (x:(nat,nat)) => x.0+x.1,
    (x:(nat,nat)) => PolynomialCheckSetCoverCertificateAdmissible(x.1)+PolynomialVerifySetCoverCore(x.0), 39, 4, (n,size));
  polynomial_verify_set_cover_bound();
  apply_polynomial_bound<nat>((x:nat) => true, (x:nat) => x, PolynomialVerifySetCover, 63, 4, n);
  if (size <= PolynomialSetCoverCertificateSize(n)) {
    nonnegative_product_monotonic(size, 2*size+4,
      PolynomialSetCoverCertificateSize(n), 2*PolynomialSetCoverCertificateSize(n)+4);
  }
}


// ABSENCE OF FALSE POSITIVES

// Main verification method for Set Cover.
// Demonstrates that no admissable certificate accepts a negative instance.
// Additionally, bounds the operation counter by the composed cost budget.

// Together with SetCoverHasShortCertificate, this contract establishes the
// NP certificate characterization in the abstract collection/atomic-label cost model.
// Complete verifier on initialized candidates, including incorrect and oversized ones.
// The total Cost budget covers both phases. cost_verify_set_cover_is_polynomial
// separately proves the general and short-candidate polynomial bounds.
method VerifySetCover(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>) returns (accepted:bool, ghost counter:nat)
  requires U.Init() && S.Init() && certificate.Init()
  requires SetCoverValidInstance(U.Model(), S.Model())
  ensures accepted == SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model())
  ensures accepted ==> SetCover(U.Model(), S.Model(), k)
  ensures counter <= CostVerifySetCover(U, S, k, certificate)
{
  var admissible:bool;
  admissible, counter := CheckSetCoverCertificateAdmissible(U, S, certificate);
  if (admissible) {
    ghost var checking:nat;
    accepted, checking := VerifySetCoverCore(U, S, k, certificate);
    counter := counter + checking;
  } else {
    accepted := false;
    if (SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model())) {
      set_cover_certificate_size_bound(U.Model(), S.Model(), k, certificate.Model());
      assert false;
    }
  }
}


// Check only structural admissibility; neither coverage nor membership in S is assumed.
// Initialization is a representation invariant of the supplied collection, as for U and S.
method CheckSetCoverCertificateAdmissible(U:Set<int>, S:SetSet<int>, certificate:SetSet<int>) returns (admissible:bool, ghost counter:nat)
  // Types in
  requires U.Init() && S.Init() && certificate.Init()
  // Invariant out
  ensures admissible == (certificate.Cardinality() <= S.Cardinality() &&
    forall member | member in certificate.Model() :: |member| <= U.Cardinality())
  ensures admissible ==> certificate.USize1() <= U.USize()
  ensures admissible ==> (certificate.Cardinality() + certificate.Size() + 1 <=
    PolynomialSetCoverCertificateSize(U.Cardinality() + S.Cardinality() + 1))
  // Counter
  ensures counter <= CostCheckSetCoverCertificateAdmissible(certificate)
{
  var count:nat;
  var limit:nat;
  var width:nat;
  count, counter := certificate.Count(0);
  limit, counter := S.Count(counter);
  width, counter := U.Count(counter);
  if (count > limit) {
    admissible := false;
    return;
  }
  var remaining:SetSet<int> := certificate;
  var empty:bool;
  empty, counter := remaining.IsEmpty(counter);
  admissible := true;
  ghost var base := 3*certificate.CostCount() + certificate.CostIsEmpty();
  ghost var step := certificate.UCostPick() + certificate.CostCount() +
    certificate.UCostRemove() + certificate.CostIsEmpty();
  linear_loop_budget_zero(base, step);
  while (!empty && admissible)
    // Termination
    decreases remaining.Cardinality()
    // Types
    invariant remaining.UniverseWithin(certificate)
    invariant remaining.Universe() == certificate.Universe()
    // Regular invariants
    invariant empty == (remaining.Model() == {})
    invariant admissible == (forall member | member in certificate.Model() - remaining.Model() :: |member| <= width)
    // Counter
    invariant counter <= LinearLoopBudget(base, step, certificate.Cardinality() - remaining.Cardinality())
  {
    linear_loop_budget_step(base, step, certificate.Cardinality() - remaining.Cardinality());
    remaining.universe_within_bound(certificate);
    var member:Set<int>;
    member, counter := remaining.Pick(counter);
    var memberSize:nat;
    memberSize, counter := member.Count(counter);
    admissible := memberSize <= width;
    remaining, counter := remaining.Remove(member, counter);
    empty, counter := remaining.IsEmpty(counter);
  }
  linear_loop_budget_bound(base, step, certificate.Cardinality() - remaining.Cardinality(), certificate.Cardinality());
  if (admissible) {
    certificate.u_cardinality1_bound(U.Cardinality());
    ghost var n := U.Cardinality() + S.Cardinality() + 1;
    certificate.u_size_bound(n, n);
  }
}


// Verify coverage and cardinality after the public entry establishes admissibility.
method VerifySetCoverCore(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>) returns (accepted:bool, ghost counter:nat)
  // Types in
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires U.Init() && S.Init() && certificate.Init()
  requires certificate.USize1() <= U.USize()
  requires certificate.Cardinality() <= S.Cardinality()
  // Invariant out
  ensures accepted == SetCoverCertificate(U.Model(), S.Model(), k, certificate.Model())
  ensures accepted ==> SetCover(U.Model(), S.Model(), k)
  // Counter
  ensures counter <= CostVerifySetCoverCore(U, S, k, certificate)
{
  counter := 0;
  var certificateCardinality:nat;
  certificateCardinality, counter := certificate.Count(counter);
  if (k < certificateCardinality) {
    return false, counter;
  }
  var isSubset:bool;
  isSubset, counter := IsSubset(certificate, S, counter);
  if (!isSubset) {
    return false, counter;
  }
  var remainingUniverse:Set<int>;
  remainingUniverse := U;
  accepted := true;
  var remainingUniverseEmpty:bool;
  remainingUniverseEmpty, counter := remainingUniverse.IsEmpty(counter);
  
  ghost var loopBase := certificate.CostCount() + CostIsSubset(certificate, S) +
    U.CostIsEmpty();
  linear_loop_budget_zero(loopBase, CostCheckUniverseElement(U, S, k, certificate));
  while (!remainingUniverseEmpty && accepted)
    // Termination
    decreases remainingUniverse.Cardinality()
    invariant remainingUniverseEmpty == (remainingUniverse.Model() == {})
    // Types
    invariant remainingUniverse.UniverseWithin(U)
    invariant certificate.Valid()
    invariant S.Valid()
    invariant certificate.Model() <= S.Model()
    invariant certificate.Cardinality() <= S.Cardinality()
    invariant certificate.USize1() <= U.USize()
    invariant remainingUniverse.Valid()
    // Regular invariants
    invariant accepted == IsCover(U.Model() - remainingUniverse.Model() , certificate.Model())
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, CostCheckUniverseElement(U, S, k, certificate),
      U.Cardinality() - remainingUniverse.Cardinality())
  {
    linear_loop_budget_step(loopBase, CostCheckUniverseElement(U, S, k, certificate), U.Cardinality() - remainingUniverse.Cardinality());
    accepted, remainingUniverse, remainingUniverseEmpty, counter := CheckUniverseElement(U, S, k, certificate, remainingUniverse, counter);
  }
  assert accepted ==> U.Model() - remainingUniverse.Model() == U.Model();
  linear_loop_budget_bound(loopBase, CostCheckUniverseElement(U, S, k, certificate), U.Cardinality() - remainingUniverse.Cardinality(), U.UCardinality());
}


method IsSubset(S1:SetSet<int>, S2:SetSet<int>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
  // Types in
  requires S1.Init() && S2.Valid()
  // Invariant out
  ensures b == (S1.Model() <= S2.Model())
  // Counter
  ensures counter <= counter_in + CostIsSubset(S1, S2)
{
  counter := counter_in;
  b := true;
  var S1':SetSet<int>;
  S1' := S1;
  var S1'_empty:bool;
  S1'_empty, counter := S1'.IsEmpty(counter);
  
  ghost var loopBase := counter_in + S1.CostIsEmpty();
  linear_loop_budget_zero(loopBase, CostIsSubsetStep(S1, S2));
  while (!S1'_empty)
  // Termination
  decreases S1'.Cardinality()
  invariant S1'_empty == (S1'.Model() == {})
  // Types
  invariant S1'.Valid()
  invariant S1'.UniverseWithin(S1)
  // Regular invariants
  invariant b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Counter
  invariant counter <= LinearLoopBudget(loopBase, CostIsSubsetStep(S1, S2),
    S1.Cardinality() - S1'.Cardinality())
  {
    linear_loop_budget_step(loopBase, CostIsSubsetStep(S1, S2), S1.Cardinality() - S1'.Cardinality());
    S1', S1'_empty, b, counter := IsSubsetStep(S1, S2, S1', counter, b);
  }
  linear_loop_budget_bound(loopBase, CostIsSubsetStep(S1, S2), S1.Cardinality() - S1'.Cardinality(), S1.UCardinality());
}


method IsSubsetStep(S1:SetSet<int>, S2:SetSet<int>, S1':SetSet<int>, ghost counter_in:nat, b:bool) returns (S1'':SetSet<int>, S1'_empty:bool, b':bool, ghost counter:nat)
  requires S1'.Model() != {}
  requires S1'.UniverseWithin(S1)
  requires S2.Valid()
  requires b == ((S1.Model() - S1'.Model()) <= S2.Model())
  ensures S1''.Cardinality() == S1'.Cardinality() - 1
  ensures S1'_empty == (S1''.Model() == {})
  ensures S1''.Valid()
  ensures S1''.UniverseWithin(S1)
  ensures b' == ((S1.Model() - S1''.Model()) <= S2.Model())
  ensures counter <= counter_in + CostIsSubsetStep(S1, S2)
{
  S1'.universe_within_bound(S1);

  counter := counter_in;
  var s:Set<int>;
  s, counter := S1'.Pick(counter);

  var s_in_S2:bool;
  s_in_S2, counter := S2.Contains(s, counter);
  b' := b && s_in_S2;

  S1'', counter := S1'.Remove(s, counter);
  S1'_empty, counter := S1''.IsEmpty(counter);
}


method CheckUniverseElement(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>, remainingUniverse:Set<int>, ghost counter_in:nat) returns (covered:bool, remainingUniverseOut:Set<int>, remainingUniverseOutEmpty:bool, ghost counter:nat)
  // Termination in
  requires remainingUniverse.Model() != {}
  // Types in
  requires U.Valid()
  requires remainingUniverse.Valid()
  requires S.Valid()
  requires certificate.Init()
  requires remainingUniverse.UniverseWithin(U)
  requires certificate.Model() <= S.Model()
  requires certificate.Cardinality() <= S.Cardinality()
  requires certificate.USize1() <= U.USize()
  // Invariant in
  requires IsCover(U.Model() - remainingUniverse.Model(), certificate.Model())
  // Termination out
  ensures remainingUniverseOut.Cardinality() == remainingUniverse.Cardinality() - 1
  ensures remainingUniverseOutEmpty == (remainingUniverseOut.Model() == {})
  // Types out
  ensures remainingUniverseOut.Valid()
  ensures remainingUniverseOut.UniverseWithin(U)
  // Invariant out
  ensures covered == IsCover(U.Model() - remainingUniverseOut.Model(), certificate.Model())
  // Counter
  ensures counter <= counter_in + CostCheckUniverseElement(U, S, k, certificate)
{
  remainingUniverse.universe_within_bound(U);
  counter := counter_in;
  var u:int;
  u, counter := remainingUniverse.Pick(counter);
  remainingUniverseOut, counter := remainingUniverse.Remove(u, counter);

  var remainingCertificate:SetSet<int>;
  remainingCertificate := certificate;

  var elementCovered:bool := false;
  var remainingCertificateEmpty:bool;
  remainingCertificateEmpty, counter := remainingCertificate.IsEmpty(counter);
  assert counter <= counter_in + U.CostPick() + U.UCostRemove() +
                               certificate.CostIsEmpty();
  
  while (!remainingCertificateEmpty && !elementCovered)
    // Termination
    decreases remainingCertificate.Cardinality()
    invariant remainingCertificateEmpty == (remainingCertificate.Model() == {})
    // Types
    invariant remainingCertificate.Valid()
    invariant remainingCertificate.UniverseWithin(certificate)
    invariant certificate.Init()
    invariant S.Valid()
    invariant certificate.Cardinality() <= S.Cardinality()
    invariant certificate.USize1() <= U.USize()
    // Regular invariants
    invariant elementCovered == (exists i' | i' in certificate.Model() - remainingCertificate.Model() :: u in i')
    // Counter
    invariant counter <= counter_in + U.CostPick() + U.UCostRemove() +
                         certificate.CostIsEmpty() +
                         (certificate.Cardinality()-remainingCertificate.Cardinality())*
                           CostCheckCoverSet(U, S, k, certificate)
  {
    elementCovered, remainingCertificate, remainingCertificateEmpty, counter := CheckCoverSet(U, S, k, certificate, remainingCertificate, u, counter);
  }
  covered := elementCovered;

  remainingUniverseOutEmpty, counter := remainingUniverseOut.IsEmpty(counter);

  assert U.Model() - remainingUniverseOut.Model() == U.Model() - remainingUniverse.Model() + {u};
  assert counter <= counter_in + U.CostPick() + U.UCostRemove() +
                       certificate.CostIsEmpty() +
                       certificate.Cardinality()*CostCheckCoverSet(U, S, k, certificate) +
                       U.CostIsEmpty();
  nonnegative_product_monotonic(certificate.Cardinality(),
                       CostCheckCoverSet(U, S, k, certificate),
                       certificate.UCardinality(),
                       CostCheckCoverSet(U, S, k, certificate));
}


method CheckCoverSet(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>, remainingCertificate:SetSet<int>, u:int, ghost counter_in:nat) returns (elementCovered:bool, remainingCertificateOut:SetSet<int>, remainingCertificateOutEmpty:bool, ghost counter:nat)
  requires remainingCertificate.Model() != {}
  requires U.Valid()
  requires S.Valid()
  requires certificate.Valid()
  requires remainingCertificate.UniverseWithin(certificate)
  requires certificate.Cardinality() <= S.Cardinality()
  requires certificate.USize1() <= U.USize()
  requires !(exists i' | i' in certificate.Model() - remainingCertificate.Model() :: u in i')
  ensures remainingCertificateOut.Cardinality() == remainingCertificate.Cardinality() - 1
  ensures remainingCertificateOutEmpty == (remainingCertificateOut.Model() == {})
  ensures remainingCertificateOut.Valid()
  ensures remainingCertificateOut.UniverseWithin(certificate)
  ensures elementCovered == (exists i' | i' in certificate.Model() - remainingCertificateOut.Model() :: u in i')
  ensures counter <= counter_in + CostCheckCoverSet(U, S, k, certificate)
{
  remainingCertificate.universe_within_bound(certificate);
  counter := counter_in;
  var i:Set<int>;
  i, counter := remainingCertificate.Pick(counter);
  elementCovered, counter := i.Contains(u, counter);
  remainingCertificateOut, counter := remainingCertificate.Remove(i, counter);
  remainingCertificateOutEmpty, counter := remainingCertificateOut.IsEmpty(counter);
}


// Charge the core only when its certificate cardinality and width bounds hold.
ghost function CostVerifySetCover(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>):nat
  requires U.Valid() && S.Valid() && certificate.Valid()
{
  CostCheckSetCoverCertificateAdmissible(certificate) +
    (if certificate.Cardinality() <= S.Cardinality() && certificate.USize1() <= U.USize()
     then CostVerifySetCoverCore(U, S, k, certificate) else 0)
}


// The counter uses the existing trait costs, including a potentially oversized member.
ghost function CostCheckSetCoverCertificateAdmissible(certificate:SetSet<int>):nat
{
  3*certificate.CostCount() + certificate.CostIsEmpty() + certificate.Cardinality()*
    (certificate.UCostPick() + certificate.CostCount() + certificate.UCostRemove() + certificate.CostIsEmpty())
}


ghost function CostVerifySetCoverCore(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>) : (o:nat)
  requires U.Valid()
  requires S.Valid()
  requires certificate.Valid()
  ensures 1 <= o
{
  certificate.CostCount() + CostIsSubset(certificate, S) +
  U.CostIsEmpty() +
  U.UCardinality()*CostCheckUniverseElement(U, S, k, certificate)
}


ghost function CostIsSubset(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  S1.CostIsEmpty() +
  S1.UCardinality()*CostIsSubsetStep(S1, S2)
}


ghost function CostIsSubsetStep(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  S1.UCostPick() + S2.UCostContains() +
  S1.UCostRemove() + S1.CostIsEmpty()
}


ghost function CostCheckUniverseElement(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>) : (o:nat)
{
  U.CostPick() + U.UCostRemove() +
  certificate.CostIsEmpty() +
  certificate.UCardinality()*CostCheckCoverSet(U, S, k, certificate) +
  U.CostIsEmpty()
}


ghost function CostCheckCoverSet(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>) : (o:nat)
{
  certificate.UCostPick() +
  U.UCostContains() +
  certificate.UCostRemove() +
  certificate.CostIsEmpty()
}


ghost function PolynomialVerifySetCover(n:nat):nat
{
  PolynomialCheckSetCoverCertificateAdmissible(PolynomialSetCoverCertificateSize(n)) + PolynomialVerifySetCoverCore(n)
}


ghost function PolynomialCheckSetCoverCertificateAdmissible(size:nat):nat
{ 4 + size*(2*size+4) }


// Fixed polynomial in the instance measure n = |U| + |S| + 1.
ghost function PolynomialVerifySetCoverCore(n:nat):nat
{
  2 + (n*n + 2) + n*(2*n*n + n + 4) + n + 2 +
  n*(n + 4 + n*n + n*(n*n + 2*n + 5))
}


lemma cost_check_set_cover_certificate_admissible_to_polynomial(certificate:SetSet<int>)
  requires certificate.Init()
  ensures CostCheckSetCoverCertificateAdmissible(certificate) <=
    PolynomialCheckSetCoverCertificateAdmissible(certificate.Cardinality() + certificate.Size() + 1)
{
  if (certificate.Cardinality() != 0) {
    nonnegative_product_monotonic(1, certificate.Cardinality1(), certificate.Cardinality(), certificate.Cardinality1());
  }
  assert certificate.Cardinality1() <= certificate.Size();
  reveal certificate.UCardinality1();
  var size := certificate.Cardinality() + certificate.Size() + 1;
  nonnegative_product_monotonic(certificate.Cardinality(),
    certificate.UCostPick() + certificate.CostCount() + certificate.UCostRemove() + certificate.CostIsEmpty(),
    size, 2*size+4);
}


lemma {:isolate_assertions} cost_verify_set_cover_core_to_polynomial(U:Set<int>, S:SetSet<int>, k:nat, certificate:SetSet<int>)
  requires U.Init() && S.Init() && certificate.Init()
  requires S.USize1() <= U.USize()
  requires certificate.USize1() <= U.USize()
  requires certificate.Cardinality() <= S.Cardinality()
  ensures CostVerifySetCoverCore(U, S, k, certificate) <= PolynomialVerifySetCoverCore(|U.Model()| + |S.Model()| + 1)
{
  var n := |U.Model()| + |S.Model()| + 1;
  certificate.u_size_bound(n, n);
  S.u_size_bound(n, n);
  assert n*n + n*n == 2*n*n by { multiplication_associative(2, n, n); }
  assert CostIsSubsetStep(certificate, S) <= 2*n*n + n + 4;
  nonnegative_product_monotonic(certificate.UCardinality(), CostIsSubsetStep(certificate, S), n, 2*n*n + n + 4);
  assert CostIsSubset(certificate, S) <= n*n + 2 + n*(2*n*n + n + 4);
  assert CostCheckCoverSet(U, S, k, certificate) <= n*n + 2*n + 5;
  nonnegative_product_monotonic(certificate.UCardinality(), CostCheckCoverSet(U, S, k, certificate),
                       n, n*n + 2*n + 5);
  assert CostCheckUniverseElement(U, S, k, certificate) <= n + 4 + n*n + n*(n*n + 2*n + 5);
  nonnegative_product_monotonic(U.UCardinality(), CostCheckUniverseElement(U, S, k, certificate),
                       n, n + 4 + n*n + n*(n*n + 2*n + 5));
}
