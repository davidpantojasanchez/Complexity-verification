include "../Problems/SetCover.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"


// Native variant of the admissible-certificate core.
method {:isolate_assertions} VerifySetCoverCore_simple<T(==)>(instance:SetCoverModel<T>, certificate:set<set<T>>) returns (accepted:bool, ghost counter:nat)
  requires SetCoverValidInstance(instance)
  requires |certificate| <= |instance.sets|
  requires (forall s | s in certificate :: |s| <= |instance.universe|)
  ensures accepted == SetCoverCertificate(instance, certificate)
  ensures accepted ==> SetCover(instance)
  ensures counter <= BudgetVerifySetCoverCore_simple(instance.universe, instance.sets, instance.k)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  assert forall i | i in certificate :: |i| <= |U|;
  counter := 0;
  var remainingUniverse := U; counter := counter + |U|;
  accepted:= true;
  counter := counter + 1;
  if (k < |certificate|) {
    return false, counter;
  }
  var isSubset:bool;
  isSubset, counter := IsSubset_simple(U, certificate, S, counter);

  if (!isSubset) {
    assert counter <= |U| + 1 + BudgetIsSubset_simple(U, certificate, S);
    budget_verify_set_cover_core_bound_simple(U, S, k, certificate);
    assert counter <= BudgetVerifySetCoverCore_simple(U, S, k);
    return false, counter;
  }
  while (remainingUniverse != {} && accepted)
    decreases |remainingUniverse|
    invariant remainingUniverse <= U 
    invariant accepted == IsCover(U-remainingUniverse,certificate)
    invariant counter <= |U| + BudgetIsSubset_simple(U, certificate, S) + 1 + (|U| - |remainingUniverse|)*(BudgetCheckUniverseElement_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    accepted, remainingUniverse, counter := CheckUniverseElement_simple(U, S, k, certificate, remainingUniverse, counter);
  }
  counter := counter + 1;
  assert counter <= |U| + BudgetIsSubset_simple(U, certificate, S) + 2 + |U|*(BudgetCheckUniverseElement_simple(U, S, k) + 1) by {
    var stepBudget := BudgetCheckUniverseElement_simple(U, S, k) + 1;
    subset_cardinality_bound_set(remainingUniverse, U);
    nonnegative_product_monotonic(|U|-|remainingUniverse|, stepBudget, |U|, stepBudget);
  }
  budget_verify_set_cover_core_bound_simple(U, S, k, certificate);
  assert accepted ==> U-remainingUniverse == U;
  assert accepted ==> SetCoverCertificate(instance, certificate);
}


method IsSubset_simple<T(==)>(U:set<T>, S1:set<set<T>>, S2:set<set<T>>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
  requires forall s |s in S2 :: s <= U
  ensures b == (S1 <= S2)
  ensures counter <= counter_in + BudgetIsSubset_simple(U, S1, S2)
{
  counter := counter_in;
  b := true;
  var S1':= S1; counter := counter + |U|*|S1|;
  while (S1' != {})
    decreases |S1'|
    invariant S1' <= S1
    invariant b == ((S1 - S1') <= S2)
    invariant counter <= counter_in + |S1|*|U| + 1 + (|S1| - |S1'|)*(BudgetIsSubsetStep_simple(U, S1, S2) + 1)
  {
    counter := counter + 1;
    S1', b, counter := IsSubsetStep_simple(U, S1, S2, S1', counter, b);
  }
  counter := counter + 1;
}


method IsSubsetStep_simple<T(==)>(U:set<T>, S1:set<set<T>>, S2:set<set<T>>, S1':set<set<T>>, ghost counter_in:nat, b:bool) returns (S1'':set<set<T>>, b':bool, ghost counter:nat)
  requires S1' != {}
  requires S1' <= S1
  requires b == ((S1 - S1') <= S2)
  ensures |S1''| == |S1'| - 1
  ensures S1'' <= S1
  ensures b' == ((S1 - S1'') <= S2)
  ensures counter <= counter_in + BudgetIsSubsetStep_simple(U, S1, S2)
{
  counter := counter_in;
  subset_cardinality_bound_set(S1', S1);
  var s:set<T> :| s in S1'; counter := counter + |U|;
  b' := b && s in S2; counter := counter + |S2|*|U|;
  S1'' := S1' - {s}; counter := counter + |S1|*|U|;
}


method CheckUniverseElement_simple<T(==)>(U:set<T>, S:set<set<T>>, k:nat, certificate:set<set<T>>, remainingUniverse:set<T>, ghost counter_in:nat)
    returns (covered:bool, remainingUniverseOut:set<T>, ghost counter:nat)
  requires remainingUniverse != {}
  requires remainingUniverse <= U
  requires |certificate| <= |S|
  requires IsCover(U - remainingUniverse, certificate)
  ensures |remainingUniverseOut| == |remainingUniverse| - 1
  ensures remainingUniverseOut <= U
  ensures covered == IsCover(U - remainingUniverseOut, certificate)
  ensures counter <= counter_in + BudgetCheckUniverseElement_simple(U, S, k)
{
  counter := counter_in;
  var u :| u in remainingUniverse; counter := counter + 1;
  remainingUniverseOut := remainingUniverse - {u}; counter := counter + |U|;

  var remainingCertificate := certificate; counter := counter + |S|*|U|;
  covered:= false;
  while (remainingCertificate != {} && !covered)
    decreases |remainingCertificate|
    invariant remainingCertificate <= certificate
    invariant covered == (exists i' | i' in certificate - remainingCertificate :: u in i')
    invariant counter <= counter_in + |S|*|U| + |U| + 1 + (|certificate|-|remainingCertificate|)*(CostCheckCoverSet_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    covered, remainingCertificate, counter := CheckCoverSet_simple(U, S, k, certificate, remainingCertificate, u, counter);
  }
  counter := counter + 1;
  assert counter <= counter_in + |S|*|U| + |U| + 2 + (|certificate|-|remainingCertificate|)*(CostCheckCoverSet_simple(U, S, k) + 1);
  assert counter <= counter_in + |S|*|U| + |U| + 2 + (|S|)*(CostCheckCoverSet_simple(U, S, k) + 1);
  assert U - remainingUniverseOut == U - remainingUniverse + {u};
}


method CheckCoverSet_simple<T(==)>(U:set<T>, S:set<set<T>>, k:nat, certificate:set<set<T>>, remainingCertificate:set<set<T>>, u:T, ghost counter_in:nat)
    returns (elementCovered:bool, remainingCertificateOut:set<set<T>>, ghost counter:nat)
  requires remainingCertificate != {}
  requires remainingCertificate <= certificate
  requires !(exists i' | i' in certificate - remainingCertificate :: u in i')
  ensures |remainingCertificateOut| == |remainingCertificate| - 1
  ensures remainingCertificateOut <= certificate
  ensures elementCovered == (exists i' | i' in certificate - remainingCertificateOut :: u in i')
  ensures counter == counter_in + CostCheckCoverSet_simple(U, S, k)
{
  counter := counter_in;
  var i :| i in remainingCertificate; counter := counter + |U|;
  elementCovered := u in i; counter := counter + |U|;
  remainingCertificateOut := remainingCertificate - {i}; counter := counter + |S|*|U|;
}


ghost function BudgetIsSubsetStep_simple<T>(U: set<T>, S1:set<set<T>>, S2:set<set<T>>) : (o:nat)
{
  |S1|*|U| + |S2|*|U| + |U|
}
ghost function BudgetIsSubset_simple<T>(U: set<T>, S1:set<set<T>>, S2:set<set<T>>) : (o:nat)
{
  |S1|*|S1|*|U| + |S1|*|S2|*|U| + 2*|S1|*|U| + |S1| + 2
}
ghost function CostCheckCoverSet_simple<T>(U: set<T>, S: set<set<T>>, k: nat) : (o:nat) {
  |S|*|U| + 2*|U|
}
ghost function BudgetCheckUniverseElement_simple<T>(U: set<T>, S: set<set<T>>, k: nat) : (o:nat)
  ensures |S|*|U| + |U| + 2 + |S|*(CostCheckCoverSet_simple(U, S, k) + 1) == o
{
  |U|*|S|*|S| + 3*|U|*|S| + |U| + |S| + 2
}


ghost function BudgetVerifySetCoverCore_simple<T>(U: set<T>, S: set<set<T>>, k: nat) : (o:nat)
{
  
  |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4
}


lemma budget_verify_set_cover_core_bound_simple<T>(U: set<T>, S: set<set<T>>, k: nat, certificate: set<set<T>>)
  requires |certificate| <= |S|
  ensures |U| + BudgetIsSubset_simple(U, certificate, S) + 2 + |U|*(BudgetCheckUniverseElement_simple(U, S, k) + 1) <= BudgetVerifySetCoverCore_simple(U, S, k)
{
  calc <= {
    |U| + BudgetIsSubset_simple(U, certificate, S) + 2 + |U|*(BudgetCheckUniverseElement_simple(U, S, k) + 1);
    |U| + |certificate|*|certificate|*|U| + |certificate|*|S|*|U| + 2*|certificate|*|U| + |certificate| + |U|*(BudgetCheckUniverseElement_simple(U, S, k) + 1) + 4;
    |certificate|*|certificate|*|U| + |certificate|*|S|*|U| + 2*|certificate|*|U| + |certificate| + 2*|U| + 4 + |U|*BudgetCheckUniverseElement_simple(U, S, k);
    |certificate|*|certificate|*|U| + |certificate|*|S|*|U| + 2*|certificate|*|U| + |certificate| + 2*|U| + 4 + (|S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + 2*|U|);
    assert 2*|certificate|*|U| <= 2*|S|*|U| by {
      nonnegative_product_monotonic(|certificate|, 2*|U|, |S|, 2*|U|);
    }
    |certificate|*|certificate|*|U| + |certificate|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    assert |certificate|*|certificate|*|U| <= |certificate|*|S|*|U| by {
      nonnegative_product_monotonic(|certificate|, |certificate|*|U|, |S|, |certificate|*|U|);
      assert |certificate|*|certificate|*|U| <= |S|*|certificate|*|U|;
      assert |S|*|certificate|*|U| <= |certificate|*|S|*|U|;
    }
    |certificate|*|S|*|U| + |certificate|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    2*|certificate|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    assert |certificate|*|S|*|U| <= |S|*|S|*|U| by {
      nonnegative_product_monotonic(|certificate|, |S|*|U|, |S|, |S|*|U|);
    }
    2*|S|*|S|*|U| + 2*|S|*|U| + |S|*|S|*|U|*|U| + 3*|S|*|U|*|U| + |U|*|U| + |S|*|U| + |S| + 4*|U| + 4;
    |S|*|S|*|U|*|U| + 2*|S|*|S|*|U| + 3*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 4;
  }
}
