include "../Problems/SetCover.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Lemmas.dfy"


method verifySetCover(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) returns (accepted:bool, ghost counter:nat)
  // Types in
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires init_Set(U) && init_SetSet(S) && init_SetSet(I)
  requires S.UBSize1() <= U.UBSize0()
  requires I.UBSize1() <= U.UBSize0()
  requires I.Cardinality() <= S.Cardinality()
  // Invariant out
  ensures accepted == SetCoverCertificate(U.Model(), S.Model(), k, I.Model())
  ensures accepted ==> SetCover(U.Model(), S.Model(), k)
  // Counter
  ensures counter <= SetCoverVerificationPolynomial(|U.Model()| + |S.Model()| + 1)
{
  SetCoverVerificationCostBound(U, S, k, I);
  counter := 0;
  var I_cardinality:nat;
  I_cardinality, counter := I.nElements(counter);
  if (k < I_cardinality) {
    return false, counter;
  }
  var I_seq_S:bool;
  I_seq_S, counter := isSubset(I, S, counter);
  if (!I_seq_S) {
    return false, counter;
  }
  if_smaller_then_less_cardinality(I.Model(), S.Model());

  var U':Set<int>;
  U' := U;
  accepted := true;
  var U'_empty:bool;
  U'_empty, counter := U'.Empty(counter);
  
  ghost var loopBase := cost_SetSetNElements(I) + poly_isSubset(I, S) +
    cost_SetEmpty(U);
  LinearLoopBudgetZero(loopBase, poly_outer_loop(U, S, k, I));
  while (!U'_empty && accepted)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant in_universe_Set(U', U)
    invariant I.Valid()
    invariant S.Valid()
    invariant I.Model() <= S.Model()
    invariant I.Cardinality() <= S.Cardinality()
    invariant I.UBSize1() <= U.UBSize0()
    invariant U'.Valid()
    // Regular invariants
    invariant accepted == isCover(U.Model() - U'.Model() , I.Model())
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, poly_outer_loop(U, S, k, I),
      U.Cardinality() - U'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, poly_outer_loop(U, S, k, I), U.Cardinality() - U'.Cardinality());
    accepted, U', U'_empty, counter := verifySetCover_outer_loop(U, S, k, I, U', counter);
  }
  assert accepted ==> U.Model() - U'.Model() == U.Model();
  LinearLoopBudgetBound(loopBase, poly_outer_loop(U, S, k, I), U.Cardinality() - U'.Cardinality(), U.UBCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, poly_outer_loop(U, S, k, I), U.Cardinality() - U'.Cardinality()),
    loopBase + (U.UBCardinality())*(poly_outer_loop(U, S, k, I)), 0, poly(U, S, k, I));
}


method isSubset(S1:SetSet<int>, S2:SetSet<int>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
  // Types in
  requires init_SetSet(S1) && S2.Valid()
  // Invariant out
  ensures b == (S1.Model() <= S2.Model())
  // Counter
  ensures counter <= counter_in + poly_isSubset(S1, S2)
{
  counter := counter_in;
  b := true;
  var S1';
  S1' := S1;
  var S1'_empty:bool;
  S1'_empty, counter := S1'.Empty(counter);
  
  ghost var loopBase := counter_in + cost_SetSetEmpty(S1);
  LinearLoopBudgetZero(loopBase, poly_isSubset_loop(S1, S2));
  while (!S1'_empty)
  // Termination
  decreases S1'.Cardinality()
  invariant S1'_empty == (S1'.Model() == {})
  // Types
  invariant S1'.Valid()
  invariant in_universe_SetSet(S1', S1)
  // Regular invariants
  invariant b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Counter
  invariant counter <= LinearLoopBudget(loopBase, poly_isSubset_loop(S1, S2),
    S1.Cardinality() - S1'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, poly_isSubset_loop(S1, S2), S1.Cardinality() - S1'.Cardinality());
    S1', S1'_empty, b, counter := isSubset_loop(S1, S2, S1', counter, b);
  }
  LinearLoopBudgetBound(loopBase, poly_isSubset_loop(S1, S2), S1.Cardinality() - S1'.Cardinality(), S1.UBCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, poly_isSubset_loop(S1, S2), S1.Cardinality() - S1'.Cardinality()),
    loopBase + (S1.UBCardinality())*(poly_isSubset_loop(S1, S2)), 0, counter_in + poly_isSubset(S1, S2));
}


method isSubset_loop(S1:SetSet<int>, S2:SetSet<int>, S1':SetSet<int>, ghost counter_in:nat, b:bool) returns (S1'':SetSet<int>, S1'_empty:bool, b':bool, ghost counter:nat)
  requires S1'.Model() != {}
  requires in_universe_SetSet(S1', S1)
  requires S2.Valid()
  requires b == ((S1.Model() - S1'.Model()) <= S2.Model())
  ensures S1''.Cardinality() == S1'.Cardinality() - 1
  ensures S1'_empty == (S1''.Model() == {})
  ensures S1''.Valid()
  ensures in_universe_SetSet(S1'', S1)
  ensures b' == ((S1.Model() - S1''.Model()) <= S2.Model())
  ensures counter <= counter_in + poly_isSubset_loop(S1, S2)
{
  in_universe_lemma_SetSet(S1', S1);

  counter := counter_in;
  var s:Set<int>;
  s, counter := S1'.Pick(counter);

  var s_in_S2:bool;
  s_in_S2, counter := S2.Contains(s, counter);
  b' := b && s_in_S2;

  S1'', counter := S1'.Remove(s, counter);
  S1'_empty, counter := S1''.Empty(counter);
}


method verifySetCover_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, U':Set<int>, ghost counter_in:nat) returns (b1:bool, U'':Set<int>, U''_empty:bool, ghost counter:nat)
  // Termination in
  requires U'.Model() != {}
  // Types in
  requires U.Valid()
  requires U'.Valid()
  requires S.Valid()
  requires init_SetSet(I)
  requires in_universe_Set(U', U)
  requires I.Model() <= S.Model()
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.UBSize0()
  // Invariant in
  requires isCover(U.Model() - U'.Model(), I.Model())
  // Termination out
  ensures U''.Cardinality() == U'.Cardinality() - 1
  ensures U''_empty == (U''.Model() == {})
  // Types out
  ensures U''.Valid()
  ensures in_universe_Set(U'', U)
  // Invariant out
  ensures b1 == isCover(U.Model() - U''.Model(), I.Model())
  // Counter
  ensures counter <= counter_in + poly_outer_loop(U, S, k, I)
{
  in_universe_lemma_Set(U', U);
  counter := counter_in;
  var u:int;
  u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var I':SetSet<int>;
  I' := I;

  var b2:bool := false;
  var I'_empty:bool;
  I'_empty, counter := I'.Empty(counter);
  assert counter <= counter_in + cost_SetPick(U) + cost_SetRemoveUniverse(U) +
                               cost_SetSetEmpty(I);
  
  while (!I'_empty && !b2)
    // Termination
    decreases I'.Cardinality()
    invariant I'_empty == (I'.Model() == {})
    // Types
    invariant I'.Valid()
    invariant in_universe_SetSet(I', I)
    invariant init_SetSet(I)
    invariant S.Valid()
    invariant I.Cardinality() <= S.Cardinality()
    invariant I.UBSize1() <= U.UBSize0()
    // Regular invariants
    invariant b2 == (exists i' | i' in I.Model() - I'.Model() :: u in i')
    // Counter
    invariant counter <= counter_in + cost_SetPick(U) + cost_SetRemoveUniverse(U) +
                         cost_SetSetEmpty(I) +
                         (I.Cardinality()-I'.Cardinality())*
                           poly_inner_loop(U, S, k, I)
  {
    b2, I', I'_empty, counter := verifySetCover_inner_loop(U, S, k, I, I', u, counter);
  }
  b1 := b2;

  U''_empty, counter := U''.Empty(counter);

  assert U.Model() - U''.Model() == U.Model() - U'.Model() + {u};
  assert counter <= counter_in + cost_SetPick(U) + cost_SetRemoveUniverse(U) +
                       cost_SetSetEmpty(I) +
                       I.Cardinality()*poly_inner_loop(U, S, k, I) +
                       cost_SetEmpty(U);
  mult_preserves_order(I.Cardinality(),
                       poly_inner_loop(U, S, k, I),
                       I.UBCardinality(),
                       poly_inner_loop(U, S, k, I));
}


method verifySetCover_inner_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, I':SetSet<int>, u:int, ghost counter_in:nat) returns (b2:bool, I'':SetSet<int>, I''_empty:bool, ghost counter:nat)
  requires I'.Model() != {}
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  requires in_universe_SetSet(I', I)
  requires I.Cardinality() <= S.Cardinality()
  requires I.UBSize1() <= U.UBSize0()
  requires !(exists i' | i' in I.Model() - I'.Model() :: u in i')
  ensures I''.Cardinality() == I'.Cardinality() - 1
  ensures I''_empty == (I''.Model() == {})
  ensures I''.Valid()
  ensures in_universe_SetSet(I'', I)
  ensures b2 == (exists i' | i' in I.Model() - I''.Model() :: u in i')
  ensures counter <= counter_in + poly_inner_loop(U, S, k, I)
{
  in_universe_lemma_SetSet(I', I);
  counter := counter_in;
  var i:Set<int>;
  i, counter := I'.Pick(counter);
  b2, counter := i.Contains(u, counter);
  I'', counter := I'.Remove(i, counter);
  I''_empty, counter := I''.Empty(counter);
}


ghost function poly_inner_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
{
  cost_SetSetPickUniverse(I) +
  cost_SetContainsUniverse(U) +
  cost_SetSetRemoveUniverse(I) +
  cost_SetSetEmpty(I)
}
ghost function poly_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
{
  cost_SetPick(U) + cost_SetRemoveUniverse(U) +
  cost_SetSetEmpty(I) +
  I.UBCardinality()*poly_inner_loop(U, S, k, I) +
  cost_SetEmpty(U)
}
ghost function poly_isSubset_loop(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  cost_SetSetPickUniverse(S1) + cost_SetSetContainsUniverse(S2) +
  cost_SetSetRemoveUniverse(S1) + cost_SetSetEmpty(S1)
}
ghost function {:opaque} poly_isSubset(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
  ensures o == cost_SetSetEmpty(S1) +
               S1.UBCardinality()*poly_isSubset_loop(S1, S2)
{
  cost_SetSetEmpty(S1) +
  S1.UBCardinality()*poly_isSubset_loop(S1, S2)
}


ghost function poly(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  ensures 1 <= o
{
  cost_SetSetNElements(I) + poly_isSubset(I, S) +
  cost_SetEmpty(U) +
  U.UBCardinality()*poly_outer_loop(U, S, k, I)
}


// Fixed polynomial in the instance measure n = |U| + |S| + 1.
ghost function SetCoverVerificationPolynomial(n:nat):nat
{
  2 + (n*n + 2) + n*(2*n*n + n + 4) + n + 2 +
  n*(n + 4 + n*n + n*(n*n + 2*n + 5))
}

lemma {:isolate_assertions} SetCoverVerificationCostBound(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>)
  requires init_Set(U) && init_SetSet(S) && init_SetSet(I)
  requires S.UBSize1() <= U.UBSize0()
  requires I.UBSize1() <= U.UBSize0()
  requires I.Cardinality() <= S.Cardinality()
  ensures poly(U, S, k, I) <= SetCoverVerificationPolynomial(|U.Model()| + |S.Model()| + 1)
{
  var n := |U.Model()| + |S.Model()| + 1;
  SetSetUniverseSizeBound(I, n, n);
  SetSetUniverseSizeBound(S, n, n);
  assert n*n + n*n == 2*n*n by { associativity(2, n, n); }
  assert poly_isSubset_loop(I, S) <= 2*n*n + n + 4;
  mult_preserves_order(I.UBCardinality(), poly_isSubset_loop(I, S), n, 2*n*n + n + 4);
  assert poly_isSubset(I, S) <= n*n + 2 + n*(2*n*n + n + 4);
  assert poly_inner_loop(U, S, k, I) <= n*n + 2*n + 5;
  mult_preserves_order(I.UBCardinality(), poly_inner_loop(U, S, k, I),
                       n, n*n + 2*n + 5);
  assert poly_outer_loop(U, S, k, I) <= n + 4 + n*n + n*(n*n + 2*n + 5);
  mult_preserves_order(U.UBCardinality(), poly_outer_loop(U, S, k, I),
                       n, n + 4 + n*n + n*(n*n + 2*n + 5));
}
