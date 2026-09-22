include "../Problems/SetCover.dfy"
include "../Auxiliary/Set.dfy"
include "../Auxiliary/Lemmas.dfy"


method VerifySetCover(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) returns (accepted:bool, ghost counter:nat)
  // Types in
  requires SetCoverValidInstance(U.Model(), S.Model())
  requires Init_Set(U) && Init_SetSet(S) && Init_SetSet(I)
  requires I.USize1() <= U.USize0()
  requires I.Cardinality() <= S.Cardinality()
  // Invariant out
  ensures accepted == SetCoverCertificate(U.Model(), S.Model(), k, I.Model())
  ensures accepted ==> SetCover(U.Model(), S.Model(), k)
  // Counter
  ensures counter <= PolySetCoverVerification(|U.Model()| + |S.Model()| + 1)
{
  assert {:split_here} S.USize1() <= U.USize0() by {
    UniverseSubsetSizeBound_SetSet(S, U.Model());
  }
  CostSetCoverVerificationBound(U, S, k, I);
  counter := 0;
  var I_cardinality:nat;
  I_cardinality, counter := I.Count(counter);
  if (k < I_cardinality) {
    return false, counter;
  }
  var I_seq_S:bool;
  I_seq_S, counter := IsSubset(I, S, counter);
  if (!I_seq_S) {
    return false, counter;
  }
  SubsetCardinalityBound(I.Model(), S.Model());

  var U':Set<int>;
  U' := U;
  accepted := true;
  var U'_empty:bool;
  U'_empty, counter := U'.IsEmpty(counter);
  
  ghost var loopBase := CostCount_SetSet(I) + PolyIsSubset(I, S) +
    CostIsEmpty_Set(U);
  LinearLoopBudgetZero(loopBase, PolyCheckUniverseElement(U, S, k, I));
  while (!U'_empty && accepted)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant InUniverse_Set(U', U)
    invariant I.Valid()
    invariant S.Valid()
    invariant I.Model() <= S.Model()
    invariant I.Cardinality() <= S.Cardinality()
    invariant I.USize1() <= U.USize0()
    invariant U'.Valid()
    // Regular invariants
    invariant accepted == IsCover(U.Model() - U'.Model() , I.Model())
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, PolyCheckUniverseElement(U, S, k, I),
      U.Cardinality() - U'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, PolyCheckUniverseElement(U, S, k, I), U.Cardinality() - U'.Cardinality());
    accepted, U', U'_empty, counter := CheckUniverseElement(U, S, k, I, U', counter);
  }
  assert accepted ==> U.Model() - U'.Model() == U.Model();
  LinearLoopBudgetBound(loopBase, PolyCheckUniverseElement(U, S, k, I), U.Cardinality() - U'.Cardinality(), U.UCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, PolyCheckUniverseElement(U, S, k, I), U.Cardinality() - U'.Cardinality()),
    loopBase + (U.UCardinality())*(PolyCheckUniverseElement(U, S, k, I)), 0, PolyVerifySetCover(U, S, k, I));
}


method IsSubset(S1:SetSet<int>, S2:SetSet<int>, ghost counter_in:nat) returns (b:bool, ghost counter:nat)
  // Types in
  requires Init_SetSet(S1) && S2.Valid()
  // Invariant out
  ensures b == (S1.Model() <= S2.Model())
  // Counter
  ensures counter <= counter_in + PolyIsSubset(S1, S2)
{
  counter := counter_in;
  b := true;
  var S1';
  S1' := S1;
  var S1'_empty:bool;
  S1'_empty, counter := S1'.IsEmpty(counter);
  
  ghost var loopBase := counter_in + CostIsEmpty_SetSet(S1);
  LinearLoopBudgetZero(loopBase, PolyIsSubsetStep(S1, S2));
  while (!S1'_empty)
  // Termination
  decreases S1'.Cardinality()
  invariant S1'_empty == (S1'.Model() == {})
  // Types
  invariant S1'.Valid()
  invariant InUniverse_SetSet(S1', S1)
  // Regular invariants
  invariant b == ((S1.Model() - S1'.Model()) <= S2.Model())
  // Counter
  invariant counter <= LinearLoopBudget(loopBase, PolyIsSubsetStep(S1, S2),
    S1.Cardinality() - S1'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, PolyIsSubsetStep(S1, S2), S1.Cardinality() - S1'.Cardinality());
    S1', S1'_empty, b, counter := IsSubsetStep(S1, S2, S1', counter, b);
  }
  LinearLoopBudgetBound(loopBase, PolyIsSubsetStep(S1, S2), S1.Cardinality() - S1'.Cardinality(), S1.UCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, PolyIsSubsetStep(S1, S2), S1.Cardinality() - S1'.Cardinality()),
    loopBase + (S1.UCardinality())*(PolyIsSubsetStep(S1, S2)), 0, counter_in + PolyIsSubset(S1, S2));
}


method IsSubsetStep(S1:SetSet<int>, S2:SetSet<int>, S1':SetSet<int>, ghost counter_in:nat, b:bool) returns (S1'':SetSet<int>, S1'_empty:bool, b':bool, ghost counter:nat)
  requires S1'.Model() != {}
  requires InUniverse_SetSet(S1', S1)
  requires S2.Valid()
  requires b == ((S1.Model() - S1'.Model()) <= S2.Model())
  ensures S1''.Cardinality() == S1'.Cardinality() - 1
  ensures S1'_empty == (S1''.Model() == {})
  ensures S1''.Valid()
  ensures InUniverse_SetSet(S1'', S1)
  ensures b' == ((S1.Model() - S1''.Model()) <= S2.Model())
  ensures counter <= counter_in + PolyIsSubsetStep(S1, S2)
{
  InUniverseBounds_SetSet(S1', S1);

  counter := counter_in;
  var s:Set<int>;
  s, counter := S1'.Pick(counter);

  var s_in_S2:bool;
  s_in_S2, counter := S2.Contains(s, counter);
  b' := b && s_in_S2;

  S1'', counter := S1'.Remove(s, counter);
  S1'_empty, counter := S1''.IsEmpty(counter);
}


method CheckUniverseElement(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, U':Set<int>, ghost counter_in:nat) returns (b1:bool, U'':Set<int>, U''_empty:bool, ghost counter:nat)
  // Termination in
  requires U'.Model() != {}
  // Types in
  requires U.Valid()
  requires U'.Valid()
  requires S.Valid()
  requires Init_SetSet(I)
  requires InUniverse_Set(U', U)
  requires I.Model() <= S.Model()
  requires I.Cardinality() <= S.Cardinality()
  requires I.USize1() <= U.USize0()
  // Invariant in
  requires IsCover(U.Model() - U'.Model(), I.Model())
  // Termination out
  ensures U''.Cardinality() == U'.Cardinality() - 1
  ensures U''_empty == (U''.Model() == {})
  // Types out
  ensures U''.Valid()
  ensures InUniverse_Set(U'', U)
  // Invariant out
  ensures b1 == IsCover(U.Model() - U''.Model(), I.Model())
  // Counter
  ensures counter <= counter_in + PolyCheckUniverseElement(U, S, k, I)
{
  InUniverseBounds_Set(U', U);
  counter := counter_in;
  var u:int;
  u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var I':SetSet<int>;
  I' := I;

  var b2:bool := false;
  var I'_empty:bool;
  I'_empty, counter := I'.IsEmpty(counter);
  assert counter <= counter_in + CostPick_Set(U) + UCostRemove_Set(U) +
                               CostIsEmpty_SetSet(I);
  
  while (!I'_empty && !b2)
    // Termination
    decreases I'.Cardinality()
    invariant I'_empty == (I'.Model() == {})
    // Types
    invariant I'.Valid()
    invariant InUniverse_SetSet(I', I)
    invariant Init_SetSet(I)
    invariant S.Valid()
    invariant I.Cardinality() <= S.Cardinality()
    invariant I.USize1() <= U.USize0()
    // Regular invariants
    invariant b2 == (exists i' | i' in I.Model() - I'.Model() :: u in i')
    // Counter
    invariant counter <= counter_in + CostPick_Set(U) + UCostRemove_Set(U) +
                         CostIsEmpty_SetSet(I) +
                         (I.Cardinality()-I'.Cardinality())*
                           PolyCheckCoverSet(U, S, k, I)
  {
    b2, I', I'_empty, counter := CheckCoverSet(U, S, k, I, I', u, counter);
  }
  b1 := b2;

  U''_empty, counter := U''.IsEmpty(counter);

  assert U.Model() - U''.Model() == U.Model() - U'.Model() + {u};
  assert counter <= counter_in + CostPick_Set(U) + UCostRemove_Set(U) +
                       CostIsEmpty_SetSet(I) +
                       I.Cardinality()*PolyCheckCoverSet(U, S, k, I) +
                       CostIsEmpty_Set(U);
  MultiplicationPreservesOrder(I.Cardinality(),
                       PolyCheckCoverSet(U, S, k, I),
                       I.UCardinality(),
                       PolyCheckCoverSet(U, S, k, I));
}


method CheckCoverSet(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>, I':SetSet<int>, u:int, ghost counter_in:nat) returns (b2:bool, I'':SetSet<int>, I''_empty:bool, ghost counter:nat)
  requires I'.Model() != {}
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  requires InUniverse_SetSet(I', I)
  requires I.Cardinality() <= S.Cardinality()
  requires I.USize1() <= U.USize0()
  requires !(exists i' | i' in I.Model() - I'.Model() :: u in i')
  ensures I''.Cardinality() == I'.Cardinality() - 1
  ensures I''_empty == (I''.Model() == {})
  ensures I''.Valid()
  ensures InUniverse_SetSet(I'', I)
  ensures b2 == (exists i' | i' in I.Model() - I''.Model() :: u in i')
  ensures counter <= counter_in + PolyCheckCoverSet(U, S, k, I)
{
  InUniverseBounds_SetSet(I', I);
  counter := counter_in;
  var i:Set<int>;
  i, counter := I'.Pick(counter);
  b2, counter := i.Contains(u, counter);
  I'', counter := I'.Remove(i, counter);
  I''_empty, counter := I''.IsEmpty(counter);
}


ghost function PolyCheckCoverSet(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
{
  UCostPick_SetSet(I) +
  UCostContains_Set(U) +
  UCostRemove_SetSet(I) +
  CostIsEmpty_SetSet(I)
}
ghost function PolyCheckUniverseElement(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
{
  CostPick_Set(U) + UCostRemove_Set(U) +
  CostIsEmpty_SetSet(I) +
  I.UCardinality()*PolyCheckCoverSet(U, S, k, I) +
  CostIsEmpty_Set(U)
}
ghost function PolyIsSubsetStep(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
{
  UCostPick_SetSet(S1) + UCostContains_SetSet(S2) +
  UCostRemove_SetSet(S1) + CostIsEmpty_SetSet(S1)
}
ghost function {:opaque} PolyIsSubset(S1:SetSet<int>, S2:SetSet<int>) : (o:nat)
  ensures o == CostIsEmpty_SetSet(S1) +
               S1.UCardinality()*PolyIsSubsetStep(S1, S2)
{
  CostIsEmpty_SetSet(S1) +
  S1.UCardinality()*PolyIsSubsetStep(S1, S2)
}


ghost function PolyVerifySetCover(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>) : (o:nat)
  requires U.Valid()
  requires S.Valid()
  requires I.Valid()
  ensures 1 <= o
{
  CostCount_SetSet(I) + PolyIsSubset(I, S) +
  CostIsEmpty_Set(U) +
  U.UCardinality()*PolyCheckUniverseElement(U, S, k, I)
}


// Fixed polynomial in the instance measure n = |U| + |S| + 1.
ghost function PolySetCoverVerification(n:nat):nat
{
  2 + (n*n + 2) + n*(2*n*n + n + 4) + n + 2 +
  n*(n + 4 + n*n + n*(n*n + 2*n + 5))
}

lemma {:isolate_assertions} CostSetCoverVerificationBound(U:Set<int>, S:SetSet<int>, k:nat, I:SetSet<int>)
  requires Init_Set(U) && Init_SetSet(S) && Init_SetSet(I)
  requires S.USize1() <= U.USize0()
  requires I.USize1() <= U.USize0()
  requires I.Cardinality() <= S.Cardinality()
  ensures PolyVerifySetCover(U, S, k, I) <= PolySetCoverVerification(|U.Model()| + |S.Model()| + 1)
{
  var n := |U.Model()| + |S.Model()| + 1;
  UniverseSizeBound_SetSet(I, n, n);
  UniverseSizeBound_SetSet(S, n, n);
  assert n*n + n*n == 2*n*n by { MultiplicationAssociative(2, n, n); }
  assert PolyIsSubsetStep(I, S) <= 2*n*n + n + 4;
  MultiplicationPreservesOrder(I.UCardinality(), PolyIsSubsetStep(I, S), n, 2*n*n + n + 4);
  assert PolyIsSubset(I, S) <= n*n + 2 + n*(2*n*n + n + 4);
  assert PolyCheckCoverSet(U, S, k, I) <= n*n + 2*n + 5;
  MultiplicationPreservesOrder(I.UCardinality(), PolyCheckCoverSet(U, S, k, I),
                       n, n*n + 2*n + 5);
  assert PolyCheckUniverseElement(U, S, k, I) <= n + 4 + n*n + n*(n*n + 2*n + 5);
  MultiplicationPreservesOrder(U.UCardinality(), PolyCheckUniverseElement(U, S, k, I),
                       n, n + 4 + n*n + n*(n*n + 2*n + 5));
}
