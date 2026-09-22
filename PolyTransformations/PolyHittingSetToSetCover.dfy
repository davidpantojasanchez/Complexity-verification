include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/ConcreteSet.dfy"


method TransformHittingSetToSetCover(U:Set<int>, S:SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, nat), ghost counter:nat)
  // Types in
  requires HittingSetValidInstance(U.Model(), S.Model())
  requires Init_Set(U) && Init_SetSet(S)
  // Invariant out
  ensures (r.0.Model(),r.1.Model(),r.2) == HittingSetToSetCover(U.Model(), S.Model(), k)
  // Counter
  ensures counter <= PolyHittingSetToSetCover(U.Cardinality() + S.Cardinality() + 1)
{
  assert S.USize1() <= U.USize0() by {
    UniverseSubsetSizeBound_SetSet(S, U.Model());
  }
  CostHittingSetToSetCoverBound(U, S, k);
  counter := 0;
  // Edge case
  var empty_set:Set<int>; empty_set, counter := New_Set(counter);
  var S_contains_empty:bool; S_contains_empty, counter := S.Contains(empty_set, counter);
  if (S_contains_empty) {

    ghost var SS_universe := (set s | s in S.Model() :: {s});
    var SS:SetSetSet<int>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
    HittingSetSingletonUniverseBounds(S, SS);
    var S':SetSet<int>; S' := S;
    var S'_empty:bool; S'_empty, counter := S'.IsEmpty(counter);

    ghost var loopBase := CostNew_Set() + UCostContains_SetSet(S) + CostNew_SetSetSet() + CostIsEmpty_SetSet(S);
    LinearLoopBudgetZero(loopBase, PolyAddSingletonSourceSet(U, S, k));
    while (!S'_empty)
      // Termination
      decreases S'.Cardinality()
      invariant S'_empty == (S'.Model() == {})
      // Types
      invariant U.Valid()
      invariant SS.Valid()
      invariant InUniverse_SetSet(S', S)
      invariant S.USize1() <= U.USize0()
      invariant SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
      invariant SS.USize1() <= S.USize1()
      // Regular invariants
      invariant SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
      // Counter
      invariant counter <= LinearLoopBudget(loopBase, PolyAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality())
    {
      LinearLoopBudgetStep(loopBase, PolyAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality());
      S', SS, S'_empty, counter := AddSingletonSourceSet(U, S, k, S', SS, counter);
    }
    PolyBranchBounds(U, S, k);
    LinearLoopBudgetBound(loopBase, PolyAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality(), S.UCardinality());
    LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, PolyAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()),
      loopBase + (S.UCardinality())*(PolyAddSingletonSourceSet(U, S, k)), 0, PolyTransformHittingSetToSetCover(U, S, k));
    assert SS.Model() == (set s | s in S.Model() :: {s});
    return (S, SS, 0), counter;
  }
  // Regular case
  ghost var SS_universe := (set u | u in U.Model() :: (set s | s in S.Model() && u in s));
  var SS:SetSetSet<int>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
  HittingSetIncidenceUniverseBounds(U, S, SS);
  var U':Set<int>; U' := U;
  var U'_empty:bool; U'_empty, counter := U'.IsEmpty(counter);
  ghost var loopBase := CostNew_Set() + UCostContains_SetSet(S) + CostNew_SetSetSet() +
      CostIsEmpty_Set(U);
  LinearLoopBudgetZero(loopBase, PolyBuildIncidenceSet(U, S, k));
  while (!U'_empty)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant SS.Valid()
    invariant InUniverse_Set(U', U)
    invariant SS.Cardinality() <= U.Cardinality() - U'.Cardinality()
    invariant SS.USize1() <= S.USize0()
    // Regular invariants
    invariant SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, PolyBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, PolyBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality());
    U', SS, U'_empty, counter := BuildIncidenceSet(U, S, k, U', SS, counter);
  }
  PolyBranchBounds(U, S, k);
  LinearLoopBudgetBound(loopBase, PolyBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality(), U.UCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, PolyBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality()),
    loopBase + (U.UCardinality())*(PolyBuildIncidenceSet(U, S, k)), 0, PolyTransformHittingSetToSetCover(U, S, k));
  SubtractionIdentity(U.Model(), U'.Model());

  return (S,SS,k),counter;
}


method BuildIncidenceSet(U:Set<int>, S:SetSet<int>, k:nat, U':Set<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (U'':Set<int>, SS':SetSetSet<int>, U''_empty:bool, ghost counter:nat)
  // Termination in
  requires U'.Model() != {}
  // Types in
  requires Init_SetSet(S)
  requires SS.Valid()
  requires InUniverse_Set(U', U)
  requires S.USize1() <= U.USize0()
  requires SS.Cardinality() <= (U.Cardinality() - U'.Cardinality())
  requires SS.USize1() <= S.USize0()
  // Invariant in
  requires SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
  // Termination out
  ensures U''_empty == (U''.Model() == {})
  ensures U''.Cardinality() == U'.Cardinality() - 1
  // Types out
  ensures SS'.Valid()
  ensures InUniverse_Set(U'', U)
  ensures SS'.Cardinality() <= (U.Cardinality() - U''.Cardinality())
  ensures SS'.USize1() <= S.USize0()
  // Invariant out
  ensures SS'.Model() == (set u | u in (U.Model() - U''.Model()) :: (set s | s in S.Model() && u in s))
  // Counter
  ensures counter <= counter_in + PolyBuildIncidenceSet(U, S, k)
{
  counter := counter_in;
  InUniverseBounds_Set(U', U);
  var u:int; u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var sets_in_S_that_contain_u:SetSet<int>; sets_in_S_that_contain_u, counter := NewWithUniverse_SetSet(S.Model(), counter);
  UniverseMemberSizeBound_SetSet(sets_in_S_that_contain_u, S.USize1());
  ModelSizeBound_SetSet(S);
  var S'; S' := S;
  var S'_empty; S'_empty, counter := S'.IsEmpty(counter);
  ghost var loopBase := counter_in + CostPick_Set(U) + UCostRemove_Set(U) + CostNew_SetSet() +
    CostIsEmpty_SetSet(S);
  LinearLoopBudgetZero(loopBase, PolyAddIncidentSourceSet(U, S, k));
  while (!S'_empty)
    // Termination
    decreases S'.Cardinality()
    invariant S'_empty == (S'.Model() == {})
    // Types
    invariant U.Valid()
    invariant InUniverse_SetSet(S', S)
    invariant InUniverse_SetSet(sets_in_S_that_contain_u, S)
    invariant S.USize1() <= U.USize0()
    // Regular invariants
    invariant sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, PolyAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, PolyAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality());
    S', sets_in_S_that_contain_u, S'_empty, counter := AddIncidentSourceSet(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  PolyBuildIncidenceSetDefinition(U, S, k);
  LinearLoopBudgetBound(loopBase, PolyAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality(), S.UCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, PolyAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()),
    loopBase + (S.UCardinality())*(PolyAddIncidentSourceSet(U, S, k)), S.USize0()*U.UCardinality() + 1 + CostIsEmpty_Set(U), counter_in + PolyBuildIncidenceSet(U, S, k));
  InUniverseBounds_SetSet(sets_in_S_that_contain_u, S);
  SS', counter := SS.Add(sets_in_S_that_contain_u, counter);

  U''_empty, counter := U''.IsEmpty(counter);
  ModelSizeBound_SetSetSet(SS);
  NatMultiplicationMonotonic(SS.Cardinality(), SS.Size1(), SS.USize1());
  MultiplicationPreservesOrder(SS.Cardinality(), SS.USize1(), U.UCardinality(), S.USize0());
  assert CostAdd_SetSetSet(SS) <= S.USize0()*U.UCardinality() + 1;
  calc <= {
    counter;
    LinearLoopBudget(loopBase, PolyAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()) +
      CostAdd_SetSetSet(SS) + CostIsEmpty_Set(U);
    LinearLoopBudget(loopBase, PolyAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()) +
      S.USize0()*U.UCardinality() + 1 + CostIsEmpty_Set(U);
    counter_in + PolyBuildIncidenceSet(U, S, k);
  }
  assert SS'.Model() == (set v | v in (U.Model() - U''.Model()) :: (set s | s in S.Model() && v in s)) by {
    assert (S.Model() - S'.Model()) == S.Model();
    assert SS'.Model() == (set v | v in (U.Model() - U'.Model()) + {u} :: (set s | s in S.Model() && v in s));
    assert (U.Model() - U''.Model()) == (U.Model() - U'.Model()) + {u};
  }
}


method AddIncidentSourceSet(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, u:int, sets_in_S_that_contain_u:SetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, sets_in_S_that_contain_u':SetSet<int>, S''_empty:bool, ghost counter:nat)
  // Termination in
  requires S'.Model() != {}
  // Types in
  requires U.Valid()
  requires InUniverse_SetSet(S', S)
  requires InUniverse_SetSet(sets_in_S_that_contain_u, S)
  requires S.USize1() <= U.USize0()
  // Invariant in
  requires sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
  // Termination out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Types out
  ensures sets_in_S_that_contain_u.USize0() <= S.USize0()
  ensures InUniverse_SetSet(S'', S)
  ensures InUniverse_SetSet(sets_in_S_that_contain_u', S)
  // Invariant out
  ensures sets_in_S_that_contain_u'.Model() == (set s | s in (S.Model() - S''.Model()) && u in s)
  // Counter
  ensures counter <= counter_in + PolyAddIncidentSourceSet(U, S, k)
{
  InUniverseBounds_SetSet(S', S);
  InUniverseBounds_SetSet(sets_in_S_that_contain_u, S);
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);

  var s_contains_u:bool;
  s_contains_u, counter := s.Contains(u, counter);
  PolyAddIncidentSourceSetDefinition(U, S, k);
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u'.Add(s, counter);
  }
  S''_empty, counter := S''.IsEmpty(counter);
}


method {:isolate_assertions} AddSingletonSourceSet(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, SS':SetSetSet<int>, S''_empty:bool, ghost counter:nat)
  // Termination in
  requires S'.Model() != {}
  // Types in
  requires U.Valid()
  requires SS.Valid()
  requires InUniverse_SetSet(S', S)
  requires S.USize1() <= U.USize0()
  requires SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
  requires SS.USize1() <= S.USize1()
  // Invariant in
  requires SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
  // Termination out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Types out
  ensures SS'.Valid()
  ensures InUniverse_SetSet(S'', S)
  ensures SS'.Cardinality() <= S.Cardinality() - S''.Cardinality()
  ensures SS'.USize1() <= S.USize1()
  // Invariant out
  ensures SS'.Model() == (set s | s in (S.Model() - S''.Model()) :: {s})
  // Counter
  ensures counter <= counter_in + PolyAddSingletonSourceSet(U, S, k)
{
  InUniverseBounds_SetSet(S', S);
  MultiplicationPreservesOrder(SS.Cardinality(), SS.USize1(), S.Cardinality(), S.USize1());
  counter := counter_in;
  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);
  var s_set:SetSet<int>; s_set, counter := NewWithUniverse_SetSet(S.Model(), counter);
  UniverseMemberSizeBound_SetSet(s_set, S.USize1());
  ghost var empty_s_set := s_set;
  s_set, counter := s_set.Add(s, counter);
  ModelSizeBound_SetSet(s_set);
  SS', counter := SS.Add(s_set, counter);
  S''_empty, counter := S''.IsEmpty(counter);
  ModelSizeBound_SetSet(S);
  NatMultiplicationMonotonic(S.USize1(), S.Cardinality(), S.UCardinality());
  ModelSizeBound_SetSetSet(SS);
  NatMultiplicationMonotonic(SS.Cardinality(), SS.Size1(), SS.USize1());
  calc <= {
    CostAdd_SetSetSet(SS);
    SS.Cardinality()*SS.USize1() + 1;
    S.Cardinality()*S.USize1() + 1;
    S.USize0() + 1;
  }
}



lemma HittingSetSingletonUniverseBounds(S:SetSet<int>, SS:SetSetSet<int>)
  requires S.Valid() && SS.Valid()
  requires SS.Universe() == (set s | s in S.Model() :: {s})
  ensures SS.USize1() <= S.USize1()
  ensures SS.USize2() <= S.USize1()
{
  forall child | child in SS.Universe()
    ensures |child| * MaxCardinality_set(child) <= S.USize1()
    ensures MaxCardinality_set(child) <= S.USize1()
  {
    var s :| s in S.Model() && child == {s};
    MaxCardinalityInsert_set({}, s);
  }
  UniverseMemberSizeBound_SetSetSet(SS, S.USize1());
  UniverseLeafSizeBound_SetSetSet(SS, S.USize1());
}

lemma HittingSetIncidenceUniverseBounds(U:Set<int>, S:SetSet<int>, SS:SetSetSet<int>)
  requires S.Valid() && SS.Valid()
  requires SS.Universe() == (set u | u in U.Model() :: (set s | s in S.Model() && u in s))
  ensures SS.USize1() <= S.USize0()
  ensures SS.USize2() <= S.USize1()
{
  ModelSizeBound_SetSet(S);
  forall child | child in SS.Universe()
    ensures |child| * MaxCardinality_set(child) <= S.USize0()
    ensures MaxCardinality_set(child) <= S.USize1()
  {
    assert child <= S.Model();
    SubsetCardinalityBound(child, S.Model());
    MaxCardinalityMonotonic_set(child, S.Model());
    MultiplicationPreservesOrder(|child|, MaxCardinality_set(child), S.Cardinality(), S.Size1());
  }
  UniverseMemberSizeBound_SetSetSet(SS, S.USize0());
  UniverseLeafSizeBound_SetSetSet(SS, S.USize1());
}


ghost function {:opaque} PolyAddIncidentSourceSet(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  UCostPick_SetSet(S) +
  UCostRemove_SetSet(S) + UCostContains_Set(U) +
  UCostAdd_SetSet(S) + CostIsEmpty_SetSet(S)
}
ghost function {:opaque} PolyBuildIncidenceSet(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  CostPick_Set(U) + UCostRemove_Set(U) + CostNew_SetSet() +
  CostIsEmpty_SetSet(S) +
  S.UCardinality()*PolyAddIncidentSourceSet(U, S, k) +
  S.USize0()*U.UCardinality() + 1 + CostIsEmpty_Set(U)
}
ghost function {:opaque} PolyAddSingletonSourceSet(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures o == UCostPick_SetSet(S) + UCostRemove_SetSet(S) +
               CostNew_SetSet() + UCostAdd_SetSet(S) +
               S.USize0() + 1 + CostIsEmpty_SetSet(S)
{
  UCostPick_SetSet(S) + UCostRemove_SetSet(S) +
  CostNew_SetSet() + UCostAdd_SetSet(S) +
  S.USize0() + 1 + CostIsEmpty_SetSet(S)
}


ghost function {:opaque} PolyTransformHittingSetToSetCover(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  CostNew_Set() + UCostContains_SetSet(S) + CostNew_SetSetSet() +
  CostIsEmpty_SetSet(S) +
  S.UCardinality()*PolyAddSingletonSourceSet(U, S, k) +
  CostNew_Set() + UCostContains_SetSet(S) + CostNew_SetSetSet() +
  CostIsEmpty_Set(U) +
  U.UCardinality()*PolyBuildIncidenceSet(U, S, k)
}


ghost function PolyHittingSetToSetCover(n:nat):nat
{
  (1 + (n*n + 1) + 1 + (n*n + 1) + 1 + n*(3*n*n + n + 6)) +
  (1 + (n*n + 1) + 1 + (n + 1) + 1 +
    n*(n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7))
}


lemma PolyAddIncidentSourceSetDefinition(U:Set<int>, S:SetSet<int>, k:nat)
  ensures PolyAddIncidentSourceSet(U, S, k) ==
    UCostPick_SetSet(S) +
    UCostRemove_SetSet(S) + UCostContains_Set(U) +
    UCostAdd_SetSet(S) + CostIsEmpty_SetSet(S)
{
  reveal PolyAddIncidentSourceSet();
}

lemma PolyBuildIncidenceSetDefinition(U:Set<int>, S:SetSet<int>, k:nat)
  ensures PolyBuildIncidenceSet(U, S, k) ==
    CostPick_Set(U) + UCostRemove_Set(U) + CostNew_SetSet() +
    CostIsEmpty_SetSet(S) +
    S.UCardinality()*PolyAddIncidentSourceSet(U, S, k) +
    S.USize0()*U.UCardinality() + 1 + CostIsEmpty_Set(U)
{
  reveal PolyBuildIncidenceSet();
}

lemma PolyBranchBounds(U:Set<int>, S:SetSet<int>, k:nat)
  ensures CostNew_Set() + UCostContains_SetSet(S) + CostNew_SetSetSet() +
          CostIsEmpty_SetSet(S) +
          S.UCardinality()*PolyAddSingletonSourceSet(U, S, k) <= PolyTransformHittingSetToSetCover(U, S, k)
  ensures CostNew_Set() + UCostContains_SetSet(S) + CostNew_SetSetSet() +
          CostIsEmpty_Set(U) +
          U.UCardinality()*PolyBuildIncidenceSet(U, S, k) <= PolyTransformHittingSetToSetCover(U, S, k)
{
  reveal PolyTransformHittingSetToSetCover();
}


lemma CostHittingSetToSetCoverBound(U:Set<int>, S:SetSet<int>, k:nat)
  requires Init_Set(U) && Init_SetSet(S)
  requires S.USize1() <= U.USize0()
  ensures PolyTransformHittingSetToSetCover(U, S, k) <=
    PolyHittingSetToSetCover(U.Cardinality() + S.Cardinality() + 1)
{
  var n := U.Cardinality() + S.Cardinality() + 1;
  assert U.UCardinality() <= n;
  assert U.USize0() <= n;
  assert S.UCardinality() <= n;
  assert S.USize1() <= n;
  UniverseSizeBound_SetSet(S, n, n);

  assert UCostContains_SetSet(S) <= n*n + 1;
  assert UCostRemove_SetSet(S) <= n*n + 1;
  assert UCostAdd_SetSet(S) <= n*n + 1;
  assert UCostPick_SetSet(S) <= n + 1;
  assert UCostRemove_Set(U) <= n + 1;

  reveal PolyAddSingletonSourceSet();
  calc <= {
    PolyAddSingletonSourceSet(U, S, k);
    (n + 1) + (n*n + 1) + 1 + (n*n + 1) + (n*n + 1) + 1;
    3*n*n + n + 6;
  }

  PolyAddIncidentSourceSetDefinition(U, S, k);
  calc <= {
    PolyAddIncidentSourceSet(U, S, k);
    (n + 1) + (n*n + 1) + (n + 1) + (n*n + 1) + 1;
    2*n*n + 2*n + 5;
    3*n*n + 5*n + 6;
    4*n*n + 5*n + 7;
  }

  PolyBuildIncidenceSetDefinition(U, S, k);
  MultiplicationPreservesOrder(S.UCardinality(), PolyAddIncidentSourceSet(U, S, k), n, 4*n*n + 5*n + 7);
  MultiplicationPreservesOrder(S.USize0(), U.UCardinality(), n*n, n);
  calc <= {
    PolyBuildIncidenceSet(U, S, k);
    1 + (n + 1) + 1 + 1 +
      n*(4*n*n + 5*n + 7) + n*n*n + 1 + 1;
    n + n*(4*n*n + 5*n + 7) + n*n*n + 6;
    n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7;
  }

  MultiplicationPreservesOrder(S.UCardinality(), PolyAddSingletonSourceSet(U, S, k), n, 3*n*n + n + 6);
  MultiplicationPreservesOrder(U.UCardinality(), PolyBuildIncidenceSet(U, S, k), n,
    n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7);
  reveal PolyTransformHittingSetToSetCover();
  calc <= {
    PolyTransformHittingSetToSetCover(U, S, k);
    (1 + (n*n + 1) + 1 + 1 + n*(3*n*n + n + 6)) +
      (1 + (n*n + 1) + 1 + 1 +
        n*(n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7));
    (1 + (n*n + 1) + 1 + (n*n + 1) + 1 + n*(3*n*n + n + 6)) +
      (1 + (n*n + 1) + 1 + (n + 1) + 1 +
        n*(n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7));
    PolyHittingSetToSetCover(n);
  }
}
