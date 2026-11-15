include "../Polynomial/PolynomialSetCover.dfy"
include "../Problems/SetSystemCollections.dfy"
include "../Foundations/CollectionSizes.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Problems/HittingSetLemmas.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/Collections.dfy"
include "../Foundations/LoopCosts.dfy"
include "../Collections/ConcreteSet.dfy"

// Build the incidence representation, preserving source-label provenance.
method {:isolate_assertions} TransformHittingSetToSetCover(U:Set<int>, S:SetSet<int>, k:nat)
    returns (r:SetCoverSetIntInstance, ghost counter:nat)
  // Representation in
  requires U.Init() && S.Init()
  // State in
  requires HittingSetValidInstance(U.Model(), S.Model())
  // Representation out
  ensures r.0.Valid() && r.1.Valid()
  ensures r.1.Cardinality() <= U.Cardinality()+S.Cardinality()
  ensures r.1.Cardinality1() <= S.Cardinality()+1
  ensures r.1.Cardinality2() <= U.Cardinality()
  ensures NatBits(r.2) <= NatBits(k)
  ensures r.1.Size(IntBits) <= HittingSetOperandSizeBound(HittingSetPhaseSizeBound(U,S,k))
  ensures SetSystemInstanceSize(r.0.Model(), r.1.Model(), r.2, Size_setint) <=
    BoundHittingSetToSetCoverOutputSize(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
  ensures HittingSetOutputOperandSizeBound(r) <=
    BoundHittingSetToSetCoverOutputSize(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
  // State out
  ensures (r.0.Model(), r.1.Model(), r.2) == HittingSetToSetCover(U.Model(), S.Model(), k)
  ensures SetCoverValidInstance(r.0.Model(), r.1.Model())
  ensures r.0 == S
  ensures forall setSet | setSet in r.1.Model() :: setSet <= S.Model()
  // Cost
  ensures 0 < counter <= BudgetTransformHittingSetToSetCover(SetSystemInstanceSize(U.Model(), S.Model(), k, IntBits))
{
  budget_transform_hitting_set_to_set_cover_input_bound(U, S, k);
  ghost var n := HittingSetPhaseSizeBound(U,S,k);
  ghost var size := HittingSetOperandSizeBound(n);
  ghost var primitiveBudget := BudgetPrimitiveStep(size);
  ghost var context := BitSetCost(IntBits, size);
  assert S.UVolume1() <= U.UVolume() by {
    subset_cardinality_bound_setset(S.Universe(), U.Model());
    S.u_cardinality1_bound(|U.Model()|);
  }
  counter := 0;
  // Edge case
  var empty_set:Set<int>; empty_set, counter := New_Set(counter);
  assert counter <= primitiveBudget;
  var S_contains_empty:bool; S_contains_empty, counter := S.Contains(empty_set, counter, context);
  assert counter <= 2*primitiveBudget;
  if (S_contains_empty) {
    ghost var SS_universe := (set s | s in S.Model() :: {s});
    var SS:SetSetSet<int>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
    hitting_set_singleton_universe_bounds(S, SS);
    hitting_set_singleton_cardinality_setset(S.Model());
    assert SS.UCardinality() <= S.Cardinality();
    hitting_set_output_size_bound(S, SS, n);
    var S':SetSet<int>; S' := S;
    var S'_empty:bool; S'_empty, counter := S'.IsEmpty(counter, context);

    ghost var loopBase := 4*primitiveBudget;
    linear_loop_budget_zero(loopBase, BudgetAddSingletonSourceSet(size));
    while (!S'_empty)
      // Progress
      decreases S'.Cardinality()
      invariant S'_empty == (S'.Model() == {})
      // Representation
      invariant U.Valid()
      invariant SS.USize(IntBits) <= size
      invariant SS.Valid()
      invariant S'.UniverseWithin(S)
      invariant S.UVolume1() <= U.UVolume()
      invariant SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
      invariant SS.UVolume1() <= 1 + S.UVolume1()
      // State
      invariant SS.Universe() == SS_universe
      invariant SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
      // Cost
      invariant 0 < counter
      invariant counter <= LinearLoopBudget(loopBase, BudgetAddSingletonSourceSet(size), S.Cardinality() - S'.Cardinality())
    {
      linear_loop_budget_step(loopBase, BudgetAddSingletonSourceSet(size), S.Cardinality() - S'.Cardinality());
      S', SS, S'_empty, counter := AddSingletonSourceSet(U, S, k, S', SS, counter, size);
    }

    linear_loop_budget_bound(loopBase, BudgetAddSingletonSourceSet(size), S.Cardinality() - S'.Cardinality(), n);
    assert SS.Model() == (set s | s in S.Model() :: {s});
    hitting_set_singleton_universe_bounds(S, SS);
    nat_bits_monotonic(0, k);
    hitting_set_output_input_bound(U, S, k, (S, SS, 0));
    return (S, SS, 0), counter;
  }
  // Regular case
  ghost var SS_universe := (set u | u in U.Model() :: (set s | s in S.Model() && u in s));
  var SS:SetSetSet<int>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
  hitting_set_incidence_universe_bounds(U, S, SS);
  incidence_cardinality_bound_setsetset(U.Model(),S.Model(),U.Model(),SS.Universe());
  hitting_set_output_size_bound(S, SS, n);
  var U':Set<int>; U' := U;
  var U'_empty:bool; U'_empty, counter := U'.IsEmpty(counter, context);
  ghost var loopBase := 4*primitiveBudget;
  assert counter <= loopBase;
  linear_loop_budget_zero(loopBase, BudgetBuildIncidenceSet(n));
  while (!U'_empty)
    // Progress
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Representation
    invariant SS.USize(IntBits) <= size
    invariant SS.Valid()
    invariant U'.UniverseWithin(U)
    invariant SS.Cardinality() <= U.Cardinality() - U'.Cardinality()
    invariant SS.UVolume1() <= S.UVolume()
    // State
    invariant SS.Universe() == SS_universe
    invariant SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
    // Cost
    invariant 0 < counter
    invariant counter <= LinearLoopBudget(loopBase, BudgetBuildIncidenceSet(n), U.Cardinality() - U'.Cardinality())
  {
    linear_loop_budget_step(loopBase, BudgetBuildIncidenceSet(n), U.Cardinality() - U'.Cardinality());
    U', SS, U'_empty, counter := BuildIncidenceSet(U, S, k, U', SS, counter, n);
  }

  linear_loop_budget_bound(loopBase, BudgetBuildIncidenceSet(n), U.Cardinality() - U'.Cardinality(), n);
  difference_empty_set(U.Model(), U'.Model());

  hitting_set_incidence_universe_bounds(U, S, SS);
  hitting_set_output_input_bound(U, S, k, (S, SS, k));
  return (S,SS,k),counter;
}

method {:isolate_assertions} BuildIncidenceSet(U:Set<int>, S:SetSet<int>, k:nat, U':Set<int>, SS:SetSetSet<int>, ghost counter_in:nat, ghost n:nat)
    returns (U'':Set<int>, SS':SetSetSet<int>, U''_empty:bool, ghost counter:nat)
  // Progress in
  requires U'.Model() != {}
  // Representation in
  requires U.Size(IntBits) <= HittingSetOperandSizeBound(n) && S.Size(IntBits) <= HittingSetOperandSizeBound(n)
  requires SS.USize(IntBits) <= HittingSetOperandSizeBound(n)
  requires S.Cardinality() <= n
  requires S.Init()
  requires SS.Valid()
  requires SS.Universe() == (set u | u in U.Model() :: (set s | s in S.Model() && u in s))
  requires U'.UniverseWithin(U)
  requires S.UVolume1() <= U.UVolume()
  requires SS.Cardinality() <= (U.Cardinality() - U'.Cardinality())
  requires SS.UVolume1() <= S.UVolume()
  // State in
  requires SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
  // Progress out
  ensures U''_empty == (U''.Model() == {})
  ensures U''.Cardinality() == U'.Cardinality() - 1
  // Representation out
  ensures SS'.Valid()
  ensures SS'.Universe() == SS.Universe()
  ensures SS'.USize(IntBits) == SS.USize(IntBits)
  ensures U''.UniverseWithin(U)
  ensures SS'.Cardinality() <= (U.Cardinality() - U''.Cardinality())
  ensures SS'.UVolume1() <= S.UVolume()
  // State out
  ensures SS'.Model() == (set u | u in (U.Model() - U''.Model()) :: (set s | s in S.Model() && u in s))
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetBuildIncidenceSet(n)
{
  ghost var size := HittingSetOperandSizeBound(n);
  ghost var context := BitSetCost(IntBits, size);
  ghost var primitiveBudget := BudgetPrimitiveStep(size);
  counter := counter_in;
  U'.universe_within_bound(U, context);
  var u:int; u, counter := U'.Pick(counter, context);
  U'', counter := U'.Remove(u, counter, context);

  var sets_in_S_that_contain_u:SetSet<int>; sets_in_S_that_contain_u, counter := NewWithUniverse_SetSet(S.Model(), counter);
  reveal sets_in_S_that_contain_u.UCardinality1();
  var S':SetSet<int>; S' := S;
  var S'_empty; S'_empty, counter := S'.IsEmpty(counter, context);
  ghost var loopBase := counter_in + 4*primitiveBudget;
  linear_loop_budget_zero(loopBase, BudgetAddIncidentSourceSet(size));
  while (!S'_empty)
    // Progress
    decreases S'.Cardinality()
    invariant S'_empty == (S'.Model() == {})
    // Representation
    invariant IntBits(u) <= size
    invariant U.Valid()
    invariant S'.UniverseWithin(S)
    invariant sets_in_S_that_contain_u.UniverseWithin(S)
    invariant S.UVolume1() <= U.UVolume()
    // State
    invariant sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(loopBase, BudgetAddIncidentSourceSet(size), S.Cardinality() - S'.Cardinality())
  {
    linear_loop_budget_step(loopBase, BudgetAddIncidentSourceSet(size), S.Cardinality() - S'.Cardinality());
    S', sets_in_S_that_contain_u, S'_empty, counter := AddIncidentSourceSet(U, S, k, S', u, sets_in_S_that_contain_u, counter, size);
  }
  linear_loop_budget_bound(loopBase, BudgetAddIncidentSourceSet(size), S.Cardinality() - S'.Cardinality(), n);
  sets_in_S_that_contain_u.universe_within_bound(S, context);
  assert sets_in_S_that_contain_u.Model() in SS.Universe() by {
    assert sets_in_S_that_contain_u.Model() == (set s | s in S.Model() && u in s);
    assert u in U.Model();
  }
  SS', counter := SS.Add(sets_in_S_that_contain_u, counter, context);
  reveal SS'.UCardinality1(), SS'.UCardinality2(), SS.UCardinality1(), SS.UCardinality2();

  U''.universe_within_bound(U, context);
  U''_empty, counter := U''.IsEmpty(counter, context);
  assert SS'.Model() == (set v | v in (U.Model() - U''.Model()) :: (set s | s in S.Model() && v in s)) by {
    assert (S.Model() - S'.Model()) == S.Model();
    assert SS'.Model() == (set v | v in (U.Model() - U'.Model()) + {u} :: (set s | s in S.Model() && v in s));
    assert (U.Model() - U''.Model()) == (U.Model() - U'.Model()) + {u};
  }
}

method AddIncidentSourceSet(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, u:int, sets_in_S_that_contain_u:SetSet<int>, ghost counter_in:nat, ghost size:nat)
    returns (S'':SetSet<int>, sets_in_S_that_contain_u':SetSet<int>, S''_empty:bool, ghost counter:nat)
  // Progress in
  requires S'.Model() != {}
  // Representation in
  requires U.Size(IntBits) <= size && S.Size(IntBits) <= size
  requires S.Cardinality1() <= size && 1 <= size
  requires IntBits(u) <= size
  requires U.Valid()
  requires S'.UniverseWithin(S)
  requires sets_in_S_that_contain_u.UniverseWithin(S)
  requires S.UVolume1() <= U.UVolume()
  // State in
  requires sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
  // Progress out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Representation out
  ensures sets_in_S_that_contain_u.UVolume() <= S.UVolume()
  ensures S''.UniverseWithin(S)
  ensures sets_in_S_that_contain_u'.UniverseWithin(S)
  // State out
  ensures sets_in_S_that_contain_u'.Model() == (set s | s in (S.Model() - S''.Model()) && u in s)
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetAddIncidentSourceSet(size)
{
  ghost var context := BitSetCost(IntBits, size);
  S'.universe_within_bound(S, context);
  sets_in_S_that_contain_u.universe_within_bound(S, context);
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s:Set<int>; s, counter := S'.Pick(counter, context);
  S'', counter := S'.Remove(s, counter, context);

  var s_contains_u:bool;
  s_contains_u, counter := s.Contains(u, counter, context);
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u'.Add(s, counter, context);
  }
  S''_empty, counter := S''.IsEmpty(counter, context);
}

method {:isolate_assertions} AddSingletonSourceSet(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, SS:SetSetSet<int>, ghost counter_in:nat, ghost size:nat)
    returns (S'':SetSet<int>, SS':SetSetSet<int>, S''_empty:bool, ghost counter:nat)
  // Progress in
  requires S'.Model() != {}
  // Representation in
  requires U.Size(IntBits) <= size && S.Size(IntBits) <= size
  requires S.Cardinality1() <= size && 1 <= size
  requires SS.USize(IntBits) <= size
  requires U.Valid()
  requires SS.Valid()
  requires SS.Universe() == (set s | s in S.Model() :: {s})
  requires S'.UniverseWithin(S)
  requires S.UVolume1() <= U.UVolume()
  requires SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
  requires SS.UVolume1() <= 1 + S.UVolume1()
  // State in
  requires SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
  // Progress out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Representation out
  ensures SS'.Valid()
  ensures SS'.Universe() == SS.Universe()
  ensures SS'.USize(IntBits) == SS.USize(IntBits)
  ensures S''.UniverseWithin(S)
  ensures SS'.Cardinality() <= S.Cardinality() - S''.Cardinality()
  ensures SS'.UVolume1() <= 1 + S.UVolume1()
  // State out
  ensures SS'.Model() == (set s | s in (S.Model() - S''.Model()) :: {s})
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetAddSingletonSourceSet(size)
{
  ghost var context := BitSetCost(IntBits, size);
  S'.universe_within_bound(S, context);
  counter := counter_in;
  var s:Set<int>; s, counter := S'.Pick(counter, context);
  S'', counter := S'.Remove(s, counter, context);
  var s_set:SetSet<int>; s_set, counter := NewWithUniverse_SetSet(S.Model(), counter);
  reveal s_set.UCardinality1();
  s_set, counter := s_set.Add(s, counter, context);
  s_set.universe_within_bound(S, context);
  SS', counter := SS.Add(s_set, counter, context);
  reveal SS'.UCardinality1(), SS'.UCardinality2(), SS.UCardinality1(), SS.UCardinality2();
  S''_empty, counter := S''.IsEmpty(counter, context);
}
