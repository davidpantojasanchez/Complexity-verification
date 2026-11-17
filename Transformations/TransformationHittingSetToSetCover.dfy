include "../Polynomial/PolynomialSetCover.dfy"
include "../Problems/SetSystemRepresentation.dfy"
include "../Foundations/ExactCollectionSizes.dfy"
include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"
include "../Collections/ConcreteSet.dfy"

// Build the incidence representation, preserving source-label provenance.
method {:isolate_assertions} TransformHittingSetToSetCover<T(!new)>(instance:SetSystemInstance<T>, ghost weight:T -> nat)
    returns (r:SetCoverSetInstance<T>, ghost counter:nat)
  // Representation in
  requires instance.universe.Init() && instance.sets.Init()
  // State in
  requires HittingSetValidInstance(instance.Model())
  // Representation out
  ensures r.universe.Valid() && r.sets.Valid()
  ensures r.sets.Cardinality() <= instance.universe.Cardinality()+instance.sets.Cardinality()
  ensures r.sets.Cardinality1() <= instance.sets.Cardinality()+1
  ensures r.sets.Cardinality2() <= instance.universe.Cardinality()
  ensures NatBits(r.k) <= NatBits(instance.k)
  ensures r.sets.SizeBound(weight) <= HittingSetConstructionSizeBound(SetSystemInstanceSizeBound(instance, weight))
  ensures SetSystemInstanceSize(r.universe.Model(), r.sets.Model(), r.k, member => Size_set(member, weight)) <=
          BudgetHittingSetToSetCoverOutputSize(SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
  // State out
  ensures r.Model() == HittingSetToSetCover(instance.Model())
  ensures SetCoverValidInstance(r.Model())
  ensures r.universe == instance.sets
  ensures forall setSet | setSet in r.sets.Model() :: setSet <= instance.sets.Model()
  // Cost
  ensures 0 < counter <= BudgetTransformHittingSetToSetCover(
    SetSystemInstanceSize(instance.universe.Model(), instance.sets.Model(), instance.k, weight))
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  budget_transform_hitting_set_to_set_cover_input_bound(instance, weight);
  ghost var n := SetSystemInstanceSizeBound(instance, weight);
  ghost var size := HittingSetConstructionSizeBound(n);
  ghost var primitiveBudget := BudgetPrimitiveStep(size);
  ghost var context := BitSetCost(weight, size);
  assert S.UVolumeBound1() <= U.UVolumeBound() by {
    subset_cardinality_bound_setset(S.Universe(), U.Model());
    S.u_cardinality1_bound(|U.Model()|);
  }
  counter := 0;
  // Edge case
  var empty_set:Set<T>; empty_set, counter := New_Set(counter);
  assert counter <= primitiveBudget;
  var S_contains_empty:bool; S_contains_empty, counter := S.Contains(empty_set, counter, context);
  assert counter <= 2*primitiveBudget;
  if (S_contains_empty) {
    ghost var SS_universe := (set s | s in S.Model() :: {s});
    var SS:SetSetSet<T>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
    hitting_set_singleton_universe_bounds(S, SS);
    assert |SS_universe| == S.Cardinality() by {
      var singleton := (s:set<T>) => {s};
      assert SS_universe == Image_set(S.Model(), singleton);
      injective_image_cardinality_set(S.Model(), singleton);
    }
    assert SS.UCardinality() <= S.Cardinality();
    hitting_set_output_size_bound(S, SS, weight, n);
    var S':SetSet<T>; S' := S;
    var S'_empty:bool; S'_empty, counter := S'.IsEmpty(counter, context);

    ghost var loopBase := 4*primitiveBudget;
    linear_loop_budget_zero(loopBase, BudgetAddSingletonSourceSet(size));
    while (!S'_empty)
      // Progress
      decreases S'.Cardinality()
      invariant S'_empty == (S'.Model() == {})
      // Representation
      invariant U.Valid()
      invariant SS.USizeBound(weight) <= size
      invariant SS.Valid()
      invariant S'.UniverseWithin(S)
      invariant S.UVolumeBound1() <= U.UVolumeBound()
      invariant SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
      invariant SS.UVolumeBound1() <= 1 + S.UVolumeBound1()
      // State
      invariant SS.Universe() == SS_universe
      invariant SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
      // Cost
      invariant 0 < counter
      invariant counter <= LinearLoopBudget(loopBase, BudgetAddSingletonSourceSet(size), S.Cardinality() - S'.Cardinality())
    {
      linear_loop_budget_step(loopBase, BudgetAddSingletonSourceSet(size), S.Cardinality() - S'.Cardinality());
      S', SS, S'_empty, counter := AddSingletonSourceSet(U, S, S', SS, weight, counter, size);
    }

    linear_loop_budget_bound(loopBase, BudgetAddSingletonSourceSet(size), S.Cardinality() - S'.Cardinality(), n);
    assert SS.Model() == (set s | s in S.Model() :: {s});
    hitting_set_singleton_universe_bounds(S, SS);
    nat_bits_monotonic(0, k);
    r := SetCoverSetInstance(S, SS, 0);
    hitting_set_output_input_bound(instance, r, weight);
    return r, counter;
  }
  // Regular case
  ghost var SS_universe := (set u | u in U.Model() :: (set s | s in S.Model() && u in s));
  var SS:SetSetSet<T>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
  hitting_set_incidence_universe_bounds(U, S, SS);
  ghost var target := HittingSetToSetCover(instance.Model());
  assert SS_universe == target.sets by {
    forall incidence | incidence in SS_universe
      ensures incidence in target.sets
    {
      var u :| u in U.Model() && (set s | s in S.Model() && u in s) == incidence;
    }
    forall incidence | incidence in target.sets
      ensures incidence in SS_universe
    {
      var u :| u in U.Model() && (set s | s in S.Model() && u in s) == incidence;
    }
  }
  incidence_cardinality_bound_setsetset(S.Model(), U.Model(), SS.Universe());
  hitting_set_output_size_bound(S, SS, weight, n);
  var U':Set<T>; U' := U;
  var U'_empty:bool; U'_empty, counter := U'.IsEmpty(counter, context);
  ghost var loopBase := 4*primitiveBudget;
  assert counter <= loopBase;
  linear_loop_budget_zero(loopBase, BudgetBuildIncidenceSet(n));
  while (!U'_empty)
    // Progress
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Representation
    invariant SS.USizeBound(weight) <= size
    invariant SS.Valid()
    invariant U'.UniverseWithin(U)
    invariant SS.Cardinality() <= U.Cardinality() - U'.Cardinality()
    invariant SS.UVolumeBound1() <= S.UVolumeBound()
    // State
    invariant SS.Universe() == SS_universe
    invariant SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
    // Cost
    invariant 0 < counter
    invariant counter <= LinearLoopBudget(loopBase, BudgetBuildIncidenceSet(n), U.Cardinality() - U'.Cardinality())
  {
    linear_loop_budget_step(loopBase, BudgetBuildIncidenceSet(n), U.Cardinality() - U'.Cardinality());
    U', SS, U'_empty, counter := BuildIncidenceSet(U, S, U', SS, weight, counter, n);
  }

  linear_loop_budget_bound(loopBase, BudgetBuildIncidenceSet(n), U.Cardinality() - U'.Cardinality(), n);
  difference_empty_set(U.Model(), U'.Model());

  hitting_set_incidence_universe_bounds(U, S, SS);
  r := SetCoverSetInstance(S, SS, k);
  hitting_set_output_input_bound(instance, r, weight);
  return r, counter;
}

method BuildIncidenceSet<T>(U:Set<T>, S:SetSet<T>, U':Set<T>, SS:SetSetSet<T>,
    ghost weight:T -> nat, ghost counter_in:nat, ghost n:nat)
    returns (U'':Set<T>, SS':SetSetSet<T>, U''_empty:bool, ghost counter:nat)
  // Progress in
  requires U'.Model() != {}
  // Representation in
  requires U.SizeBound(weight) <= HittingSetConstructionSizeBound(n) && S.SizeBound(weight) <= HittingSetConstructionSizeBound(n)
  requires SS.USizeBound(weight) <= HittingSetConstructionSizeBound(n)
  requires S.Cardinality() <= n
  requires S.Init()
  requires SS.Valid()
  requires SS.Universe() == (set u | u in U.Model() :: (set s | s in S.Model() && u in s))
  requires U'.UniverseWithin(U)
  requires S.UVolumeBound1() <= U.UVolumeBound()
  requires SS.Cardinality() <= (U.Cardinality() - U'.Cardinality())
  requires SS.UVolumeBound1() <= S.UVolumeBound()
  // State in
  requires SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
  // Progress out
  ensures U''_empty == (U''.Model() == {})
  ensures U''.Cardinality() == U'.Cardinality() - 1
  // Representation out
  ensures SS'.Valid()
  ensures SS'.Universe() == SS.Universe()
  ensures SS'.USizeBound(weight) == SS.USizeBound(weight)
  ensures U''.UniverseWithin(U)
  ensures SS'.Cardinality() <= (U.Cardinality() - U''.Cardinality())
  ensures SS'.UVolumeBound1() <= S.UVolumeBound()
  // State out
  ensures SS'.Model() == (set u | u in (U.Model() - U''.Model()) :: (set s | s in S.Model() && u in s))
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetBuildIncidenceSet(n)
{
  ghost var size := HittingSetConstructionSizeBound(n);
  ghost var context := BitSetCost(weight, size);
  ghost var primitiveBudget := BudgetPrimitiveStep(size);
  counter := counter_in;
  U'.universe_within_bound(U, context);
  var u:T; u, counter := U'.Pick(counter, context);
  U'', counter := U'.Remove(u, counter, context);

  var sets_in_S_that_contain_u:SetSet<T>; sets_in_S_that_contain_u, counter := NewWithUniverse_SetSet(S.Model(), counter);
  reveal sets_in_S_that_contain_u.UCardinality1();
  var S':SetSet<T>; S' := S;
  var S'_empty; S'_empty, counter := S'.IsEmpty(counter, context);
  ghost var loopBase := counter_in + 4*primitiveBudget;
  linear_loop_budget_zero(loopBase, BudgetAddIncidentSourceSet(size));
  while (!S'_empty)
    // Progress
    decreases S'.Cardinality()
    invariant S'_empty == (S'.Model() == {})
    // Representation
    invariant weight(u) <= size
    invariant U.Valid()
    invariant S'.UniverseWithin(S)
    invariant sets_in_S_that_contain_u.UniverseWithin(S)
    invariant S.UVolumeBound1() <= U.UVolumeBound()
    // State
    invariant sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
    // Cost
    invariant counter_in < counter
    invariant counter <= LinearLoopBudget(loopBase, BudgetAddIncidentSourceSet(size), S.Cardinality() - S'.Cardinality())
  {
    linear_loop_budget_step(loopBase, BudgetAddIncidentSourceSet(size), S.Cardinality() - S'.Cardinality());
    S', sets_in_S_that_contain_u, S'_empty, counter := AddIncidentSourceSet(
      U, S, S', u, sets_in_S_that_contain_u, weight, counter, size);
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

method AddIncidentSourceSet<T>(U:Set<T>, S:SetSet<T>, S':SetSet<T>, u:T, sets_in_S_that_contain_u:SetSet<T>,
    ghost weight:T -> nat, ghost counter_in:nat, ghost size:nat)
    returns (S'':SetSet<T>, sets_in_S_that_contain_u':SetSet<T>, S''_empty:bool, ghost counter:nat)
  // Progress in
  requires S'.Model() != {}
  // Representation in
  requires U.SizeBound(weight) <= size && S.SizeBound(weight) <= size
  requires weight(u) <= size
  requires U.Valid()
  requires S'.UniverseWithin(S)
  requires sets_in_S_that_contain_u.UniverseWithin(S)
  requires S.UVolumeBound1() <= U.UVolumeBound()
  // State in
  requires sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
  // Progress out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Representation out
  ensures sets_in_S_that_contain_u.UVolumeBound() <= S.UVolumeBound()
  ensures S''.UniverseWithin(S)
  ensures sets_in_S_that_contain_u'.UniverseWithin(S)
  // State out
  ensures sets_in_S_that_contain_u'.Model() == (set s | s in (S.Model() - S''.Model()) && u in s)
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetAddIncidentSourceSet(size)
{
  ghost var context := BitSetCost(weight, size);
  S'.universe_within_bound(S, context);
  sets_in_S_that_contain_u.universe_within_bound(S, context);
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s:Set<T>; s, counter := S'.Pick(counter, context);
  S'', counter := S'.Remove(s, counter, context);

  var s_contains_u:bool;
  s_contains_u, counter := s.Contains(u, counter, context);
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u'.Add(s, counter, context);
  }
  S''_empty, counter := S''.IsEmpty(counter, context);
}

method AddSingletonSourceSet<T>(U:Set<T>, S:SetSet<T>, S':SetSet<T>, SS:SetSetSet<T>,
    ghost weight:T -> nat, ghost counter_in:nat, ghost size:nat)
    returns (S'':SetSet<T>, SS':SetSetSet<T>, S''_empty:bool, ghost counter:nat)
  // Progress in
  requires S'.Model() != {}
  // Representation in
  requires U.SizeBound(weight) <= size && S.SizeBound(weight) <= size
  requires SS.USizeBound(weight) <= size
  requires U.Valid()
  requires SS.Valid()
  requires SS.Universe() == (set s | s in S.Model() :: {s})
  requires S'.UniverseWithin(S)
  requires S.UVolumeBound1() <= U.UVolumeBound()
  requires SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
  requires SS.UVolumeBound1() <= 1 + S.UVolumeBound1()
  // State in
  requires SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
  // Progress out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Representation out
  ensures SS'.Valid()
  ensures SS'.Universe() == SS.Universe()
  ensures SS'.USizeBound(weight) == SS.USizeBound(weight)
  ensures S''.UniverseWithin(S)
  ensures SS'.Cardinality() <= S.Cardinality() - S''.Cardinality()
  ensures SS'.UVolumeBound1() <= 1 + S.UVolumeBound1()
  // State out
  ensures SS'.Model() == (set s | s in (S.Model() - S''.Model()) :: {s})
  // Cost
  ensures counter_in < counter
  ensures counter <= counter_in + BudgetAddSingletonSourceSet(size)
{
  ghost var context := BitSetCost(weight, size);
  S'.universe_within_bound(S, context);
  counter := counter_in;
  var s:Set<T>; s, counter := S'.Pick(counter, context);
  S'', counter := S'.Remove(s, counter, context);
  var s_set:SetSet<T>; s_set, counter := NewWithUniverse_SetSet(S.Model(), counter);
  reveal s_set.UCardinality1();
  s_set, counter := s_set.Add(s, counter, context);
  s_set.universe_within_bound(S, context);
  SS', counter := SS.Add(s_set, counter, context);
  reveal SS'.UCardinality1(), SS'.UCardinality2(), SS.UCardinality1(), SS.UCardinality2();
  S''_empty, counter := S''.IsEmpty(counter, context);
}
