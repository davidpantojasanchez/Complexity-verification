include "../Lemmas/PolynomialBounds.dfy"
include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Lemmas/Lemmas.dfy"
include "../Collections/ConcreteSet.dfy"


method TransformHittingSetToSetCover(U:Set<int>, S:SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, nat), ghost counter:nat)
  requires HittingSetValidInstance(U.Model(), S.Model())
  requires U.Init() && S.Init()
  ensures (r.0.Model(),r.1.Model(),r.2) == HittingSetToSetCover(U.Model(), S.Model(), k)
  ensures counter <= CostTransformHittingSetToSetCover(U, S, k)
{
  assert S.USize1() <= U.USize() by {
    family_subset_cardinality_bound(S.Universe(), U.Model());
    S.u_cardinality1_bound(|U.Model()|);
  }
  counter := 0;
  // Edge case
  var empty_set:Set<int>; empty_set, counter := New_Set(counter);
  var S_contains_empty:bool; S_contains_empty, counter := S.Contains(empty_set, counter);
  if (S_contains_empty) {
    ghost var SS_universe := (set s | s in S.Model() :: {s});
    var SS:SetSetSet<int>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
    hitting_set_singleton_universe_bounds(S, SS);
    var S':SetSet<int>; S' := S;
    var S'_empty:bool; S'_empty, counter := S'.IsEmpty(counter);

    ghost var loopBase := CostNew_SetFamily() + S.UCostContains() + CostNew_SetFamily() + S.CostIsEmpty();
    linear_loop_budget_zero(loopBase, CostAddSingletonSourceSet(U, S, k));
    while (!S'_empty)
      // Termination
      decreases S'.Cardinality()
      invariant S'_empty == (S'.Model() == {})
      // Types
      invariant U.Valid()
      invariant SS.Valid()
      invariant S'.UniverseWithin(S)
      invariant S.USize1() <= U.USize()
      invariant SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
      invariant SS.USize1() <= S.USize1()
      // Regular invariants
      invariant SS.Universe() == SS_universe
      invariant SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
      // Counter
      invariant counter <= LinearLoopBudget(loopBase, CostAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality())
    {
      linear_loop_budget_step(loopBase, CostAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality());
      S', SS, S'_empty, counter := AddSingletonSourceSet(U, S, k, S', SS, counter);
    }
    cost_branch_bounds(U, S, k);
    linear_loop_budget_bound(loopBase, CostAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality(), S.UCardinality());
    linear_loop_budget_transfer(counter, LinearLoopBudget(loopBase, CostAddSingletonSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()),
      loopBase + (S.UCardinality())*(CostAddSingletonSourceSet(U, S, k)), 0, CostTransformHittingSetToSetCover(U, S, k));
    assert SS.Model() == (set s | s in S.Model() :: {s});
    return (S, SS, 0), counter;
  }
  // Regular case
  ghost var SS_universe := (set u | u in U.Model() :: (set s | s in S.Model() && u in s));
  var SS:SetSetSet<int>; SS, counter := NewWithUniverse_SetSetSet(SS_universe, counter);
  hitting_set_incidence_universe_bounds(U, S, SS);
  var U':Set<int>; U' := U;
  var U'_empty:bool; U'_empty, counter := U'.IsEmpty(counter);
  ghost var loopBase := CostNew_SetFamily() + S.UCostContains() + CostNew_SetFamily() + U.CostIsEmpty();
  linear_loop_budget_zero(loopBase, CostBuildIncidenceSet(U, S, k));
  while (!U'_empty)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant SS.Valid()
    invariant U'.UniverseWithin(U)
    invariant SS.Cardinality() <= U.Cardinality() - U'.Cardinality()
    invariant SS.USize1() <= S.USize()
    // Regular invariants
    invariant SS.Universe() == SS_universe
    invariant SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, CostBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality())
  {
    linear_loop_budget_step(loopBase, CostBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality());
    U', SS, U'_empty, counter := BuildIncidenceSet(U, S, k, U', SS, counter);
  }
  cost_branch_bounds(U, S, k);
  linear_loop_budget_bound(loopBase, CostBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality(), U.UCardinality());
  linear_loop_budget_transfer(counter, LinearLoopBudget(loopBase, CostBuildIncidenceSet(U, S, k), U.Cardinality() - U'.Cardinality()),
    loopBase + (U.UCardinality())*(CostBuildIncidenceSet(U, S, k)), 0, CostTransformHittingSetToSetCover(U, S, k));
  set_difference_empty(U.Model(), U'.Model());

  return (S,SS,k),counter;
}


method BuildIncidenceSet(U:Set<int>, S:SetSet<int>, k:nat, U':Set<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (U'':Set<int>, SS':SetSetSet<int>, U''_empty:bool, ghost counter:nat)
  // Termination in
  requires U'.Model() != {}
  // Types in
  requires S.Init()
  requires SS.Valid()
  requires SS.Universe() == (set u | u in U.Model() :: (set s | s in S.Model() && u in s))
  requires U'.UniverseWithin(U)
  requires S.USize1() <= U.USize()
  requires SS.Cardinality() <= (U.Cardinality() - U'.Cardinality())
  requires SS.USize1() <= S.USize()
  // Invariant in
  requires SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
  // Termination out
  ensures U''_empty == (U''.Model() == {})
  ensures U''.Cardinality() == U'.Cardinality() - 1
  // Types out
  ensures SS'.Valid()
  ensures SS'.Universe() == SS.Universe()
  ensures U''.UniverseWithin(U)
  ensures SS'.Cardinality() <= (U.Cardinality() - U''.Cardinality())
  ensures SS'.USize1() <= S.USize()
  // Invariant out
  ensures SS'.Model() == (set u | u in (U.Model() - U''.Model()) :: (set s | s in S.Model() && u in s))
  // Counter
  ensures counter <= counter_in + CostBuildIncidenceSet(U, S, k)
{
  counter := counter_in;
  U'.universe_within_bound(U);
  var u:int; u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var sets_in_S_that_contain_u:SetSet<int>; sets_in_S_that_contain_u, counter := NewWithUniverse_SetSet(S.Model(), counter);
  reveal sets_in_S_that_contain_u.UCardinality1();
  var S':SetSet<int>; S' := S;
  var S'_empty; S'_empty, counter := S'.IsEmpty(counter);
  ghost var loopBase := counter_in + U.CostPick() + U.UCostRemove() + CostNew_SetFamily() +
    S.CostIsEmpty();
  linear_loop_budget_zero(loopBase, CostAddIncidentSourceSet(U, S, k));
  while (!S'_empty)
    // Termination
    decreases S'.Cardinality()
    invariant S'_empty == (S'.Model() == {})
    // Types
    invariant U.Valid()
    invariant S'.UniverseWithin(S)
    invariant sets_in_S_that_contain_u.UniverseWithin(S)
    invariant S.USize1() <= U.USize()
    // Regular invariants
    invariant sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, CostAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality())
  {
    linear_loop_budget_step(loopBase, CostAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality());
    S', sets_in_S_that_contain_u, S'_empty, counter := AddIncidentSourceSet(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  reveal CostBuildIncidenceSet();
  linear_loop_budget_bound(loopBase, CostAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality(), S.UCardinality());
  linear_loop_budget_transfer(counter, LinearLoopBudget(loopBase, CostAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()),
    loopBase + (S.UCardinality())*(CostAddIncidentSourceSet(U, S, k)), S.USize()*U.UCardinality() + 1 + U.CostIsEmpty(), counter_in + CostBuildIncidenceSet(U, S, k));
  sets_in_S_that_contain_u.universe_within_bound(S);
  assert sets_in_S_that_contain_u.Model() in SS.Universe() by {
    assert sets_in_S_that_contain_u.Model() == (set s | s in S.Model() && u in s);
    assert u in U.Model();
  }
  SS', counter := SS.Add(sets_in_S_that_contain_u, counter);
  reveal SS'.UCardinality1(), SS'.UCardinality2(), SS.UCardinality1(), SS.UCardinality2();

  U''_empty, counter := U''.IsEmpty(counter);
  nat_multiplication_monotonic(SS.Cardinality(), SS.Size1(), SS.USize1());
  nonnegative_product_monotonic(SS.Cardinality(), SS.USize1(), U.UCardinality(), S.USize());
  assert SS.CostAdd() <= S.USize()*U.UCardinality() + 1;
  calc <= {
    counter;
    LinearLoopBudget(loopBase, CostAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()) +
      SS.CostAdd() + U.CostIsEmpty();
    LinearLoopBudget(loopBase, CostAddIncidentSourceSet(U, S, k), S.Cardinality() - S'.Cardinality()) +
      S.USize()*U.UCardinality() + 1 + U.CostIsEmpty();
    counter_in + CostBuildIncidenceSet(U, S, k);
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
  requires S'.UniverseWithin(S)
  requires sets_in_S_that_contain_u.UniverseWithin(S)
  requires S.USize1() <= U.USize()
  // Invariant in
  requires sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
  // Termination out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Types out
  ensures sets_in_S_that_contain_u.USize() <= S.USize()
  ensures S''.UniverseWithin(S)
  ensures sets_in_S_that_contain_u'.UniverseWithin(S)
  // Invariant out
  ensures sets_in_S_that_contain_u'.Model() == (set s | s in (S.Model() - S''.Model()) && u in s)
  // Counter
  ensures counter <= counter_in + CostAddIncidentSourceSet(U, S, k)
{
  S'.universe_within_bound(S);
  sets_in_S_that_contain_u.universe_within_bound(S);
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);

  var s_contains_u:bool;
  s_contains_u, counter := s.Contains(u, counter);
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u'.Add(s, counter);
  }
  S''_empty, counter := S''.IsEmpty(counter);
  reveal CostAddIncidentSourceSet();
}


method {:isolate_assertions} AddSingletonSourceSet(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, SS':SetSetSet<int>, S''_empty:bool, ghost counter:nat)
  // Termination in
  requires S'.Model() != {}
  // Types in
  requires U.Valid()
  requires SS.Valid()
  requires SS.Universe() == (set s | s in S.Model() :: {s})
  requires S'.UniverseWithin(S)
  requires S.USize1() <= U.USize()
  requires SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
  requires SS.USize1() <= S.USize1()
  // Invariant in
  requires SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
  // Termination out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Types out
  ensures SS'.Valid()
  ensures SS'.Universe() == SS.Universe()
  ensures S''.UniverseWithin(S)
  ensures SS'.Cardinality() <= S.Cardinality() - S''.Cardinality()
  ensures SS'.USize1() <= S.USize1()
  // Invariant out
  ensures SS'.Model() == (set s | s in (S.Model() - S''.Model()) :: {s})
  // Counter
  ensures counter <= counter_in + CostAddSingletonSourceSet(U, S, k)
{
  S'.universe_within_bound(S);
  nonnegative_product_monotonic(SS.Cardinality(), SS.USize1(), S.Cardinality(), S.UCardinality1());
  counter := counter_in;
  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);
  var s_set:SetSet<int>; s_set, counter := NewWithUniverse_SetSet(S.Model(), counter);
  reveal s_set.UCardinality1();
  ghost var empty_s_set := s_set;
  s_set, counter := s_set.Add(s, counter);
  SS', counter := SS.Add(s_set, counter);
  reveal SS'.UCardinality1(), SS'.UCardinality2(), SS.UCardinality1(), SS.UCardinality2();
  S''_empty, counter := S''.IsEmpty(counter);
  nat_multiplication_monotonic(S.UCardinality1(), S.Cardinality(), S.UCardinality());
  nat_multiplication_monotonic(SS.Cardinality(), SS.Size1(), SS.USize1());
  calc <= {
    SS.CostAdd();
    SS.Cardinality()*SS.USize1() + 1;
    S.Cardinality()*S.UCardinality1() + 1;
    S.USize() + 1;
  }
}


lemma hitting_set_singleton_universe_bounds(S:SetSet<int>, SS:SetSetSet<int>)
  requires S.Valid() && SS.Valid()
  requires SS.Universe() == (set s | s in S.Model() :: {s})
  ensures SS.USize1() <= S.USize1()
  ensures SS.UCardinality1() <= 1
  ensures SS.UCardinality2() <= S.UCardinality1()
  ensures SS.USize2() <= S.USize1()
{
  forall child | child in SS.Universe()
    ensures |child| <= 1
    ensures MaxCardinality_set(child) <= S.USize1()
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
  ensures SS.USize1() <= S.USize()
  ensures SS.UCardinality1() <= S.UCardinality()
  ensures SS.UCardinality2() <= S.UCardinality1()
  ensures SS.USize2() <= S.USize1()
{
  forall child | child in SS.Universe()
    ensures |child| <= S.UCardinality()
    ensures MaxCardinality_set(child) <= S.USize1()
  {
    assert child <= S.Model();
    subset_cardinality_bound(child, S.Model());
    max_by_monotonic(child, S.Model(), item => |item|);
  }
  SS.u_cardinality1_bound(S.UCardinality());
  SS.u_cardinality2_bound(S.UCardinality1());
  nonnegative_product_monotonic(SS.UCardinality1(), SS.UCardinality2(), S.UCardinality(), S.UCardinality1());
}


ghost function {:opaque} CostAddIncidentSourceSet(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  S.UCostPick() +
  S.UCostRemove() + U.UCostContains() +
  S.UCostAdd() + S.CostIsEmpty()
}
ghost function {:opaque} CostBuildIncidenceSet(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  U.CostPick() + U.UCostRemove() + CostNew_SetFamily() +
  S.CostIsEmpty() +
  S.UCardinality()*CostAddIncidentSourceSet(U, S, k) +
  S.USize()*U.UCardinality() + 1 + U.CostIsEmpty()
}
ghost function CostAddSingletonSourceSet(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  S.UCostPick() + S.UCostRemove() +
  CostNew_SetFamily() + S.UCostAdd() +
  S.USize() + 1 + S.CostIsEmpty()
}

ghost function {:opaque} CostTransformHittingSetToSetCover(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  CostNew_SetFamily() + S.UCostContains() + CostNew_SetFamily() +
  S.CostIsEmpty() +
  S.UCardinality()*CostAddSingletonSourceSet(U, S, k) +
  CostNew_SetFamily() + S.UCostContains() + CostNew_SetFamily() +
  U.CostIsEmpty() +
  U.UCardinality()*CostBuildIncidenceSet(U, S, k)
}

ghost function PolynomialTransformHittingSetToSetCover(n:nat):nat
{
  (1 + (n*n + 1) + 1 + (n*n + 1) + 1 + n*(3*n*n + n + 6)) +
  (1 + (n*n + 1) + 1 + (n + 1) + 1 +
    n*(n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7))
}

lemma cost_branch_bounds(U:Set<int>, S:SetSet<int>, k:nat)
  ensures CostNew_SetFamily() + S.UCostContains() + CostNew_SetFamily() +
          S.CostIsEmpty() +
          S.UCardinality()*CostAddSingletonSourceSet(U, S, k) <= CostTransformHittingSetToSetCover(U, S, k)
  ensures CostNew_SetFamily() + S.UCostContains() + CostNew_SetFamily() +
          U.CostIsEmpty() +
          U.UCardinality()*CostBuildIncidenceSet(U, S, k) <= CostTransformHittingSetToSetCover(U, S, k)
{
  reveal CostTransformHittingSetToSetCover();
}

lemma {:isolate_assertions} cost_transform_hitting_set_to_set_cover_is_polynomial(U:Set<int>, S:SetSet<int>, k:nat)
  requires U.Init() && S.Init()
  requires S.USize1() <= U.USize()
  ensures CostTransformHittingSetToSetCover(U, S, k) <=
    PolynomialTransformHittingSetToSetCover(U.Cardinality() + S.Cardinality() + 1)
  ensures CostTransformHittingSetToSetCover(U, S, k) <= 50 * NatPower((U.Cardinality() + S.Cardinality() + 1)+1, 4)
{
  var n := U.Cardinality() + S.Cardinality() + 1;
  S.u_size_bound(n, n);
  assert S.UCostRemove() <= n*n + 1;
  assert S.UCostAdd() <= n*n + 1;
  assert S.UCostPick() <= n + 1;
  assert U.UCostRemove() <= n + 1;
  assert U.UCostContains() <= n + 1;
  multiplication_associative(3, n, n);
  assert CostAddSingletonSourceSet(U, S, k) <= 3*n*n + n + 6;
  assert CostAddIncidentSourceSet(U, S, k) <= 4*n*n + 5*n + 7 by {
    reveal CostAddIncidentSourceSet();
  }
  nonnegative_product_monotonic(S.UCardinality(), CostAddIncidentSourceSet(U, S, k), n, 4*n*n + 5*n + 7);
  nonnegative_product_monotonic(S.USize(), U.UCardinality(), n*n, n);
  assert CostBuildIncidenceSet(U, S, k) <=
    n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7 by {
    reveal CostBuildIncidenceSet();
  }

  nonnegative_product_monotonic(S.UCardinality(), CostAddSingletonSourceSet(U, S, k), n, 3*n*n + n + 6);
  nonnegative_product_monotonic(U.UCardinality(), CostBuildIncidenceSet(U, S, k), n,
    n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7);
  reveal CostTransformHittingSetToSetCover();
  assert CostTransformHittingSetToSetCover(U, S, k) <= PolynomialTransformHittingSetToSetCover(n);
  polynomial_transform_hitting_set_to_set_cover_bound();
}

// Uniform witness: these constants do not depend on the instance.
lemma polynomial_transform_hitting_set_to_set_cover_bound()
  ensures HasPolynomialBound((n:nat) => true, (n:nat) => n, PolynomialTransformHittingSetToSetCover, 50, 4)
  ensures IsPolynomial((n:nat) => true, (n:nat) => n, PolynomialTransformHittingSetToSetCover)
{
  forall n:nat
    ensures PolynomialTransformHittingSetToSetCover(n) <= 50 * NatPower(n+1, 4)
  {
    assert {:fuel NatPower, 5} PolynomialTransformHittingSetToSetCover(n) ==
      10*NatPower(n, 0) + 14*NatPower(n, 1) + 12*NatPower(n, 2) +
      9*NatPower(n, 3) + 5*NatPower(n, 4);
    weighted_monomial_bound(n, n, 0, 4, 10);
    weighted_monomial_bound(n, n, 1, 4, 14);
    weighted_monomial_bound(n, n, 2, 4, 12);
    weighted_monomial_bound(n, n, 3, 4, 9);
    weighted_monomial_bound(n, n, 4, 4, 5);
  }
  polynomial_witness((n:nat) => true, (n:nat) => n, PolynomialTransformHittingSetToSetCover, 50, 4);
}
