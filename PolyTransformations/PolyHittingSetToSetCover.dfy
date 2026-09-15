include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/ConcreteSet.dfy"


method HittingSet_to_SetCover_Method(U:Set<int>, S:SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, nat), ghost counter:nat)
  // Types in
  requires HittingSetValidInstance(U.Model(), S.Model())
  requires init_Set(U) && init_SetSet(S)
  requires S.UBSize1() <= U.UBSize0()
  // Invariant out
  ensures (r.0.Model(),r.1.Model(),r.2) == HittingSet_to_SetCover(U.Model(), S.Model(), k)
  // Counter
  ensures counter <= HittingSetToSetCoverPolynomial(U.Cardinality() + S.Cardinality() + 1)
{
  HittingSetToSetCoverCostBound(U, S, k);
  counter := 0;
  // Edge case
  var empty_set:Set<int>; empty_set, counter := New_Set(counter);
  var S_contains_empty:bool; S_contains_empty, counter := S.Contains(empty_set, counter);
  if (S_contains_empty) {

    ghost var SS_universe := (set s | s in S.Model() :: {s});
    assert forall u | u in SS_universe :: |u| == 1;
    assert forall u | u in SS_universe :: forall u' | u' in u :: |u'| <= S.UBSize1();
    assert forall u | u in SS_universe :: |u|*S.UBSize1() <= S.UBSize1();
    var SS:SetSetSet<int>; SS, counter := New_SetSetSet_params(SS_universe, S.UBSize1(), S.UBSize1(), counter);
    var S':SetSet<int>; S' := S;
    var S'_empty:bool; S'_empty, counter := S'.Empty(counter);

    ghost var loopBase := cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
      cost_SetSetEmpty(S);
    LinearLoopBudgetZero(loopBase, poly_edge_case_loop(U, S, k));
    while (!S'_empty)
      // Termination
      decreases S'.Cardinality()
      invariant S'_empty == (S'.Model() == {})
      // Types
      invariant U.Valid()
      invariant SS.Valid()
      invariant in_universe_SetSet(S', S)
      invariant S.UBSize1() <= U.UBSize0()
      invariant SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
      invariant SS.UBSize1() <= S.UBSize1()
      // Regular invariants
      invariant SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
      // Counter
      invariant counter <= LinearLoopBudget(loopBase, poly_edge_case_loop(U, S, k), S.Cardinality() - S'.Cardinality())
    {
      LinearLoopBudgetStep(loopBase, poly_edge_case_loop(U, S, k), S.Cardinality() - S'.Cardinality());
      S', SS, S'_empty, counter := HittingSet_to_SetCover_edge_case_loop(U, S, k, S', SS, counter);
    }
    poly_branch_bounds(U, S, k);
    LinearLoopBudgetBound(loopBase, poly_edge_case_loop(U, S, k), S.Cardinality() - S'.Cardinality(), S.UBCardinality());
    LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, poly_edge_case_loop(U, S, k), S.Cardinality() - S'.Cardinality()),
      loopBase + (S.UBCardinality())*(poly_edge_case_loop(U, S, k)), 0, poly(U, S, k));
    assert SS.Model() == (set s | s in S.Model() :: {s});
    return (S, SS, 0), counter;
  }
  // Regular case
  ghost var SS_universe := (set u | u in U.Model() :: (set s | s in S.Model() && u in s));
  assert forall u | u in SS_universe :: |u| <= S.Cardinality() by {
    assert forall u | u in SS_universe :: u <= S.Model();
    for_all_if_smaller_then_less_cardinality(SS_universe, S.Model());
  }
  assert forall u | u in SS_universe :: |u|*S.UBSize1() <= S.UBSize0();
  var SS:SetSetSet<int>; SS, counter := New_SetSetSet_params(SS_universe, S.UBSize0(), S.UBSize1(), counter);
  var U':Set<int>; U' := U;
  var U'_empty:bool; U'_empty, counter := U'.Empty(counter);
  ghost var loopBase := cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
      cost_SetEmpty(U);
  LinearLoopBudgetZero(loopBase, poly_outer_loop(U, S, k));
  while (!U'_empty)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant SS.Valid()
    invariant in_universe_Set(U', U)
    invariant SS.Cardinality() <= U.Cardinality() - U'.Cardinality()
    invariant SS.UBSize1() <= S.UBSize0()
    // Regular invariants
    invariant SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, poly_outer_loop(U, S, k), U.Cardinality() - U'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, poly_outer_loop(U, S, k), U.Cardinality() - U'.Cardinality());
    U', SS, U'_empty, counter := HittingSet_to_SetCover_outer_loop(U, S, k, U', SS, counter);
  }
  poly_branch_bounds(U, S, k);
  LinearLoopBudgetBound(loopBase, poly_outer_loop(U, S, k), U.Cardinality() - U'.Cardinality(), U.UBCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, poly_outer_loop(U, S, k), U.Cardinality() - U'.Cardinality()),
    loopBase + (U.UBCardinality())*(poly_outer_loop(U, S, k)), 0, poly(U, S, k));
  identity_substraction_lemma(U.Model(), U'.Model());

  return (S,SS,k),counter;
}


method HittingSet_to_SetCover_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, U':Set<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (U'':Set<int>, SS':SetSetSet<int>, U''_empty:bool, ghost counter:nat)
  // Termination in
  requires U'.Model() != {}
  // Types in
  requires init_SetSet(S)
  requires SS.Valid()
  requires in_universe_Set(U', U)
  requires S.UBSize1() <= U.UBSize0()
  requires SS.Cardinality() <= (U.Cardinality() - U'.Cardinality())
  requires SS.UBSize1() <= S.UBSize0()
  // Invariant in
  requires SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
  // Termination out
  ensures U''_empty == (U''.Model() == {})
  ensures U''.Cardinality() == U'.Cardinality() - 1
  // Types out
  ensures SS'.Valid()
  ensures in_universe_Set(U'', U)
  ensures SS'.Cardinality() <= (U.Cardinality() - U''.Cardinality())
  ensures SS'.UBSize1() <= S.UBSize0()
  // Invariant out
  ensures SS'.Model() == (set u | u in (U.Model() - U''.Model()) :: (set s | s in S.Model() && u in s))
  // Counter
  ensures counter <= counter_in + poly_outer_loop(U, S, k)
{
  counter := counter_in;
  in_universe_lemma_Set(U', U);
  var u:int; u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var sets_in_S_that_contain_u:SetSet<int>; sets_in_S_that_contain_u, counter := New_SetSet_params(S.Model(), S.UBSize1(), counter);
  var S'; S' := S;
  var S'_empty; S'_empty, counter := S'.Empty(counter);
  ghost var loopBase := counter_in + cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
    cost_SetSetEmpty(S);
  LinearLoopBudgetZero(loopBase, poly_middle_loop(U, S, k));
  while (!S'_empty)
    // Termination
    decreases S'.Cardinality()
    invariant S'_empty == (S'.Model() == {})
    // Types
    invariant U.Valid()
    invariant in_universe_SetSet(S', S)
    invariant in_universe_SetSet(sets_in_S_that_contain_u, S)
    invariant S.UBSize1() <= U.UBSize0()
    // Regular invariants
    invariant sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
    // Counter
    invariant counter <= LinearLoopBudget(loopBase, poly_middle_loop(U, S, k), S.Cardinality() - S'.Cardinality())
  {
    LinearLoopBudgetStep(loopBase, poly_middle_loop(U, S, k), S.Cardinality() - S'.Cardinality());
    S', sets_in_S_that_contain_u, S'_empty, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  poly_outer_loop_definition(U, S, k);
  LinearLoopBudgetBound(loopBase, poly_middle_loop(U, S, k), S.Cardinality() - S'.Cardinality(), S.UBCardinality());
  LinearLoopBudgetTransfer(counter, LinearLoopBudget(loopBase, poly_middle_loop(U, S, k), S.Cardinality() - S'.Cardinality()),
    loopBase + (S.UBCardinality())*(poly_middle_loop(U, S, k)), S.UBSize0()*U.UBCardinality() + 1 + cost_SetEmpty(U), counter_in + poly_outer_loop(U, S, k));
  in_universe_lemma_SetSet(sets_in_S_that_contain_u, S);
  SS', counter := SS.Add(sets_in_S_that_contain_u, counter);

  U''_empty, counter := U''.Empty(counter);
  mult_preserves_order(SS.Cardinality(), SS.UBSize1(), U.UBCardinality(), S.UBSize0());
  assert cost_SetSetSetAdd(SS) <= S.UBSize0()*U.UBCardinality() + 1;
  calc <= {
    counter;
    LinearLoopBudget(loopBase, poly_middle_loop(U, S, k), S.Cardinality() - S'.Cardinality()) +
      cost_SetSetSetAdd(SS) + cost_SetEmpty(U);
    LinearLoopBudget(loopBase, poly_middle_loop(U, S, k), S.Cardinality() - S'.Cardinality()) +
      S.UBSize0()*U.UBCardinality() + 1 + cost_SetEmpty(U);
    counter_in + poly_outer_loop(U, S, k);
  }
  assert SS'.Model() == (set v | v in (U.Model() - U''.Model()) :: (set s | s in S.Model() && v in s)) by {
    assert (S.Model() - S'.Model()) == S.Model();
    assert SS'.Model() == (set v | v in (U.Model() - U'.Model()) + {u} :: (set s | s in S.Model() && v in s));
    assert (U.Model() - U''.Model()) == (U.Model() - U'.Model()) + {u};
  }
}


method HittingSet_to_SetCover_middle_loop(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, u:int, sets_in_S_that_contain_u:SetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, sets_in_S_that_contain_u':SetSet<int>, S''_empty:bool, ghost counter:nat)
  // Termination in
  requires S'.Model() != {}
  // Types in
  requires U.Valid()
  requires in_universe_SetSet(S', S)
  requires in_universe_SetSet(sets_in_S_that_contain_u, S)
  requires S.UBSize1() <= U.UBSize0()
  // Invariant in
  requires sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
  // Termination out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Types out
  ensures sets_in_S_that_contain_u.UBSize0() <= S.UBSize0()
  ensures in_universe_SetSet(S'', S)
  ensures in_universe_SetSet(sets_in_S_that_contain_u', S)
  // Invariant out
  ensures sets_in_S_that_contain_u'.Model() == (set s | s in (S.Model() - S''.Model()) && u in s)
  // Counter
  ensures counter <= counter_in + poly_middle_loop(U, S, k)
{
  in_universe_lemma_SetSet(S', S);
  in_universe_lemma_SetSet(sets_in_S_that_contain_u, S);
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);

  var s_contains_u:bool;
  s_contains_u, counter := s.Contains(u, counter);
  poly_middle_loop_definition(U, S, k);
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u'.Add(s, counter);
  }
  S''_empty, counter := S''.Empty(counter);
}


method {:isolate_assertions} HittingSet_to_SetCover_edge_case_loop(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, SS':SetSetSet<int>, S''_empty:bool, ghost counter:nat)
  // Termination in
  requires S'.Model() != {}
  // Types in
  requires U.Valid()
  requires SS.Valid()
  requires in_universe_SetSet(S', S)
  requires S.UBSize1() <= U.UBSize0()
  requires SS.Cardinality() <= S.Cardinality() - S'.Cardinality()
  requires SS.UBSize1() <= S.UBSize1()
  // Invariant in
  requires SS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
  // Termination out
  ensures S''_empty == (S''.Model() == {})
  ensures S''.Cardinality() == S'.Cardinality() - 1
  // Types out
  ensures SS'.Valid()
  ensures in_universe_SetSet(S'', S)
  ensures SS'.Cardinality() <= S.Cardinality() - S''.Cardinality()
  ensures SS'.UBSize1() <= S.UBSize1()
  // Invariant out
  ensures SS'.Model() == (set s | s in (S.Model() - S''.Model()) :: {s})
  // Counter
  ensures counter <= counter_in + poly_edge_case_loop(U, S, k)
{
  in_universe_lemma_SetSet(S', S);
  mult_preserves_order(SS.Cardinality(), SS.UBSize1(), S.Cardinality(), S.UBSize1());
  counter := counter_in;
  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);
  var s_set:SetSet<int>; s_set, counter := New_SetSet_params(S.Model(), S.UBSize1(), counter);
  ghost var empty_s_set := s_set;
  s_set, counter := s_set.Add(s, counter);
  SS', counter := SS.Add(s_set, counter);
  S''_empty, counter := S''.Empty(counter);
  SetSetModelSizeBound(S);
  calc <= {
    cost_SetSetSetAdd(SS);
    SS.Cardinality()*SS.UBSize1() + 1;
    S.Cardinality()*S.UBSize1() + 1;
    S.Size0() + 1;
    S.UBSize0() + 1;
  }
  calc <= {
    counter;
    counter_in + cost_SetSetPickUniverse(S) + cost_SetSetRemoveUniverse(S) +
      cost_NewSetSet() + cost_SetSetAdd(empty_s_set) +
      cost_SetSetSetAdd(SS) + cost_SetSetEmpty(S);
    counter_in + poly_edge_case_loop(U, S, k);
  }
}


ghost function {:opaque} poly_middle_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  cost_SetSetPickUniverse(S) +
  cost_SetSetRemoveUniverse(S) + cost_SetContainsUniverse(U) +
  cost_SetSetAddUniverse(S) + cost_SetSetEmpty(S)
}
ghost function {:opaque} poly_outer_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
  cost_SetSetEmpty(S) +
  S.UBCardinality()*poly_middle_loop(U, S, k) +
  S.UBSize0()*U.UBCardinality() + 1 + cost_SetEmpty(U)
}
ghost function {:opaque} poly_edge_case_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures o == cost_SetSetPickUniverse(S) + cost_SetSetRemoveUniverse(S) +
               cost_NewSetSet() + cost_SetSetAddUniverse(S) +
               S.UBSize0() + 1 + cost_SetSetEmpty(S)
{
  cost_SetSetPickUniverse(S) + cost_SetSetRemoveUniverse(S) +
  cost_NewSetSet() + cost_SetSetAddUniverse(S) +
  S.UBSize0() + 1 + cost_SetSetEmpty(S)
}


ghost function {:opaque} poly(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
  cost_SetSetEmpty(S) +
  S.UBCardinality()*poly_edge_case_loop(U, S, k) +
  cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
  cost_SetEmpty(U) +
  U.UBCardinality()*poly_outer_loop(U, S, k)
}


ghost function HittingSetToSetCoverPolynomial(n:nat):nat
{
  (1 + (n*n + 1) + 1 + (n*n + 1) + 1 + n*(3*n*n + n + 6)) +
  (1 + (n*n + 1) + 1 + (n + 1) + 1 +
    n*(n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7))
}


lemma poly_middle_loop_definition(U:Set<int>, S:SetSet<int>, k:nat)
  ensures poly_middle_loop(U, S, k) ==
    cost_SetSetPickUniverse(S) +
    cost_SetSetRemoveUniverse(S) + cost_SetContainsUniverse(U) +
    cost_SetSetAddUniverse(S) + cost_SetSetEmpty(S)
{
  reveal poly_middle_loop();
}

lemma poly_outer_loop_definition(U:Set<int>, S:SetSet<int>, k:nat)
  ensures poly_outer_loop(U, S, k) ==
    cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
    cost_SetSetEmpty(S) +
    S.UBCardinality()*poly_middle_loop(U, S, k) +
    S.UBSize0()*U.UBCardinality() + 1 + cost_SetEmpty(U)
{
  reveal poly_outer_loop();
}

lemma poly_branch_bounds(U:Set<int>, S:SetSet<int>, k:nat)
  ensures cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
          cost_SetSetEmpty(S) +
          S.UBCardinality()*poly_edge_case_loop(U, S, k) <= poly(U, S, k)
  ensures cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
          cost_SetEmpty(U) +
          U.UBCardinality()*poly_outer_loop(U, S, k) <= poly(U, S, k)
{
  reveal poly();
}


lemma HittingSetToSetCoverCostBound(U:Set<int>, S:SetSet<int>, k:nat)
  requires init_Set(U) && init_SetSet(S)
  requires S.UBSize1() <= U.UBSize0()
  ensures poly(U, S, k) <=
    HittingSetToSetCoverPolynomial(U.Cardinality() + S.Cardinality() + 1)
{
  var n := U.Cardinality() + S.Cardinality() + 1;
  assert U.UBCardinality() <= n;
  assert U.UBSize0() <= n;
  assert S.UBCardinality() <= n;
  assert S.UBSize1() <= n;
  SetSetUniverseSizeBound(S, n, n);

  assert cost_SetSetContainsUniverse(S) <= n*n + 1;
  assert cost_SetSetRemoveUniverse(S) <= n*n + 1;
  assert cost_SetSetAddUniverse(S) <= n*n + 1;
  assert cost_SetSetPickUniverse(S) <= n + 1;
  assert cost_SetRemoveUniverse(U) <= n + 1;

  reveal poly_edge_case_loop();
  calc <= {
    poly_edge_case_loop(U, S, k);
    (n + 1) + (n*n + 1) + 1 + (n*n + 1) + (n*n + 1) + 1;
    3*n*n + n + 6;
  }

  poly_middle_loop_definition(U, S, k);
  calc <= {
    poly_middle_loop(U, S, k);
    (n + 1) + (n*n + 1) + (n + 1) + (n*n + 1) + 1;
    2*n*n + 2*n + 5;
    3*n*n + 5*n + 6;
    4*n*n + 5*n + 7;
  }

  poly_outer_loop_definition(U, S, k);
  mult_preserves_order(S.UBCardinality(), poly_middle_loop(U, S, k), n, 4*n*n + 5*n + 7);
  mult_preserves_order(S.UBSize0(), U.UBCardinality(), n*n, n);
  calc <= {
    poly_outer_loop(U, S, k);
    1 + (n + 1) + 1 + 1 +
      n*(4*n*n + 5*n + 7) + n*n*n + 1 + 1;
    n + n*(4*n*n + 5*n + 7) + n*n*n + 6;
    n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7;
  }

  mult_preserves_order(S.UBCardinality(), poly_edge_case_loop(U, S, k), n, 3*n*n + n + 6);
  mult_preserves_order(U.UBCardinality(), poly_outer_loop(U, S, k), n,
    n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7);
  reveal poly();
  calc <= {
    poly(U, S, k);
    (1 + (n*n + 1) + 1 + 1 + n*(3*n*n + n + 6)) +
      (1 + (n*n + 1) + 1 + 1 +
        n*(n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7));
    (1 + (n*n + 1) + 1 + (n*n + 1) + 1 + n*(3*n*n + n + 6)) +
      (1 + (n*n + 1) + 1 + (n + 1) + 1 +
        n*(n + n*n + n*(4*n*n + 5*n + 7) + n*n*n + 7));
    HittingSetToSetCoverPolynomial(n);
  }
}
