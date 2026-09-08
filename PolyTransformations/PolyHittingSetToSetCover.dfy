include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"
include "../Auxiliary/ConcreteSet.dfy"


method HittingSet_to_SetCover_Method(U:Set<int>, S:SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, nat), ghost counter:nat)
  requires HittingSetValidInstance(U.Model(), S.Model())
  requires init_Set(U)
  requires init_SetSet(S)
  requires S.UBSize1() <= U.UBSize0()
  ensures (r.0.Model(),r.1.Model(),r.2) == HittingSet_to_SetCover(U.Model(), S.Model(), k)
  ensures counter <= poly(U, S, k)
{
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
    var S':SetSet<int>; S', counter := S.Copy(counter);
    var S'_empty:bool; S'_empty, counter := S'.Empty(counter);

    branch_budget_zero(U, S, k, true);
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
      invariant counter <= branch_budget(U, S, k, true, S.Cardinality() - S'.Cardinality())
    {
      branch_budget_step(U, S, k, true, S.Cardinality() - S'.Cardinality());
      S', SS, S'_empty, counter := HittingSet_to_SetCover_edge_case_loop(U, S, k, S', SS, counter);
    }
    branch_budget_finish(U, S, k, true, S.Cardinality() - S'.Cardinality(), counter);
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
  var U':Set<int>; U', counter := U.Copy(counter);
  var U'_empty:bool; U'_empty, counter := U'.Empty(counter);
  branch_budget_zero(U, S, k, false);
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
    invariant counter <= branch_budget(U, S, k, false, U.Cardinality() - U'.Cardinality())
  {
    branch_budget_step(U, S, k, false, U.Cardinality() - U'.Cardinality());
    U', SS, U'_empty, counter := HittingSet_to_SetCover_outer_loop(U, S, k, U', SS, counter);
  }
  branch_budget_finish(U, S, k, false, U.Cardinality() - U'.Cardinality(), counter);
  identity_substraction_lemma(U.Model(), U'.Model());

  return (S,SS,k),counter;
}


method HittingSet_to_SetCover_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, U':Set<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (U'':Set<int>, SS':SetSetSet<int>, U''_empty:bool, ghost counter:nat)
  // Termination in
  requires U'.Model() != {}
  // Types in
  requires S.Valid()
  requires SS.Valid()
  requires in_universe_Set(U', U)
  requires S.UBSize1() <= U.UBSize0()
  requires SS.Cardinality() <= (U.Cardinality() - U'.Cardinality())
  requires SS.UBSize1() <= S.UBSize0()
  // Invariant in
  requires SS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
  // Termination out
  ensures U''.Cardinality() == U'.Cardinality() - 1
  ensures U''_empty == (U''.Model() == {})
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
  var S'; S', counter := S.Copy(counter);
  var S'_empty; S'_empty, counter := S'.Empty(counter);
  outer_budget_zero(U, S, k, counter_in);
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
    invariant counter <= outer_budget(U, S, k, counter_in, S.Cardinality() - S'.Cardinality())
  {
    outer_budget_step(U, S, k, counter_in, S.Cardinality() - S'.Cardinality());
    S', sets_in_S_that_contain_u, S'_empty, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  outer_budget_finish(U, S, k, counter_in, S.Cardinality() - S'.Cardinality());
  in_universe_lemma_SetSet(sets_in_S_that_contain_u, S);
  SS', counter := SS.Add(sets_in_S_that_contain_u, counter);

  U''_empty, counter := U''.Empty(counter);
  mult_preserves_order(SS.Cardinality(), SS.UBSize1(), U.UBCardinality(), S.UBSize0());
  assert cost_SetSetSetAdd(SS) <= S.UBSize0()*U.UBCardinality() + 1;
  calc <= {
    counter;
    outer_budget(U, S, k, counter_in, S.Cardinality() - S'.Cardinality()) +
      cost_SetSetSetAdd(SS) + cost_SetEmpty(U);
    outer_budget(U, S, k, counter_in, S.Cardinality() - S'.Cardinality()) +
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
  ensures sets_in_S_that_contain_u.UBSize0() <= S.UBSize0()
  // Invariant in
  requires sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
  // Termination out
  ensures S''.Cardinality() == S'.Cardinality() - 1
  ensures S''_empty == (S''.Model() == {})
  // Types out
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
  sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u.Copy(counter);

  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);

  var s_contains_u:bool := false;
  var s':Set<int>; s', counter := s.Copy(counter);
  var s'_empty:bool; s'_empty, counter := s'.Empty(counter);
  middle_budget_zero(U, S, k, counter_in);
  while (!s'_empty)
    // Termination
    decreases s'.Cardinality()
    invariant s'_empty == (s'.Model() == {})
    // Types
    invariant s'.Valid()
    invariant in_universe_Set(s', s)
    invariant s.Cardinality() <= S.UBSize1()
    invariant S.UBSize1() <= U.UBSize0()
    // Regular invariants
    invariant s_contains_u == (u in (s.Model() - s'.Model()))
    // Counter
    invariant counter <= middle_budget(U, S, k, counter_in, s.Cardinality() - s'.Cardinality())
  {
    middle_budget_step(U, S, k, counter_in, s.Cardinality() - s'.Cardinality());
    s', s_contains_u, s'_empty, counter := HittingSet_to_SetCover_inner_loop(U, S, k, s, s', u, s_contains_u, counter);
  }
  middle_budget_finish(U, S, k, counter_in, s.Cardinality() - s'.Cardinality());
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u.Add(s, counter);
  }
  S''_empty, counter := S''.Empty(counter);
}


method HittingSet_to_SetCover_inner_loop(U:Set<int>, S:SetSet<int>, k:nat, s:Set<int>, s':Set<int>, u:int, s_contains_u:bool, ghost counter_in:nat) returns (s'':Set<int>, s_contains_u':bool, s''_empty:bool, ghost counter:nat)
  // Termination in
  requires s'.Model() != {}
  // Types in
  requires U.Valid()
  requires S.Valid()
  requires in_universe_Set(s', s)
  requires s.Cardinality() <= S.UBSize1()
  requires S.UBSize1() <= U.UBSize0()
  // Invariant in
  requires s_contains_u == (u in (s.Model() - s'.Model()))
  // Termination out
  ensures s''.Cardinality() == s'.Cardinality() - 1
  ensures s''_empty == (s''.Model() == {})
  // Types out
  ensures s''.Valid()
  ensures in_universe_Set(s'', s)
  // Invariant out
  ensures s_contains_u' == (u in (s.Model() - s''.Model()))
  // Counter
  ensures counter <= counter_in + poly_inner_loop(U, S, k)
{
  if_smaller_then_less_cardinality(s'.Universe(), s.Model());
  counter := counter_in;
  s_contains_u' := s_contains_u;
  var e:int; e, counter := s'.Pick(counter);
  s'', counter := s'.Remove(e, counter);
  if (e == u) {
    s_contains_u' := true;
  }
  s''_empty, counter := s''.Empty(counter);
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
  ensures S''.Cardinality() == S'.Cardinality() - 1
  ensures S''_empty == (S''.Model() == {})
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


lemma counter_simplification_aux_1(U: Set<int>, S: SetSet<int>, k: nat, S'_prev: SetSet<int>, S': SetSet<int>)
  requires S'_prev.Cardinality() == S'.Cardinality() + 1
  ensures cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
          cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S) +
          (S.Cardinality() - S'_prev.Cardinality())*poly_middle_loop(U, S, k) + poly_middle_loop(U, S, k) ==
          cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
          cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S) +
          (S.Cardinality() - S'.Cardinality())*poly_middle_loop(U, S, k)
{}


ghost function {:opaque} poly_inner_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures o == cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_SetEmpty(U)
{
  cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_SetEmpty(U)
}
ghost function {:opaque} poly_middle_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  cost_SetSetCopyUniverse(S) + cost_SetSetPickUniverse(S) +
  cost_SetSetRemoveUniverse(S) + cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
  U.UBCardinality()*poly_inner_loop(U, S, k) +
  cost_SetSetAddUniverse(S) + cost_SetSetEmpty(S)
}
ghost function {:opaque} poly_outer_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
  cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S) +
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
  cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S) +
  S.UBCardinality()*poly_edge_case_loop(U, S, k) +
  cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
  cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
  U.UBCardinality()*poly_outer_loop(U, S, k)
}


ghost function {:opaque} middle_budget(U:Set<int>, S:SetSet<int>, k:nat, start:nat, visited:nat):nat
{
  start + cost_SetSetCopyUniverse(S) + cost_SetSetPickUniverse(S) +
  cost_SetSetRemoveUniverse(S) + cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
  visited*poly_inner_loop(U, S, k)
}

lemma middle_budget_zero(U:Set<int>, S:SetSet<int>, k:nat, start:nat)
  ensures middle_budget(U, S, k, start, 0) ==
    start + cost_SetSetCopyUniverse(S) + cost_SetSetPickUniverse(S) +
    cost_SetSetRemoveUniverse(S) + cost_SetCopyUniverse(U) + cost_SetEmpty(U)
{
  reveal middle_budget();
}

lemma middle_budget_step(U:Set<int>, S:SetSet<int>, k:nat, start:nat, visited:nat)
  ensures middle_budget(U, S, k, start, visited + 1) ==
          middle_budget(U, S, k, start, visited) + poly_inner_loop(U, S, k)
{
  reveal middle_budget();
}

lemma middle_budget_finish(U:Set<int>, S:SetSet<int>, k:nat, start:nat, visited:nat)
  requires visited <= U.UBCardinality()
  ensures middle_budget(U, S, k, start, visited) +
          cost_SetSetAddUniverse(S) + cost_SetSetEmpty(S)
          <= start + poly_middle_loop(U, S, k)
{
  reveal middle_budget();
  poly_middle_loop_definition(U, S, k);
  mult_preserves_order(visited, poly_inner_loop(U, S, k), U.UBCardinality(), poly_inner_loop(U, S, k));
}

ghost function {:opaque} outer_budget(U:Set<int>, S:SetSet<int>, k:nat, start:nat, visited:nat):nat
{
  start + cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
  cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S) + visited*poly_middle_loop(U, S, k)
}

lemma outer_budget_zero(U:Set<int>, S:SetSet<int>, k:nat, start:nat)
  ensures outer_budget(U, S, k, start, 0) ==
    start + cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
    cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S)
{
  reveal outer_budget();
}

lemma outer_budget_step(U:Set<int>, S:SetSet<int>, k:nat, start:nat, visited:nat)
  ensures outer_budget(U, S, k, start, visited + 1) ==
          outer_budget(U, S, k, start, visited) + poly_middle_loop(U, S, k)
{
  reveal outer_budget();
}

lemma outer_budget_finish(U:Set<int>, S:SetSet<int>, k:nat, start:nat, visited:nat)
  requires visited <= S.UBCardinality()
  ensures outer_budget(U, S, k, start, visited) +
          S.UBSize0()*U.UBCardinality() + 1 + cost_SetEmpty(U) <= start + poly_outer_loop(U, S, k)
{
  reveal outer_budget();
  poly_outer_loop_definition(U, S, k);
  mult_preserves_order(visited, poly_middle_loop(U, S, k), S.UBCardinality(), poly_middle_loop(U, S, k));
}

lemma poly_middle_loop_definition(U:Set<int>, S:SetSet<int>, k:nat)
  ensures poly_middle_loop(U, S, k) ==
    cost_SetSetCopyUniverse(S) + cost_SetSetPickUniverse(S) +
    cost_SetSetRemoveUniverse(S) + cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
    U.UBCardinality()*poly_inner_loop(U, S, k) +
    cost_SetSetAddUniverse(S) + cost_SetSetEmpty(S)
{
  reveal poly_middle_loop();
}

lemma poly_outer_loop_definition(U:Set<int>, S:SetSet<int>, k:nat)
  ensures poly_outer_loop(U, S, k) ==
    cost_SetPick(U) + cost_SetRemoveUniverse(U) + cost_NewSetSet() +
    cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S) +
    S.UBCardinality()*poly_middle_loop(U, S, k) +
    S.UBSize0()*U.UBCardinality() + 1 + cost_SetEmpty(U)
{
  reveal poly_outer_loop();
}

ghost function {:opaque} branch_budget(U:Set<int>, S:SetSet<int>, k:nat, edge:bool, visited:nat):nat
{
  cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
  (if edge then cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S)
           else cost_SetCopyUniverse(U) + cost_SetEmpty(U)) +
  visited*(if edge then poly_edge_case_loop(U, S, k) else poly_outer_loop(U, S, k))
}

lemma branch_budget_zero(U:Set<int>, S:SetSet<int>, k:nat, edge:bool)
  ensures branch_budget(U, S, k, edge, 0) ==
    cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
    (if edge then cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S)
             else cost_SetCopyUniverse(U) + cost_SetEmpty(U))
{
  reveal branch_budget();
}

lemma branch_budget_step(U:Set<int>, S:SetSet<int>, k:nat, edge:bool, visited:nat)
  ensures branch_budget(U, S, k, edge, visited + 1) ==
          branch_budget(U, S, k, edge, visited) +
          (if edge then poly_edge_case_loop(U, S, k) else poly_outer_loop(U, S, k))
{
  reveal branch_budget();
}

lemma branch_budget_finish(U:Set<int>, S:SetSet<int>, k:nat, edge:bool, visited:nat, spent:nat)
  requires visited <= (if edge then S.UBCardinality() else U.UBCardinality())
  requires spent <= branch_budget(U, S, k, edge, visited)
  ensures branch_budget(U, S, k, edge, visited) <= poly(U, S, k)
  ensures spent <= poly(U, S, k)
{
  reveal branch_budget();
  poly_branch_bounds(U, S, k);
  if edge {
    mult_preserves_order(visited, poly_edge_case_loop(U, S, k),
                         S.UBCardinality(), poly_edge_case_loop(U, S, k));
  } else {
    mult_preserves_order(visited, poly_outer_loop(U, S, k),
                         U.UBCardinality(), poly_outer_loop(U, S, k));
  }
}

lemma poly_branch_bounds(U:Set<int>, S:SetSet<int>, k:nat)
  ensures cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
          cost_SetSetCopyUniverse(S) + cost_SetSetEmpty(S) +
          S.UBCardinality()*poly_edge_case_loop(U, S, k) <= poly(U, S, k)
  ensures cost_NewSet() + cost_SetSetContainsUniverse(S) + cost_NewSetSetSet() +
          cost_SetCopyUniverse(U) + cost_SetEmpty(U) +
          U.UBCardinality()*poly_outer_loop(U, S, k) <= poly(U, S, k)
{
  reveal poly();
}
