include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method HittingSet_to_SetCover_Method(U:Set<int>, S:SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, nat), ghost counter:nat)
  requires forall s | s in S.Model() ::  s <= U.Model()
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
    var SS:SetSetSet<int>; SS, counter := New_SetSetSet_params((set s | s in S.Model() :: {s}), S.UBSize1(), U.UBSize0(), counter);
    var S':SetSet<int>; S', counter := S.Copy(counter);
    var S'_empty:bool; S'_empty, counter := S'.Empty(counter);

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
      invariant counter <= 2*S.UBSize0() + 3 + (S.Cardinality() - S'.Cardinality())*(poly_edge_case_loop(U, S, k))
    {
      ghost var prevS' := S';
      S', SS, S'_empty, counter := HittingSet_to_SetCover_edge_case_loop(U, S, k, S', SS, counter);
      assert counter <= 2*S.UBSize0() + 3 + (S.Cardinality() - prevS'.Cardinality())*(poly_edge_case_loop(U, S, k)) + poly_edge_case_loop(U, S, k);
      calc == {
        (S.Cardinality() - prevS'.Cardinality())*(poly_edge_case_loop(U, S, k)) + poly_edge_case_loop(U, S, k);
        (S.Cardinality() - prevS'.Cardinality() + 1)*(poly_edge_case_loop(U, S, k));
        (S.Cardinality() - S'.Cardinality())*(poly_edge_case_loop(U, S, k));
      }
    }
    assert SS.Model() == (set s | s in S.Model() :: {s});
    assert (S.Model(), SS.Model(), 0) == HittingSet_to_SetCover(U.Model(), S.Model(), k);
    return (S, SS, 0), counter;
  }
  // Regular case
  var SS:SetSetSet<int>; SS, counter := New_SetSetSet_params((set u | u in U.Model() :: (set s | s in S.Model() && u in s)), S.UBSize0(), U.UBSize0(), counter);
  var U':Set<int>; U', counter := U.Copy(counter);
  var U'_empty:bool; U'_empty, counter := U'.Empty(counter);
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
    invariant counter <= S.UBSize0() + U.UBSize0() + 3 + (U.Cardinality() - U'.Cardinality())*poly_outer_loop(U, S, k)
  {
    U', SS, U'_empty, counter := HittingSet_to_SetCover_outer_loop(U, S, k, U', SS, counter);
  }
  assert counter <= S.UBSize0() + U.UBSize0() + 3 + U.Cardinality()*poly_outer_loop(U, S, k);
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
    invariant counter <= counter_in + S.UBSize0() + U.UBSize0() + 3 + (S.Cardinality() - S'.Cardinality())*(poly_middle_loop(U, S, k))
  {
    ghost var S'_prev := S';
    S', sets_in_S_that_contain_u, S'_empty, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
    counter_simplification_aux_1(U, S, k, S'_prev, S');
  }
  in_universe_lemma_SetSet(sets_in_S_that_contain_u, S);
  SS', counter := SS.Add(sets_in_S_that_contain_u, counter);

  U''_empty, counter := U''.Empty(counter);
  mult_preserves_order(SS.Cardinality(), SS.UBSize1(), U.Cardinality(), S.UBSize0());
  assert SS'.Model() == (set v | v in (U.Model() - U''.Model()) :: (set s | s in S.Model() && v in s)) by {
    assert SS'.Model() == (set v | v in (U.Model() - U'.Model()) :: (set s | s in S.Model() && v in s)) + {sets_in_S_that_contain_u.Model()};
    assert SS'.Model() == (set v | v in (U.Model() - U'.Model()) :: (set s | s in S.Model() && v in s)) + {(set s | s in (S.Model() - S'.Model()) && u in s)};
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
    invariant counter <= counter_in + 2*S.UBSize0() + 2*U.UBSize0() + 1 + (s.Cardinality() - s'.Cardinality())*poly_inner_loop(U, S, k)
  {
    s', s_contains_u, s'_empty, counter := HittingSet_to_SetCover_inner_loop(U, S, k, s, s', u, s_contains_u, counter);
  }
  mult_preserves_order(s.Cardinality(), poly_inner_loop(U, S, k), U.UBSize0(), poly_inner_loop(U, S, k));
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u.Add(s, counter);
  }
  S''_empty, counter := S''.Empty(counter);
  assert counter <= counter_in + 3*S.UBSize0() + 2*U.UBSize0() + 2 + U.UBSize0()*poly_inner_loop(U, S, k);
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


method HittingSet_to_SetCover_edge_case_loop(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, SS:SetSetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, SS':SetSetSet<int>, S''_empty:bool, ghost counter:nat)
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
  s_set, counter := s_set.Add(s, counter);
  SS', counter := SS.Add(s_set, counter);
  S''_empty, counter := S''.Empty(counter);
}


lemma counter_simplification_aux_1(U: Set<int>, S: SetSet<int>, k: nat, S'_prev: SetSet<int>, S': SetSet<int>)
  requires S'_prev.Cardinality() == S'.Cardinality() + 1
  ensures S.UBSize0() + U.UBSize0() + 3 + (S.Cardinality() - S'_prev.Cardinality())*(poly_middle_loop(U, S, k)) + poly_middle_loop(U, S, k) ==
          S.UBSize0() + U.UBSize0() + 3 + (S.Cardinality() - S'.Cardinality())*(poly_middle_loop(U, S, k))
{}


ghost function poly_inner_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  U.UBSize0() + 2
}
ghost function poly_middle_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures 3*S.UBSize0() + 2*U.UBSize0() + 2 + U.UBSize0()*poly_inner_loop(U, S, k) <= o
{
  /*calc <= {
    3*S.UBSize0() + 2*U.UBSize0() + 2 + U.UBSize0()*poly_inner_loop(U, S, k);
    3*S.UBSize0() + 2*U.UBSize0() + 2 + U.UBSize0()*(U.UBSize0() + 2);
    3*S.UBSize0() + 2*U.UBSize0() + 2 + U.UBSize0()*U.UBSize0() + 2*U.UBSize0();
    U.UBSize0()*U.UBSize0() + 3*S.UBSize0() + 4*U.UBSize0() + 1;
  }*/
  U.UBSize0()*U.UBSize0() + 3*S.UBSize0() + 4*U.UBSize0() + 2
}
ghost function poly_outer_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures S.UBSize0() + U.UBSize0() + 4 + S.Cardinality()*(poly_middle_loop(U, S, k)) + S.UBSize0()*U.Cardinality() <= o
{
  /*calc <= {
    S.UBSize0() + U.UBSize0() + 4 + S.Cardinality()*(poly_middle_loop(U, S, k)) + S.UBSize0()*U.Cardinality();
    S.UBSize0()*U.Cardinality() + S.UBSize0() + U.UBSize0() + 4 + S.Cardinality()*(poly_middle_loop(U, S, k));
    S.UBSize0()*U.Cardinality() + S.UBSize0() + U.UBSize0() + 4 + S.Cardinality()*(U.UBSize0()*U.UBSize0() + 3*S.UBSize0() + 4*U.UBSize0() + 2);
    S.UBSize0()*U.Cardinality() + S.UBSize0() + U.UBSize0() + 4 + (U.UBSize0()*U.UBSize0()*S.Cardinality() + 3*S.UBSize0()*S.Cardinality() + 4*U.UBSize0()*S.Cardinality() + 2*S.Cardinality());
    U.UBSize0()*U.UBSize0()*S.Cardinality() + 3*S.UBSize0()*S.Cardinality() + S.UBSize0()*U.Cardinality() + 4*U.UBSize0()*S.Cardinality() + S.UBSize0() + U.UBSize0() + 2*S.Cardinality() + 4;
  }*/
  U.UBSize0()*U.UBSize0()*S.Cardinality() + 3*S.UBSize0()*S.Cardinality() + S.UBSize0()*U.Cardinality() + 4*U.UBSize0()*S.Cardinality() + S.UBSize0() + U.UBSize0() + 2*S.Cardinality() + 4
}
ghost function poly_edge_case_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  2*S.UBSize0() + 2*U.UBSize0() + 2
}


ghost function poly(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures 2*S.UBSize0() + 3 + S.Cardinality()*poly_edge_case_loop(U, S, k) <= o           // If S contains empty
  ensures S.UBSize0() + U.UBSize0() + 3 + U.Cardinality()*poly_outer_loop(U, S, k) <= o      // Otherwise
{
  calc == {
    2*S.UBSize0() + 3 + S.Cardinality()*(poly_edge_case_loop(U, S, k));
    2*S.UBSize0() + 3 + S.Cardinality()*(2*S.UBSize0() + 2*U.UBSize0() + 2);
    2*S.UBSize0() + 3 + (2*S.UBSize0()*S.Cardinality() + 2*U.UBSize0()*S.Cardinality() + 2*S.Cardinality());
    2*S.UBSize0()*S.Cardinality() + 2*U.UBSize0()*S.Cardinality() + 2*S.UBSize0() + 2*S.Cardinality() + 3;
  }
  calc == {
    S.UBSize0() + U.UBSize0() + 3 + U.Cardinality()*poly_outer_loop(U, S, k);
    S.UBSize0() + U.UBSize0() + 3 + U.Cardinality()*(U.UBSize0()*U.UBSize0()*S.Cardinality() + 3*S.UBSize0()*S.Cardinality() + S.UBSize0()*U.Cardinality() + 4*U.UBSize0()*S.Cardinality() + S.UBSize0() + U.UBSize0() + 2*S.Cardinality() + 4);
    S.UBSize0() + U.UBSize0() + 3 + (U.UBSize0()*U.UBSize0()*S.Cardinality()*U.Cardinality() + 3*S.UBSize0()*S.Cardinality()*U.Cardinality() + S.UBSize0()*U.Cardinality()*U.Cardinality() + 4*U.UBSize0()*S.Cardinality()*U.Cardinality() + S.UBSize0()*U.Cardinality() + U.UBSize0()*U.Cardinality() + 2*S.Cardinality()*U.Cardinality() + 4*U.Cardinality());
    U.UBSize0()*U.UBSize0()*S.Cardinality()*U.Cardinality() + 3*S.UBSize0()*S.Cardinality()*U.Cardinality() + S.UBSize0()*U.Cardinality()*U.Cardinality() + 4*U.UBSize0()*S.Cardinality()*U.Cardinality() + S.UBSize0()*U.Cardinality() + U.UBSize0()*U.Cardinality() + 2*S.Cardinality()*U.Cardinality() + S.UBSize0() + U.UBSize0() + 4*U.Cardinality() + 3;
  }
  U.UBSize0()*U.UBSize0()*S.Cardinality()*U.Cardinality() + 3*S.UBSize0()*S.Cardinality()*U.Cardinality() + S.UBSize0()*U.Cardinality()*U.Cardinality() + 4*U.UBSize0()*S.Cardinality()*U.Cardinality() + 2*S.UBSize0()*S.Cardinality() + S.UBSize0()*U.Cardinality() + 2*U.UBSize0()*S.Cardinality() + U.UBSize0()*U.Cardinality() + 2*S.Cardinality()*U.Cardinality() + 2*S.UBSize0() + U.UBSize0() + 2*S.Cardinality() + 4*U.Cardinality() + 3
}
