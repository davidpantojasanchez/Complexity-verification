include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method HittingSet_to_SetCover_Method(U:Set<int>, S:SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, nat), ghost counter:nat)
  //ensures r == HittingSet_to_SetCover(U, S, k)
  requires init_Set(U)
  requires init_SetSet(S)
  requires S.maximumSizeElements() <= U.Size()
  ensures counter <= poly(U, S, k)
{
  counter := 0;
  var newS:SetSetSet<int>; newS, counter := New_SetSetSet_params((set u | u in U.Model() :: (set s | s in S.Model() && u in s)), S.Size(), U.Size(), counter);
  var U':Set<int>; U', counter := U.Copy(counter);
  var U'_empty:bool; U'_empty, counter := U'.Empty(counter);
  assert counter == U.Size() + 2*constant;
  while (!U'_empty)
    // Termination
    decreases U'.Cardinality()
    invariant U'_empty == (U'.Model() == {})
    // Types
    invariant newS.Valid()
    invariant in_universe_Set(U', U)
    invariant newS.Cardinality() <= U.Cardinality() - U'.Cardinality()
    invariant newS.maximumSizeElements() <= S.Size()
    // Regular invariants
    invariant newS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
    // Counter
    invariant counter <= U.Size() + 2*constant + (U.Cardinality() - U'.Cardinality())*poly_outer_loop(U, S, k)
  {
    U', newS, U'_empty, counter := HittingSet_to_SetCover_outer_loop(U, S, k, U', newS, counter);
  }
  //identity_substraction_lemma(U.Model(), U'.Model());
  var empty_set:Set<int>; empty_set, counter := New_Set(counter);
  var S_contains_empty:bool; S_contains_empty, counter := S.Contains(empty_set, counter);
  /*
  var S_contains_empty:bool := false;
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant S_contains_empty == ({} in (S - S'))
    invariant counter <= poly_aux_1(U, S, k) + (|S| - |S'|)*(poly_contains_empty_loop(U, S, k) + 1)
  {
    S', S_contains_empty, counter := HittingSet_to_SetCover_S_contains_empty_loop(U, S, k, S', S_contains_empty, counter);
  }
  */
  if (S_contains_empty) {
    var newS:SetSetSet<int>; newS, counter := New_SetSetSet_params((set s | s in S.Model() :: {s}), S.maximumSizeElements(), U.Size(), counter);
    var S':SetSet<int>; S', counter := S.Copy(counter);
    var S'_empty:bool; S'_empty, counter := S'.Empty(counter);
    assert counter <= poly_aux_1(U, S, k);
    while (!S'_empty)
      // Termination
      decreases S'.Cardinality()
      invariant S'_empty == (S'.Model() == {})
      // Types
      invariant U.Valid()
      invariant newS.Valid()
      invariant in_universe_SetSet(S', S)
      invariant S.maximumSizeElements() <= U.Size()
      invariant newS.Cardinality() <= S.Cardinality() - S'.Cardinality()
      invariant newS.maximumSizeElements() <= S.maximumSizeElements()
      // Regular invariants
      invariant newS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
      // Counter
      invariant counter <= poly_aux_1(U, S, k) + (S.Cardinality() - S'.Cardinality())*(poly_edge_case_loop(U, S, k))
    {
      ghost var prevS' := S';
      S', newS, S'_empty, counter := HittingSet_to_SetCover_edge_case_loop(U, S, k, S', newS, counter);
      assert counter <= poly_aux_1(U, S, k) + (S.Cardinality() - prevS'.Cardinality())*(poly_edge_case_loop(U, S, k)) + poly_edge_case_loop(U, S, k);
      assert (S.Cardinality() - prevS'.Cardinality()) + 1 == (S.Cardinality() - S'.Cardinality());
      calc == {
        (S.Cardinality() - prevS'.Cardinality())*(poly_edge_case_loop(U, S, k)) + poly_edge_case_loop(U, S, k);
        (S.Cardinality() - prevS'.Cardinality() + 1)*(poly_edge_case_loop(U, S, k));
        (S.Cardinality() - S'.Cardinality())*(poly_edge_case_loop(U, S, k));
      }
    }
    //assert counter <= poly_aux_1(U, S, k) + S.Cardinality()*(poly_edge_case_loop(U, S, k));
    return (S, newS, 0), counter;
  }
  else {
    return (S, newS, k), counter;
  }
  
}


method HittingSet_to_SetCover_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, U':Set<int>, newS:SetSetSet<int>, ghost counter_in:nat) returns (U'':Set<int>, newS':SetSetSet<int>, U''_empty:bool, ghost counter:nat)
// Termination in
requires U'.Model() != {}
// Types in
requires S.Valid()
requires newS.Valid()
requires in_universe_Set(U', U)
requires S.maximumSizeElements() <= U.Size()
requires newS.Cardinality() <= (U.Cardinality() - U'.Cardinality())
requires newS.maximumSizeElements() <= S.Size()
// Invariant in
requires newS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
// Termination out
ensures U''.Cardinality() == U'.Cardinality() - 1
ensures U''_empty == (U''.Model() == {})
// Types out
ensures newS'.Valid()
ensures in_universe_Set(U'', U)
ensures newS'.Cardinality() <= (U.Cardinality() - U''.Cardinality())
ensures newS'.maximumSizeElements() <= S.Size()
// Invariant out
ensures newS'.Model() == (set u | u in (U.Model() - U''.Model()) :: (set s | s in S.Model() && u in s))
// Counter
ensures counter <= counter_in + poly_outer_loop(U, S, k)
{
  counter := counter_in;
  in_universe_lemma_Set(U', U);
  var u:int; u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var sets_in_S_that_contain_u:SetSet<int>; sets_in_S_that_contain_u, counter := New_SetSet_params(S.Model(), S.maximumSizeElements(), counter);
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
    invariant S.maximumSizeElements() <= U.Size()
    // Regular invariants
    invariant sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
    // Counter
    invariant counter <= counter_in + S.Size() + U.Size() + 3*constant + (S.Cardinality() - S'.Cardinality())*(poly_middle_loop(U, S, k))
  {
    ghost var S'_prev := S';
    S', sets_in_S_that_contain_u, S'_empty, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
    counter_simplification_aux_1(U, S, k, S'_prev, S');
  }
  in_universe_lemma_SetSet(sets_in_S_that_contain_u, S);
  newS', counter := newS.Add(sets_in_S_that_contain_u, counter);

  U''_empty, counter := U''.Empty(counter);
  mult_preserves_order(newS.Cardinality(), newS.maximumSizeElements(), U.Cardinality(), S.Size());
  assert newS'.Model() == (set v | v in (U.Model() - U''.Model()) :: (set s | s in S.Model() && v in s)) by {
    assert newS'.Model() == (set v | v in (U.Model() - U'.Model()) :: (set s | s in S.Model() && v in s)) + {sets_in_S_that_contain_u.Model()};
    assert newS'.Model() == (set v | v in (U.Model() - U'.Model()) :: (set s | s in S.Model() && v in s)) + {(set s | s in (S.Model() - S'.Model()) && u in s)};
    assert (S.Model() - S'.Model()) == S.Model();
    assert newS'.Model() == (set v | v in (U.Model() - U'.Model()) + {u} :: (set s | s in S.Model() && v in s));
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
requires S.maximumSizeElements() <= U.Size()
ensures sets_in_S_that_contain_u.Size() <= S.Size()
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
    invariant s.Cardinality() <= S.maximumSizeElements()
    invariant S.maximumSizeElements() <= U.Size()
    // Regular invariants
    invariant s_contains_u == (u in (s.Model() - s'.Model()))
    // Counter
    invariant counter <= counter_in + 2*S.Size() + 2*U.Size() + constant + (s.Cardinality() - s'.Cardinality())*poly_inner_loop(U, S, k)
  {
    s', s_contains_u, s'_empty, counter := HittingSet_to_SetCover_inner_loop(U, S, k, s, s', u, s_contains_u, counter);
  }
  mult_preserves_order(s.Cardinality(), poly_inner_loop(U, S, k), U.Size(), poly_inner_loop(U, S, k));
  if (s_contains_u) {
    sets_in_S_that_contain_u', counter := sets_in_S_that_contain_u.Add(s, counter);
  }
  S''_empty, counter := S''.Empty(counter);
  assert counter <= counter_in + 3*S.Size() + 2*U.Size() + 2*constant + U.Size()*poly_inner_loop(U, S, k);
}

method HittingSet_to_SetCover_inner_loop(U:Set<int>, S:SetSet<int>, k:nat, s:Set<int>, s':Set<int>, u:int, s_contains_u:bool, ghost counter_in:nat) returns (s'':Set<int>, s_contains_u':bool, s''_empty:bool, ghost counter:nat)
// Termination in
requires s'.Model() != {}
// Types in
requires U.Valid()
requires S.Valid()
requires in_universe_Set(s', s)
requires s.Cardinality() <= S.maximumSizeElements()
requires S.maximumSizeElements() <= U.Size()
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

method HittingSet_to_SetCover_S_contains_empty_loop(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, S_contains_empty:bool, ghost counter_in:nat) returns (S'':SetSet<int>, S_contains_empty':bool, ghost counter:nat)
// Termination in
requires S'.Model() != {}
// Types in
requires U.Valid()
requires in_universe_SetSet(S', S)
requires S.maximumSizeElements() <= U.Size()
// Invariant in
requires S_contains_empty == ({} in (S.Model() - S'.Model()))
// Termination out
ensures S''.Cardinality() == S'.Cardinality() - 1
// Types out
ensures in_universe_SetSet(S'', S)
ensures S''.maximumSizeElements() <= U.Size()
// Invariant out
ensures S_contains_empty'== ({} in (S.Model() - S''.Model()))
// Counter
ensures counter <= counter_in + poly_contains_empty_loop(U, S, k)
{
  in_universe_lemma_SetSet(S', S);
  counter := counter_in;
  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);
  var s_empty:bool; s_empty, counter := s.Empty(counter);
  S_contains_empty' := S_contains_empty || s_empty;
}

method HittingSet_to_SetCover_edge_case_loop(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, newS:SetSetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, newS':SetSetSet<int>, S''_empty:bool, ghost counter:nat)
// Termination in
requires S'.Model() != {}
// Types in
requires U.Valid()
requires newS.Valid()
requires in_universe_SetSet(S', S)
requires S.maximumSizeElements() <= U.Size()
requires newS.Cardinality() <= S.Cardinality() - S'.Cardinality()
requires newS.maximumSizeElements() <= S.maximumSizeElements()
// Invariant in
requires newS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
// Termination out
ensures S''.Cardinality() == S'.Cardinality() - 1
ensures S''_empty == (S''.Model() == {})
// Types out
ensures newS'.Valid()
ensures in_universe_SetSet(S'', S)
ensures newS'.Cardinality() <= S.Cardinality() - S''.Cardinality()
ensures newS'.maximumSizeElements() <= S.maximumSizeElements()
// Invariant out
ensures newS'.Model() == (set s | s in (S.Model() - S''.Model()) :: {s})
// Counter
ensures counter <= counter_in + poly_edge_case_loop(U, S, k)
{
  in_universe_lemma_SetSet(S', S);
  mult_preserves_order(newS.Cardinality(), newS.maximumSizeElements(), S.Cardinality(), S.maximumSizeElements());
  counter := counter_in;
  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);
  var s_set:SetSet<int>; s_set, counter := New_SetSet_params(S.Model(), S.maximumSizeElements(), counter);
  s_set, counter := s_set.Add(s, counter);
  newS', counter := newS.Add(s_set, counter);
  S''_empty, counter := S''.Empty(counter);
}


lemma counter_simplification_aux_1(U: Set<int>, S: SetSet<int>, k: nat, S'_prev: SetSet<int>, S': SetSet<int>)
requires S'_prev.Cardinality() == S'.Cardinality() + 1
ensures S.Size() + U.Size() + 3*constant + (S.Cardinality() - S'_prev.Cardinality())*(poly_middle_loop(U, S, k)) + poly_middle_loop(U, S, k) == S.Size() + U.Size() + 3*constant + (S.Cardinality() - S'.Cardinality())*(poly_middle_loop(U, S, k))
{}


ghost function poly_aux_1(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures 2*S.Size() + U.Size() + 5*constant + U.Size()*poly_outer_loop(U, S, k) <= o
{
  /*calc == {
    2*S.Size() + U.Size() + 5*constant + U.Size()*poly_outer_loop(U, S, k);
    2*S.Size() + U.Size() + 5*constant + U.Size()*(U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*S.Cardinality() + S.Size()*U.Cardinality() + 4*U.Size()*S.Cardinality() + S.Size() + U.Size() + 2*S.Cardinality() + 4*constant);
    2*S.Size() + U.Size() + 5*constant + (U.Size()*U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size()*U.Cardinality() + 4*U.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size() + U.Size()*U.Size() + 2*U.Size()*S.Cardinality() + 4*U.Size()*constant);
    U.Size()*U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size()*U.Cardinality() + 4*U.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size() + U.Size()*U.Size() + 2*U.Size()*S.Cardinality() + 2*S.Size() + 5*U.Size() + 5*constant;
  }*/
  U.Size()*U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size()*U.Cardinality() + 4*U.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size() + U.Size()*U.Size() + 2*U.Size()*S.Cardinality() + 2*S.Size() + 5*U.Size() + 5*constant
}
ghost function poly_inner_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  U.Size() + 2*constant
}
ghost function poly_middle_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures 3*S.Size() + 2*U.Size() + 2*constant + U.Size()*poly_inner_loop(U, S, k) <= o
{
  /*calc <= {
    3*S.Size() + 2*U.Size() + 2*constant + U.Size()*poly_inner_loop(U, S, k);
    3*S.Size() + 2*U.Size() + 2*constant + U.Size()*(U.Size() + 2*constant);
    3*S.Size() + 2*U.Size() + 2*constant + U.Size()*U.Size() + 2*U.Size();
    U.Size()*U.Size() + 3*S.Size() + 4*U.Size() + constant;
  }*/
  U.Size()*U.Size() + 3*S.Size() + 4*U.Size() + 2*constant
}
ghost function poly_outer_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures S.Size() + U.Size() + 4*constant + S.Cardinality()*(poly_middle_loop(U, S, k)) + S.Size()*U.Cardinality() <= o
{
  /*calc <= {
    S.Size() + U.Size() + 4*constant + S.Cardinality()*(poly_middle_loop(U, S, k)) + S.Size()*U.Cardinality();
    S.Size()*U.Cardinality() + S.Size() + U.Size() + 4*constant + S.Cardinality()*(poly_middle_loop(U, S, k));
    S.Size()*U.Cardinality() + S.Size() + U.Size() + 4*constant + S.Cardinality()*(U.Size()*U.Size() + 3*S.Size() + 4*U.Size() + 2*constant);
    S.Size()*U.Cardinality() + S.Size() + U.Size() + 4*constant + (U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*S.Cardinality() + 4*U.Size()*S.Cardinality() + 2*S.Cardinality());
    U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*S.Cardinality() + S.Size()*U.Cardinality() + 4*U.Size()*S.Cardinality() + S.Size() + U.Size() + 2*S.Cardinality() + 4*constant;
  }*/
  U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*S.Cardinality() + S.Size()*U.Cardinality() + 4*U.Size()*S.Cardinality() + S.Size() + U.Size() + 2*S.Cardinality() + 4*constant
}
ghost function poly_contains_empty_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  S.Size() + U.Size() + constant
}
ghost function poly_edge_case_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  2*S.Size() + 2*U.Size() + 2*constant
}

ghost function poly(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
  ensures poly_aux_1(U, S, k) + S.Cardinality()*(poly_edge_case_loop(U, S, k)) <= o           // If S contains empty
  ensures S.Size() + U.Size() + 3*constant + U.Cardinality()*poly_outer_loop(U, S, k) <= o    // Otherwise
{
  /*calc == {
    poly_aux_1(U, S, k) + S.Cardinality()*(poly_edge_case_loop(U, S, k));
    poly_aux_1(U, S, k) + S.Cardinality()*(2*S.Size() + 2*U.Size() + 2*constant);
    poly_aux_1(U, S, k) + (2*S.Size()*S.Cardinality() + 2*U.Size()*S.Cardinality() + 2*S.Cardinality());
    U.Size()*U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size()*U.Cardinality() + 4*U.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size() + U.Size()*U.Size() + 2*U.Size()*S.Cardinality() + 2*S.Size() + 5*U.Size() + 5*constant +
      (2*S.Size()*S.Cardinality() + 2*U.Size()*S.Cardinality() + 2*S.Cardinality());
    U.Size()*U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size()*U.Cardinality() + 4*U.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size() + U.Size()*U.Size() + 2*S.Size()*S.Cardinality() + 4*U.Size()*S.Cardinality() + 2*S.Size() + 5*U.Size() + 2*S.Cardinality() + 5*constant;
  }*/
  U.Size()*U.Size()*U.Size()*S.Cardinality() + 3*S.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size()*U.Cardinality() + 4*U.Size()*U.Size()*S.Cardinality() + S.Size()*U.Size() + U.Size()*U.Size() + 2*S.Size()*S.Cardinality() + 4*U.Size()*S.Cardinality() + 2*S.Size() + 5*U.Size() + 2*S.Cardinality() + 5*constant
}
