include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method HittingSet_to_SetCover_Method(U:Set<int>, S:SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, nat), ghost counter:nat)
  //requires forall s | s in S ::  s <= U
  //ensures r == HittingSet_to_SetCover(U, S, k) (en simple tampoco está puesto)
  //ensures counter <= poly(U, S, k)
  requires init_Set(U)
  requires init_SetSet(S)
  requires S.maximumSizeElements() <= U.Size()
{
  counter := 0;

  var newS:SetSetSet<int>; newS, counter := NewSetSetSet(counter);
  var U':Set<int>; U', counter := U.Copy(counter);
  var U'_empty:bool; U'_empty, counter := U'.Empty(counter);
  assume false;
  while (!U'_empty)
    /*
    decreases |U'|
    invariant U' <= U
    invariant newS == (set u | u in (U - U') :: (set s | s in S && u in s))
    invariant counter <= 1 + |U| + (|U| - |U'|)*(poly_outer_loop(U, S, k) + 1)
    */
    // Termination
    decreases U'.Cardinality()
    // Types

    // Regular invariants

    // Counter

  {
    U', newS, U'_empty, counter := HittingSet_to_SetCover_outer_loop(U, S, k, U', newS, counter);
  }
  /*
  identity_substraction_lemma(U.Model(), U'.Model());
  var S_contains_empty:bool := false;
  var S' := S; counter := counter + |S|*|U|;
  assert counter <= poly_aux_1(U, S, k);
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant S_contains_empty == ({} in (S - S'))
    invariant counter <= poly_aux_1(U, S, k) + (|S| - |S'|)*(poly_contains_empty_loop(U, S, k) + 1)
  {
    S', S_contains_empty, counter := HittingSet_to_SetCover_S_contains_empty_loop(U, S, k, S', S_contains_empty, counter);
  }

  if (S_contains_empty) {
    var newS := {};
    var S' := S;
    assert counter <= poly_aux_2(U, S, k);
    while (S' != {})
      decreases |S'|
      invariant S' <= S
      invariant newS == (set s | s in (S - S') :: {s})
      invariant counter <= poly_aux_2(U, S, k) + (|S| - |S'|)*(poly_edge_case_loop(U, S, k) + 1)
    {
      S', newS, counter := HittingSet_to_SetCover_edge_case_loop(U, S, k, S', newS, counter);
    }
    assert counter <= poly(U, S, k);
    return (S, newS, 0), counter;
  }
  else {
    return (S, newS, k), counter;
  }
  */
}


method HittingSet_to_SetCover_outer_loop(U:Set<int>, S:SetSet<int>, k:nat, U':Set<int>, newS:SetSetSet<int>, ghost counter_in:nat) returns (U'':Set<int>, newS':SetSetSet<int>, U''_empty:bool, ghost counter:nat)
// Termination in
requires U'.Model() != {}
// Types in
requires S.Valid()
requires newS.Valid()
requires in_universe_Set(U', U)
requires S.maximumSizeElements() <= U.Size()
// Invariant in
requires forall s | s in S.Model() ::  s <= U.Model()
requires newS.Model() == (set u | u in (U.Model() - U'.Model()) :: (set s | s in S.Model() && u in s))
// Termination out
ensures U''.Cardinality() == U'.Cardinality() - 1
ensures U''_empty == (U''.Model() == {})
// Types out
ensures newS'.Valid()
ensures in_universe_Set(U'', U)
// Invariant out
ensures newS'.Model() == (set u | u in (U.Model() - U''.Model()) :: (set s | s in S.Model() && u in s))
// Counter
//ensures counter <= counter_in + poly_outer_loop(U, S, k)
{
  counter := counter_in;
  in_universe_lemma_Set(U', U);
  var u:int; u, counter := U'.Pick(counter);
  U'', counter := U'.Remove(u, counter);

  var sets_in_S_that_contain_u:SetSet<int>; sets_in_S_that_contain_u, counter := NewSetSet_params(S.Model(), S.maximumSizeElements(), counter);
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
    invariant forall s | s in S.Model() ::  s <= U.Model()
    invariant sets_in_S_that_contain_u.Model() == (set s | s in (S.Model() - S'.Model()) && u in s)
    // Counter
    invariant counter <= counter_in + S.Size() + U.Size() + 3*constant + (S.Cardinality() - S'.Cardinality())*(poly_middle_loop(U, S, k))
  {
    S', sets_in_S_that_contain_u, S'_empty, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  newS', counter := newS.Add(sets_in_S_that_contain_u, counter);
  U''_empty, counter := U''.Empty(counter);
  assert counter <= counter_in + S.Size() + U.Size() + 4*constant + S.Cardinality()*(poly_middle_loop(U, S, k)) + newS.Size();  // newS.Size() == U.Cardinality()*S.Size()


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
// Invariant in
requires forall s | s in S.Model() ::  s <= U.Model()
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

method HittingSet_to_SetCover_edge_case_loop(U:Set<int>, S:SetSet<int>, k:nat, S':SetSet<int>, newS:SetSetSet<int>, ghost counter_in:nat) returns (S'':SetSet<int>, newS':SetSetSet<int>, ghost counter:nat)
// Termination in
requires S'.Model() != {}
// Types in
requires U.Valid()
requires newS.Valid()
requires in_universe_SetSet(S', S)
requires S.maximumSizeElements() <= U.Size()
// Invariant in
requires newS.Model() == (set s | s in (S.Model() - S'.Model()) :: {s})
requires newS.Cardinality() <= S.Cardinality() - S'.Cardinality()
requires newS.maximumSizeElements() <= S.maximumSizeElements()
// Termination out
ensures S''.Cardinality() == S'.Cardinality() - 1
// Types out
ensures newS'.Valid()
ensures in_universe_SetSet(S'', S)
// Invariant out
ensures newS'.Model() == (set s | s in (S.Model() - S''.Model()) :: {s})
ensures newS'.Cardinality() <= S.Cardinality() - S''.Cardinality()
ensures newS'.maximumSizeElements() <= S.maximumSizeElements()
// Counter
ensures counter <= counter_in + poly_edge_case_loop(U, S, k)
{
  in_universe_lemma_SetSet(S', S);
  mult_preserves_order(newS.Cardinality(), newS.maximumSizeElements(), S.Cardinality(), S.maximumSizeElements());
  counter := counter_in;
  var s:Set<int>; s, counter := S'.Pick(counter);
  S'', counter := S'.Remove(s, counter);
  var s_set:SetSet<int>; s_set, counter := NewSetSet(counter);
  s_set, counter := s_set.Add(s, counter);
  newS', counter := newS.Add(s_set, counter);
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
ghost function poly_contains_empty_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  S.Size() + U.Size() + constant
}
ghost function poly_edge_case_loop(U: Set<int>, S: SetSet<int>, k: nat) : (o:nat)
{
  2*S.Size() + 2*U.Size() + constant
}
