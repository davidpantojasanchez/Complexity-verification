include "HittingSet.dfy"
include "SetCover.dfy"
include "ReductionHittingSetToSetCover.dfy"
include "Lemmas.dfy"


method HittingSet_to_SetCover_Method(U: set<int>, S: set<set<int>>, k: nat) returns (r:(set<set<int>>, set<set<set<int>>>, int), ghost counter:nat)
  requires forall s | s in S ::  s <= U
  ensures r == HittingSet_to_SetCover(U, S, k)
{
  counter := 0;

  var newS:set<set<set<int>>> := {};
  var U' := U;
  while (U' != {})
    decreases |U'|
    invariant U' <= U
    invariant newS == (set u | u in (U - U') :: (set s | s in S && u in s))
  {
    U', newS, counter := HittingSet_to_SetCover_outer_loop(U, S, k, U', newS, counter);
  }
  identity_substraction_lemma(U, U');

  var S_contains_empty:bool := false;
  var S' := S;
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant S_contains_empty == ({} in (S - S'))
  {
    S', S_contains_empty, counter := HittingSet_to_SetCover_S_contains_empty_loop(U, S, k, S', S_contains_empty, counter);
  }

  if (S_contains_empty) {
    var newS := {};
    var S' := S;
    while (S' != {})
      decreases |S'|
      invariant S' <= S
      invariant newS == (set s | s in (S - S') :: {s})
    {
      S', newS, counter := HittingSet_to_SetCover_edge_case_loop(U, S, k, S', newS, counter);
    }
    identity_substraction_lemma(S, S');
    return (S, newS, 0), counter;
  }
  else {
    return (S, newS, k), counter;
  }

}


method HittingSet_to_SetCover_outer_loop(U:set<int>, S:set<set<int>>, k:nat, U':set<int>, newS:set<set<set<int>>>, ghost counter_in:nat) returns (U'':set<int>, newS':set<set<set<int>>>, ghost counter:nat)
// Problem requirements
requires forall s | s in S ::  s <= U
// Termination
requires U' != {}
// Invariant in
requires U' <= U
requires newS == (set u | u in (U - U') :: (set s | s in S && u in s))
// Decreases
ensures |U''| == |U'| - 1
// Invariant out
ensures U'' <= U
ensures newS' == (set u | u in (U - U'') :: (set s | s in S && u in s))
// Counter

{
  counter := counter_in;
  var u :| u in U';
  counter := counter + 1;
  U'' := U' - {u};
  counter := counter + |U|;

  var sets_in_S_that_contain_u:set<set<int>> := {};
  var S' := S;
  counter := counter + |S|;
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
  {
    S', sets_in_S_that_contain_u, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }

  newS' := newS + {sets_in_S_that_contain_u};
  counter := counter + |S|*|U|*|U|;

  assert newS' == (set v | v in (U - U'') :: (set s | s in S && v in s)) by {
    assert newS' == (set v | v in (U - U') :: (set s | s in S && v in s)) + {sets_in_S_that_contain_u};
    assert newS' == (set v | v in (U - U') :: (set s | s in S && v in s)) + {(set s | s in (S - S') && u in s)};
    assert (S - S') == S;
    assert newS' == (set v | v in (U - U') + {u} :: (set s | s in S && v in s));
    assert (U - U'') == (U - U') + {u};
  }
  
}


method HittingSet_to_SetCover_middle_loop(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, u:int, sets_in_S_that_contain_u:set<set<int>>, ghost counter_in:nat) returns (S'':set<set<int>>, sets_in_S_that_contain_u':set<set<int>>, ghost counter:nat)
// Problem requirements
requires forall s | s in S ::  s <= U
// Termination
requires S' != {}
// Invariant in
requires S' <= S
requires sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
// Decreases
ensures |S''| == |S'| - 1
// Invariant out
ensures S'' <= S
ensures sets_in_S_that_contain_u' == (set s | s in (S - S'') && u in s)
// Counter
ensures counter <= counter_in + 2*|S|*|U| + 2*|U| + |U|*(|U| + 2)
{
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s :| s in S';
  counter := counter + |U|;
  S'' := S' - {s};
  counter := counter + |S|*|U|;

  var s_contains_u:bool := false;
  var s' := s;
  counter := counter + |U|;
  while (s' != {})
    decreases |s'|
    invariant s' <= s
    invariant s_contains_u == (u in (s - s'))
    invariant counter == counter_in + |S|*|U| + 2*|U| + (|s| - |s'|)*(|U| + 2)
  {
    s', s_contains_u, counter := HittingSet_to_SetCover_inner_loop(U, S, k, s, s', u, s_contains_u, counter);
  }
  assert counter <= counter_in + |S|*|U| + 2*|U| + (|U|)*(|U| + 2) by {
    assert s <= U;
  }

  if (s_contains_u) {
    sets_in_S_that_contain_u' := sets_in_S_that_contain_u + {s};
    counter := counter + |S|*|U|;
  }

}


method HittingSet_to_SetCover_inner_loop(U:set<int>, S:set<set<int>>, k:nat, s:set<int>, s':set<int>, u:int, s_contains_u:bool, ghost counter_in:nat) returns (s'':set<int>, s_contains_u':bool, ghost counter:nat)
// Problem requirements
requires forall s | s in S ::  s <= U
// Termination
requires s' != {}
// Invariant in
requires s' <= s
requires s_contains_u == (u in (s - s'))
// Decreases
ensures |s''| == |s'| - 1
// Invariant out
ensures s'' <= s
ensures s_contains_u' == (u in (s - s''))
// Counter
ensures counter == counter_in + |U| + 2
{
  counter := counter_in;
  s_contains_u' := s_contains_u;

  var e :| e in s';
  counter := counter + 1;
  s'' := s' - {e};
  counter := counter + |U|;

  if (e == u) {
    s_contains_u' := true;
  }
  counter := counter + 1;
}


method HittingSet_to_SetCover_S_contains_empty_loop(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, S_contains_empty:bool, ghost counter_in:nat) returns (S'':set<set<int>>, S_contains_empty':bool, ghost counter:nat)
// Problem requirements
requires forall s | s in S ::  s <= U
// Termination
requires S' != {}
// Invariant in
requires S' <= S
requires S_contains_empty == ({} in (S - S'))
// Decreases
ensures |S''| == |S'| - 1
// Invariant out
ensures S'' <= S
ensures S_contains_empty'== ({} in (S - S''))
// Counter
ensures counter == counter_in + |S|*|U| + 2*|U|
{
  counter := counter_in;
  S_contains_empty' := S_contains_empty;

  var s :| s in S';
  counter := counter + |U|;
  S'' := S' - {s};
  counter := counter + |S|*|U|;
  if (s == {}) {
    S_contains_empty' := true;
  }
  counter := counter + |U|;
}


method HittingSet_to_SetCover_edge_case_loop(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, newS:set<set<set<int>>>, ghost counter_in:nat) returns (S'':set<set<int>>, newS':set<set<set<int>>>, ghost counter:nat)
// Problem requirements
requires forall s | s in S ::  s <= U
// Termination
requires S' != {}
// Invariant in
requires S' <= S
requires newS == (set s | s in (S - S') :: {s})
// Decreases
ensures |S''| == |S'| - 1
// Invariant out
ensures S'' <= S
ensures newS' == (set s | s in (S - S'') :: {s})
// Counter
ensures counter == counter_in + 2*|S|*|U| + |U|
{
  counter := counter_in;
  var s :| s in S';
  counter := counter + |U|;
  S'' := S' - {s};
  counter := counter + |S|*|U|;
  newS' := newS + {{s}};
  counter := counter + |S|*|U|;
}

