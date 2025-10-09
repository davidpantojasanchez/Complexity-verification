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
// Termination
requires U' != {}
// Invariant in
requires U' <= U
requires newS == (set u | u in (U - U') :: (set s | s in S && u in s))
// Decreases
ensures |U''| < |U'|
// Invariant out
ensures U'' <= U
ensures newS' == (set u | u in (U - U'') :: (set s | s in S && u in s))
{
  counter := counter_in;
  var u :| u in U';
  U'' := U' - {u};

  var sets_in_S_that_contain_u:set<set<int>> := {};
  var S' := S;
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
  {
    S', sets_in_S_that_contain_u, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }

  newS' := newS + {sets_in_S_that_contain_u};

  assert newS' == (set v | v in (U - U'') :: (set s | s in S && v in s)) by {
    assert newS' == (set v | v in (U - U') :: (set s | s in S && v in s)) + {sets_in_S_that_contain_u};
    assert newS' == (set v | v in (U - U') :: (set s | s in S && v in s)) + {(set s | s in (S - S') && u in s)};
    assert (S - S') == S;
    assert newS' == (set v | v in (U - U') + {u} :: (set s | s in S && v in s));
    assert (U - U'') == (U - U') + {u};
  }
  
}


method HittingSet_to_SetCover_middle_loop(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, u:int, sets_in_S_that_contain_u:set<set<int>>, ghost counter_in:nat) returns (S'':set<set<int>>, sets_in_S_that_contain_u':set<set<int>>, ghost counter:nat)
// Termination
requires S' != {}
// Invariant in
requires S' <= S
requires sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
// Decreases
ensures |S''| < |S'|
// Invariant out
ensures S'' <= S
ensures sets_in_S_that_contain_u' == (set s | s in (S - S'') && u in s)
{
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s :| s in S';
  S'' := S' - {s};

  var s_contains_u:bool := false;
  var s' := s;

  while (s' != {})
    decreases |s'|
    invariant s' <= s
    invariant s_contains_u == (u in (s - s'))
  {
    s', s_contains_u, counter := HittingSet_to_SetCover_inner_loop(U, S, k, s, s', u, s_contains_u, counter);
  }

  if (s_contains_u) {
    sets_in_S_that_contain_u' := sets_in_S_that_contain_u + {s};
  }

}


method HittingSet_to_SetCover_inner_loop(U:set<int>, S:set<set<int>>, k:nat, s:set<int>, s':set<int>, u:int, s_contains_u:bool, ghost counter_in:nat) returns (s'':set<int>, s_contains_u':bool, ghost counter:nat)
// Termination
requires s' != {}
// Invariant in
requires s' <= s
requires s_contains_u == (u in (s - s'))
// Decreases
ensures |s''| < |s'|
// Invariant out
ensures s'' <= s
ensures s_contains_u' == (u in (s - s''))
{
  counter := counter_in;
  s_contains_u' := s_contains_u;

  var e :| e in s';
  s'' := s' - {e};

  if (e == u) {
    s_contains_u' := true;
  }
}


method HittingSet_to_SetCover_S_contains_empty_loop(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, S_contains_empty:bool, ghost counter_in:nat) returns (S'':set<set<int>>, S_contains_empty':bool, ghost counter:nat)
// Termination
requires S' != {}
// Invariant in
requires S' <= S
requires S_contains_empty == ({} in (S - S'))
// Decreases
ensures |S''| < |S'|
// Invariant out
ensures S'' <= S
ensures S_contains_empty'== ({} in (S - S''))
{
  counter := counter_in;
  S_contains_empty' := S_contains_empty;

  var s :| s in S';
  S'' := S' - {s};
  if (s == {}) {
    S_contains_empty' := true;
  }
}


method HittingSet_to_SetCover_edge_case_loop(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, newS:set<set<set<int>>>, ghost counter_in:nat) returns (S'':set<set<int>>, newS':set<set<set<int>>>, ghost counter:nat)
// Termination
requires S' != {}
// Invariant in
requires S' <= S
requires newS == (set s | s in (S - S') :: {s})
// Decreases
ensures |S''| < |S'|
// Invariant out
ensures S'' <= S
ensures newS' == (set s | s in (S - S'') :: {s})
{
  counter := counter_in;
  var s :| s in S';
  S'' := S' - {s};
  newS' := newS + {{s}};
}

