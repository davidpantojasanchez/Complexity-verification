include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"

method HittingSet_to_SetCover_Method(U: set<int>, S: set<set<int>>, k: nat) returns (r:(set<set<int>>, set<set<set<int>>>, nat), ghost counter:nat)
  requires forall s | s in S ::  s <= U
  //ensures r == HittingSet_to_SetCover(U, S, k)
  ensures counter <= poly(U, S, k)
{
  counter := 0;

  var newS:set<set<set<int>>> := {};
  counter := counter + 1;
  var U' := U;
  counter := counter + |U|;
  while (U' != {})
    decreases |U'|
    invariant U' <= U
    invariant newS == (set u | u in (U - U') :: (set s | s in S && u in s))
    invariant counter <= 1 + |U| + (|U| - |U'|)*(poly_outer_loop(U, S, k) + 1)
  {
    counter := counter + 1;
    U', newS, counter := HittingSet_to_SetCover_outer_loop(U, S, k, U', newS, counter);
  }
  counter := counter + 1;
  identity_substraction_lemma(U, U');

  var S_contains_empty:bool := false;
  var S' := S;
  counter := counter + |S|;
  assert counter <= poly1(U, S, k);
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant S_contains_empty == ({} in (S - S'))
    invariant counter <= poly1(U, S, k) + (|S| - |S'|)*(poly_contains_empty_loop(U, S, k) + 1)
  {
    counter := counter + 1;
    S', S_contains_empty, counter := HittingSet_to_SetCover_S_contains_empty_loop(U, S, k, S', S_contains_empty, counter);
  }
  assert counter <= poly1(U, S, k) + |S|*(poly_contains_empty_loop(U, S, k) + 1);
  counter := counter + 1;

  if (S_contains_empty) {
    var newS := {};
    counter := counter + 1;
    var S' := S;
    counter := counter;
    //assert counter <= poly1(U, S, k) + |S|*(poly_contains_empty_loop(U, S, k) + 1) + |S| + 1;
    assert counter <= poly2(U, S, k);
    while (S' != {})
      decreases |S'|
      invariant S' <= S
      invariant newS == (set s | s in (S - S') :: {s})
      invariant counter <= poly2(U, S, k) + (|S| - |S'|)*(poly_edge_case_loop(U, S, k) + 1)
    {
      counter := counter + 1;
      S', newS, counter := HittingSet_to_SetCover_edge_case_loop(U, S, k, S', newS, counter);
      //assert counter <= poly2(U, S, k) + (|S| - |S'| - 1)*(poly_edge_case_loop(U, S, k) + 1) + 1 + 2*|S|*|U| + |U|;
    }
    //assert counter <= poly2(U, S, k) + |S|*(poly_edge_case_loop(U, S, k) + 1);
    counter := counter + 1;
    assert counter <= poly(U, S, k);
    return (S, newS, 0), counter;
  }
  else {
    //assert counter <= poly1(U, S, k) + |S|*(|S|*|U| + 2*|U| + 1) + 1;
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
ensures counter <= counter_in + poly_outer_loop(U, S, k) // 2*|S|*|S|*|U| + 2*|S|*|U|*|U| + 5*|S|*|U| + 3*|S| + |U| + 2
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
    invariant counter <= counter_in + |S| + |U| + 1 + (|S| - |S'|)*(poly_middle_loop(U, S, k) + 1)
  {
    counter := counter + 1;
    S', sets_in_S_that_contain_u, counter := HittingSet_to_SetCover_middle_loop(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  counter := counter + 1;

  newS' := newS + {sets_in_S_that_contain_u};
  counter := counter + |S|*|U|*|U|;

  assert counter <= counter_in + 2*|S|*|S|*|U| + 2*|S|*|U|*|U| + 5*|S|*|U| + 3*|S| + |U| + 2;

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
ensures counter <= counter_in + poly_middle_loop(U, S, k)
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
    invariant counter == counter_in + |S|*|U| + 2*|U| + (|s| - |s'|)*(|U| + 3)
  {
    counter := counter + 1;
    s', s_contains_u, counter := HittingSet_to_SetCover_inner_loop(U, S, k, s, s', u, s_contains_u, counter);
  }
  counter := counter + 1;
  assert counter <= counter_in + poly3(U, S, k) by {
    //assert counter <= counter_in + |S|*|U| + 2*|U| + (|s| - |s'|)*(|U| + 3) + 1;
    if_smaller_then_less_cardinality(s, U);
    //assert |s| <= |U|;
    //assert (|s| - |s'|) <= |U|;
    aux_lemma_1(U, S, k, s, s');
    //assert (|s| - |s'|)*(|U| + 3) <= (|U|)*(|U| + 3);
    //assert counter <= counter_in + |S|*|U| + 2*|U| + (|U|)*(|U| + 3) + 1;
  }

  if (s_contains_u) {
    sets_in_S_that_contain_u' := sets_in_S_that_contain_u + {s};
    counter := counter + |S|*|U|;
  }
  assert counter <= counter_in + |S|*|U| + poly3(U, S, k);
  assert counter <= counter_in + poly_middle_loop(U, S, k);
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
ensures counter == counter_in + poly_inner_loop(U, S, k)
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
ensures counter == counter_in + poly_contains_empty_loop(U, S, k)
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
ensures counter == counter_in + poly_edge_case_loop(U, S, k)     //2*|S|*|U| + |U|
{
  counter := counter_in;
  var s :| s in S';
  counter := counter + |U|;
  S'' := S' - {s};
  counter := counter + |S|*|U|;
  newS' := newS + {{s}};
  counter := counter + |S|*|U|;
}

/*
const c:nat := 100

ghost function O_SSU_SUU(U: set<int>, S: set<set<int>>, k: nat) : (o:nat) {
  c*|S|*|S|*|U| + c*|S|*|U|*|U| + c*|S|*|U| + c*|S| + c*|U| + c
}

ghost function O_SSUU_SUUU(U: set<int>, S: set<set<int>>, k: nat) : (o:nat) {
  c*|S|*|S|*|U|*|U| + c*|S|*|U|*|U|*|U| + c*|S|*|S|*|U| + c*|S|*|U|*|U| + c*|S|*|U| + c*|U|*|U| + c*|S| + c*|U| + c
}
*/

ghost function poly1(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
ensures |S| + |U|*(poly_outer_loop(U, S, k) + 2) + 2 <= o
{
  2*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 5*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + |S| + 4*|U| + 2
}

ghost function poly2(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
ensures poly1(U, S, k) + |S|*(poly_contains_empty_loop(U, S, k) + 1) + |S| + 1 <= o
{
  2*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + |S|*|S|*|U| + 5*|S|*|U|*|U| + 5*|S|*|U| + |U|*|U| + 3*|S| + 4*|U| + 4
}

ghost function poly3(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
{
  |S|*|U| + 2*|U| + (|U|)*(|U| + 3) + 1
}

ghost function poly_inner_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
{
  |U| + 2
}

ghost function poly_middle_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
  ensures |S|*|U| + poly3(U, S, k) <= o
{
  2*|S|*|U| + 2*|U| + |U|*(|U| + 3) + 1
}

ghost function poly_outer_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
{
  2*|S|*|S|*|U| + 2*|S|*|U|*|U| + 5*|S|*|U| + 3*|S| + |U| + 2
}

ghost function poly_contains_empty_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
{
  |S|*|U| + 2*|U|
}

ghost function poly_edge_case_loop(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
{
  2*|S|*|U| + |U|
}

ghost function poly(U: set<int>, S: set<set<int>>, k: nat) : (o:nat)
  //ensures poly1(U, S, k) + |S|*(|S|*|U| + 2*|U| + 1) + 1 <= o
  ensures poly2(U, S, k) + |S|*(poly_edge_case_loop(U, S, k) + 1) + 1 <= o
{
  /*
  calc == {
    poly1(U, S, k) + |S|*(|S|*|U| + 2*|U| + 1) + 1;
    poly1(U, S, k) + |S|*|S|*|U| + 2*|S|*|U| + |S| + 1;
  }
  */

  calc == {
    poly2(U, S, k) + |S|*(poly_edge_case_loop(U, S, k) + 1) + 1;
    poly2(U, S, k) + |S|*(2*|S|*|U| + |U| + 1) + 1;
    poly2(U, S, k) + 2*|S|*|S|*|U| + |S|*|U| + |S| + 1;
    poly2(U, S, k) + 2*|S|*|S|*|U| + |S|*|U| + |S| + 1;
    (2*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + |S|*|S|*|U| + 5*|S|*|U|*|U| + 5*|S|*|U| + |U|*|U| + 3*|S| + 4*|U| + 4) + 2*|S|*|S|*|U| + |S|*|U| + |S| + 1;
    2*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 3*|S|*|S|*|U| + 5*|S|*|U|*|U| + 6*|S|*|U| + |U|*|U| + 4*|S| + 4*|U| + 5;
  }

  2*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 3*|S|*|S|*|U| + 5*|S|*|U|*|U| + 6*|S|*|U| + |U|*|U| + 4*|S| + 4*|U| + 5

}

lemma aux_lemma_1(U: set<int>, S: set<set<int>>, k: nat, s: set<int>, s': set<int>)
requires 0 <= |s'| <= |s| <= |U|
ensures (|s| - |s'|)*(|U| + 3) <= (|U|)*(|U| + 3)
{
}
