include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Lemmas/Lemmas.dfy"


method TransformHittingSetToSetCover_simple(U:set<int>, S:set<set<int>>, k:nat) returns (r:(set<set<int>>, set<set<set<int>>>, nat), ghost counter:nat)
  requires HittingSetValidInstance(U, S)
  ensures r == HittingSetToSetCover(U, S, k)
  ensures counter <= PolyTransformHittingSetToSetCover_simple(U, S, k)
{
  counter := 0;
  var SS:set<set<set<int>>> := {}; counter := counter + 1;
  // Edge case
  var S_contains_empty:bool := {} in S; counter := counter + |S|*|U|;
  if (S_contains_empty) {
    var S' := S; counter := counter + |S|*|U|;
    while (S' != {})
      decreases |S'|
      invariant S' <= S
      invariant SS == (set s | s in (S - S') :: {s})
      invariant counter <= 2*|S|*|U| + 1 + (|S| - |S'|)*(PolyAddSingletonSourceSet_simple(U, S, k) + 1)
    {
      counter := counter + 1;
      S', SS, counter := AddSingletonSourceSet_simple(U, S, k, S', SS, counter);
    }
    counter := counter + 1;
    SubtractionIdentity(S, S');
    return (S, SS, 0), counter;
  }
  // Regular case
  var U' := U; counter := counter + |U|;
  while (U' != {})
    decreases |U'|
    invariant U' <= U
    invariant SS == (set u | u in (U - U') :: (set s | s in S && u in s))
    invariant counter <= |S|*|U| + |U| + 1 + (|U| - |U'|)*(PolyBuildIncidenceSet_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    U', SS, counter := BuildIncidenceSet_simple(U, S, k, U', SS, counter);
  }
  counter := counter + 1;
  SubtractionIdentity(U, U');
  
  return (S, SS, k), counter;
}


method BuildIncidenceSet_simple(U:set<int>, S:set<set<int>>, k:nat, U':set<int>, SS:set<set<set<int>>>, ghost counter_in:nat) returns (U'':set<int>, SS':set<set<set<int>>>, ghost counter:nat)
// Problem requirements
requires U' != {}
requires HittingSetValidInstance(U, S)
requires U' <= U
requires SS == (set u | u in (U - U') :: (set s | s in S && u in s))
ensures |U''| == |U'| - 1
ensures U'' <= U
ensures SS' == (set u | u in (U - U'') :: (set s | s in S && u in s))
ensures counter <= counter_in + PolyBuildIncidenceSet_simple(U, S, k)
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
    invariant counter <= counter_in + |S| + |U| + 1 + (|S| - |S'|)*(PolyAddIncidentSourceSet_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    S', sets_in_S_that_contain_u, counter := AddIncidentSourceSet_simple(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  counter := counter + 1;
  SS' := SS + {sets_in_S_that_contain_u};
  counter := counter + |S|*|U|*|U|;

  calc <= {
    counter;
    counter_in + |S| + |U| + 2 + |S|*(PolyAddIncidentSourceSet_simple(U, S, k) + 1) + |S|*|U|*|U|;
    counter_in + 3*|S|*|S|*|U| + |S|*|U|*|U| + 2*|S|*|U| + 3*|S| + |U| + 2;
    counter_in + PolyBuildIncidenceSet_simple(U, S, k);
  }
  assert SS' == (set v | v in (U - U'') :: (set s | s in S && v in s)) by {
  calc {
      SS';
      (set v | v in (U - U') :: (set s | s in S && v in s)) + {sets_in_S_that_contain_u};
      (set v | v in (U - U') :: (set s | s in S && v in s)) + {(set s | s in (S - S') && u in s)};
       {assert (S - S') == S;}
      (set v | v in (U - U') + {u} :: (set s | s in S && v in s));
      {assert (U - U'') == (U - U') + {u};}
      (set v | v in (U - U'') :: (set s | s in S && v in s));
    }  }
  
}


method AddIncidentSourceSet_simple(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, u:int, sets_in_S_that_contain_u:set<set<int>>, ghost counter_in:nat) returns (S'':set<set<int>>, sets_in_S_that_contain_u':set<set<int>>, ghost counter:nat)
// Problem requirements
requires S' != {}
requires HittingSetValidInstance(U, S)
requires S' <= S
requires sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
ensures |S''| == |S'| - 1
ensures S'' <= S
ensures sets_in_S_that_contain_u' == (set s | s in (S - S'') && u in s)
ensures counter <= counter_in + PolyAddIncidentSourceSet_simple(U, S, k)
{
  counter := counter_in;
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;
  counter := counter + |S|*|U|;

  var s :| s in S';
  counter := counter + |U|;
  S'' := S' - {s};
  counter := counter + |S|*|U|;

  var s_contains_u:bool := u in s;
  counter := counter + |U| + 1;

  if (s_contains_u) {
    sets_in_S_that_contain_u' := sets_in_S_that_contain_u + {s};
    counter := counter + |S|*|U|;
  }
}


method AddSingletonSourceSet_simple(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, SS:set<set<set<int>>>, ghost counter_in:nat) returns (S'':set<set<int>>, SS':set<set<set<int>>>, ghost counter:nat)
// Problem requirements
requires S' != {}
requires HittingSetValidInstance(U, S)
requires S' <= S
requires SS == (set s | s in (S - S') :: {s})
ensures |S''| == |S'| - 1
ensures S'' <= S
ensures SS' == (set s | s in (S - S'') :: {s})
ensures counter == counter_in + PolyAddSingletonSourceSet_simple(U, S, k)
{
  counter := counter_in;
  var s :| s in S';
  counter := counter + |U|;
  S'' := S' - {s};
  counter := counter + |S|*|U|;
  var s_set:set<set<int>> := {s};
  counter := counter + |U|;
  SS' := SS + {s_set};
  counter := counter + |S|*|U|;
}


ghost function PolyAddIncidentSourceSet_simple(U:set<int>, S:set<set<int>>, k:nat) : (o:nat)
{
  3*|S|*|U| + 2*|U| + 1
}
ghost function PolyBuildIncidenceSet_simple(U:set<int>, S:set<set<int>>, k:nat) : (o:nat)
{
  3*|S|*|S|*|U| + 2*|S|*|U|*|U| + 4*|S|*|U| + 3*|S| + |U| + 2
}
ghost function PolyContainsEmptySetLoop_simple(U:set<int>, S:set<set<int>>, k:nat) : (o:nat)
{
  |S|*|U| + |U| + 1
}
ghost function PolyAddSingletonSourceSet_simple(U:set<int>, S:set<set<int>>, k:nat) : (o:nat)
{
  2*|S|*|U| + 2*|U|
}


ghost function PolyTransformHittingSetToSetCover_simple(U:set<int>, S:set<set<int>>, k:nat) : (o:nat)
  ensures 2*|S|*|U| + 2 + |S|*(PolyAddSingletonSourceSet_simple(U, S, k) + 1) <= o
  ensures |S|*|U| + |U| + 2 + |U|*(PolyBuildIncidenceSet_simple(U, S, k) + 1) <= o
{
  calc == {
    |S|*|U| + |U| + 2 + |U|*(PolyBuildIncidenceSet_simple(U, S, k) + 1);
    |S|*|U| + |U| + 2 + |U|*(3*|S|*|S|*|U| + 2*|S|*|U|*|U| + 4*|S|*|U| + 3*|S| + |U| + 3);
    |S|*|U| + |U| + 2 + (3*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 4*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + 3*|U|);
    3*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 4*|S|*|U|*|U| + 4*|S|*|U| + |U|*|U| + 4*|U| + 2;
  }
  calc == {
    2*|S|*|U| + 2 + |S|*(PolyAddSingletonSourceSet_simple(U, S, k) + 1);
    2*|S|*|U| + 2 + |S|*(2*|S|*|U| + 2*|U| + 1);
    2*|S|*|U| + 2 + (2*|S|*|S|*|U| + 2*|S|*|U| + |S|);
    2*|S|*|S|*|U| + 4*|S|*|U| + |S| + 2;
  }
  3*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 2*|S|*|S|*|U| + 4*|S|*|U|*|U| + 4*|S|*|U| + |U|*|U| + |S| + 4*|U| + 2
}
