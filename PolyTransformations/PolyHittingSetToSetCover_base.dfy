include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Auxiliary/Lemmas.dfy"


method TransformHittingSetToSetCover_base(U:set<int>, S:set<set<int>>, k:nat) returns (r:(set<set<int>>, set<set<set<int>>>, nat))
  requires HittingSetValidInstance(U, S)
  ensures r == HittingSetToSetCover(U, S, k)
{
  var SS:set<set<set<int>>> := {};
  // Edge case
  var S_contains_empty:bool := {} in S;
  if (S_contains_empty) {
    var SS := {};
    var S' := S;
    while (S' != {})
      decreases |S'|
      invariant S' <= S
      invariant SS == (set s | s in (S - S') :: {s})
    {
      S', SS := AddSingletonSourceSet_base(U, S, k, S', SS);
    }
    SubtractionIdentity(S, S');
    return (S, SS, 0);
  }
  // Regular case
  var U' := U;
  while (U' != {})
    decreases |U'|
    invariant U' <= U
    invariant SS == (set u | u in (U - U') :: (set s | s in S && u in s))
  {
    U', SS := BuildIncidenceSet_base(U, S, k, U', SS);
  }
  SubtractionIdentity(U, U');

  return (S, SS, k);
}


method BuildIncidenceSet_base(U:set<int>, S:set<set<int>>, k:nat, U':set<int>, SS:set<set<set<int>>>) returns (U'':set<int>, SS':set<set<set<int>>>)
  requires U' != {}
  requires U' <= U
  requires SS == (set u | u in (U - U') :: (set s | s in S && u in s))
  ensures |U''| == |U'| - 1
  ensures U'' <= U
  ensures SS' == (set u | u in (U - U'') :: (set s | s in S && u in s))
{
  var u :| u in U';
  U'' := U' - {u};

  var sets_in_S_that_contain_u:set<set<int>> := {};
  var S' := S;
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
  {
    S', sets_in_S_that_contain_u := AddIncidentSourceSet_base(U, S, k, S', u, sets_in_S_that_contain_u);
  }

  SS' := SS + {sets_in_S_that_contain_u};

  assert SS' == (set v | v in (U - U'') :: (set s | s in S && v in s)) by {
    calc {
      SS';
      (set v | v in (U - U') :: (set s | s in S && v in s)) + {sets_in_S_that_contain_u};
      (set v | v in (U - U') :: (set s | s in S && v in s)) + {(set s | s in (S - S') && u in s)};
       {assert (S - S') == S;}
      (set v | v in (U - U') + {u} :: (set s | s in S && v in s));
      {assert (U - U'') == (U - U') + {u};}
      (set v | v in (U - U'') :: (set s | s in S && v in s));
    }
  }
}


method AddIncidentSourceSet_base(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, u:int, sets_in_S_that_contain_u:set<set<int>>) returns (S'':set<set<int>>, sets_in_S_that_contain_u':set<set<int>>)
  requires S' != {}
  requires S' <= S
  requires sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
  ensures |S''| == |S'| - 1
  ensures S'' <= S
  ensures sets_in_S_that_contain_u' == (set s | s in (S - S'') && u in s)
{
  sets_in_S_that_contain_u' := sets_in_S_that_contain_u;

  var s :| s in S';
  S'' := S' - {s};

  var s_contains_u:bool := u in s;

  if (s_contains_u) {
    sets_in_S_that_contain_u' := sets_in_S_that_contain_u + {s};
  }

}


method AddSingletonSourceSet_base(U:set<int>, S:set<set<int>>, k:nat, S':set<set<int>>, SS:set<set<set<int>>>) returns (S'':set<set<int>>, SS':set<set<set<int>>>)
  requires S' != {}
  requires S' <= S
  requires SS == (set s | s in (S - S') :: {s})
  ensures |S''| == |S'| - 1
  ensures S'' <= S
  ensures SS' == (set s | s in (S - S'') :: {s})
{
  var s :| s in S';
  S'' := S' - {s};
  SS' := SS + {{s}};
}
