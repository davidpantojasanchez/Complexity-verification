include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"


method TransformHittingSetToSetCover_base<T(==)>(instance:HittingSetModel<T>) returns (r:SetCoverModel<set<T>>)
  requires HittingSetValidInstance(instance)
  ensures r == HittingSetToSetCover(instance)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  var SS:set<set<set<T>>> := {};
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
    difference_empty_set(S, S');
    return SetSystemModel(S, SS, 0);
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
  difference_empty_set(U, U');
  ghost var target := HittingSetToSetCover(instance);
  assert SS == target.sets by {
    forall incidence | incidence in SS
      ensures incidence in target.sets
    {
      var u :| u in U && (set s | s in S && u in s) == incidence;
    }
    forall incidence | incidence in target.sets
      ensures incidence in SS
    {
      var u :| u in U && (set s | s in S && u in s) == incidence;
    }
  }

  return SetSystemModel(S, SS, k);
}


method BuildIncidenceSet_base<T(==)>(U:set<T>, S:set<set<T>>, k:nat, U':set<T>, SS:set<set<set<T>>>) returns (U'':set<T>, SS':set<set<set<T>>>)
  requires U' != {}
  requires U' <= U
  requires SS == (set u | u in (U - U') :: (set s | s in S && u in s))
  ensures |U''| == |U'| - 1
  ensures U'' <= U
  ensures SS' == (set u | u in (U - U'') :: (set s | s in S && u in s))
{
  var u :| u in U';
  U'' := U' - {u};

  var sets_in_S_that_contain_u:set<set<T>> := {};
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


method AddIncidentSourceSet_base<T(==)>(U:set<T>, S:set<set<T>>, k:nat, S':set<set<T>>, u:T, sets_in_S_that_contain_u:set<set<T>>)
    returns (S'':set<set<T>>, sets_in_S_that_contain_u':set<set<T>>)
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


method AddSingletonSourceSet_base<T(==)>(U:set<T>, S:set<set<T>>, k:nat, S':set<set<T>>, SS:set<set<set<T>>>) returns (S'':set<set<T>>, SS':set<set<set<T>>>)
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
