include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
include "../Reductions/ReductionHittingSetToSetCover.dfy"
include "../Arithmetic/BitLengths.dfy"
include "../Foundations/CollectionLaws.dfy"
include "../Foundations/LoopCosts.dfy"


method TransformHittingSetToSetCover_simple<T(==)>(instance:HittingSetModel<T>) returns (r:SetCoverModel<set<T>>, ghost counter:nat)
  requires HittingSetValidInstance(instance)
  ensures r == HittingSetToSetCover(instance)
  ensures counter <= BudgetTransformHittingSetToSetCover_simple(instance.universe, instance.sets, instance.k)
{
  var U, S, k := instance.universe, instance.sets, instance.k;
  counter := 0;
  var SS:set<set<set<T>>> := {}; counter := counter + 1;
  // Edge case
  var S_contains_empty:bool := {} in S; counter := counter + |S|*|U|;
  if (S_contains_empty) {
    var S' := S; counter := counter + |S|*|U|;
    while (S' != {})
      decreases |S'|
      invariant S' <= S
      invariant SS == (set s | s in (S - S') :: {s})
      invariant counter <= 2*|S|*|U| + 1 + (|S| - |S'|)*(CostAddSingletonSourceSet_simple(U, S, k) + 1)
    {
      counter := counter + 1;
      S', SS, counter := AddSingletonSourceSet_simple(U, S, k, S', SS, counter);
    }
    counter := counter + 1;
    difference_empty_set(S, S');
    return SetSystemModel(S, SS, 0), counter;
  }
  // Regular case
  var U' := U; counter := counter + |U|;
  while (U' != {})
    decreases |U'|
    invariant U' <= U
    invariant SS == (set u | u in (U - U') :: (set s | s in S && u in s))
    invariant counter <= |S|*|U| + |U| + 1 + (|U| - |U'|)*(BudgetBuildIncidenceSet_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    U', SS, counter := BuildIncidenceSet_simple(U, S, k, U', SS, counter);
  }
  counter := counter + 1;
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
  
  return SetSystemModel(S, SS, k), counter;
}


method BuildIncidenceSet_simple<T(==)>(U:set<T>, S:set<set<T>>, k:nat, U':set<T>, SS:set<set<set<T>>>, ghost counter_in:nat)
    returns (U'':set<T>, SS':set<set<set<T>>>, ghost counter:nat)
// Problem requirements
requires U' != {}
requires SetSystemMembersWithinUniverse(U, S)
requires U' <= U
requires SS == (set u | u in (U - U') :: (set s | s in S && u in s))
ensures |U''| == |U'| - 1
ensures U'' <= U
ensures SS' == (set u | u in (U - U'') :: (set s | s in S && u in s))
ensures counter <= counter_in + BudgetBuildIncidenceSet_simple(U, S, k)
{
  counter := counter_in;
  var u :| u in U';
  counter := counter + 1;
  U'' := U' - {u};
  counter := counter + |U|;

  var sets_in_S_that_contain_u:set<set<T>> := {};
  var S' := S;
  counter := counter + |S|;
  while (S' != {})
    decreases |S'|
    invariant S' <= S
    invariant sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
    invariant counter <= counter_in + |S| + |U| + 1 + (|S| - |S'|)*(BudgetAddIncidentSourceSet_simple(U, S, k) + 1)
  {
    counter := counter + 1;
    S', sets_in_S_that_contain_u, counter := AddIncidentSourceSet_simple(U, S, k, S', u, sets_in_S_that_contain_u, counter);
  }
  counter := counter + 1;
  SS' := SS + {sets_in_S_that_contain_u};
  counter := counter + |S|*|U|*|U|;

  calc <= {
    counter;
    counter_in + |S| + |U| + 2 + |S|*(BudgetAddIncidentSourceSet_simple(U, S, k) + 1) + |S|*|U|*|U|;
    counter_in + 3*|S|*|S|*|U| + |S|*|U|*|U| + 2*|S|*|U| + 3*|S| + |U| + 2;
    counter_in + BudgetBuildIncidenceSet_simple(U, S, k);
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


method AddIncidentSourceSet_simple<T(==)>(U:set<T>, S:set<set<T>>, k:nat, S':set<set<T>>, u:T, sets_in_S_that_contain_u:set<set<T>>, ghost counter_in:nat)
    returns (S'':set<set<T>>, sets_in_S_that_contain_u':set<set<T>>, ghost counter:nat)
// Problem requirements
requires S' != {}
requires SetSystemMembersWithinUniverse(U, S)
requires S' <= S
requires sets_in_S_that_contain_u == (set s | s in (S - S') && u in s)
ensures |S''| == |S'| - 1
ensures S'' <= S
ensures sets_in_S_that_contain_u' == (set s | s in (S - S'') && u in s)
ensures counter <= counter_in + BudgetAddIncidentSourceSet_simple(U, S, k)
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


method AddSingletonSourceSet_simple<T(==)>(U:set<T>, S:set<set<T>>, k:nat, S':set<set<T>>, SS:set<set<set<T>>>, ghost counter_in:nat)
    returns (S'':set<set<T>>, SS':set<set<set<T>>>, ghost counter:nat)
// Problem requirements
requires S' != {}
requires SetSystemMembersWithinUniverse(U, S)
requires S' <= S
requires SS == (set s | s in (S - S') :: {s})
ensures |S''| == |S'| - 1
ensures S'' <= S
ensures SS' == (set s | s in (S - S'') :: {s})
ensures counter == counter_in + CostAddSingletonSourceSet_simple(U, S, k)
{
  counter := counter_in;
  var s :| s in S';
  counter := counter + |U|;
  S'' := S' - {s};
  counter := counter + |S|*|U|;
  var s_set:set<set<T>> := {s};
  counter := counter + |U|;
  SS' := SS + {s_set};
  counter := counter + |S|*|U|;
}


ghost function BudgetAddIncidentSourceSet_simple<T>(U:set<T>, S:set<set<T>>, k:nat) : (o:nat)
{
  3*|S|*|U| + 2*|U| + 1
}
ghost function BudgetBuildIncidenceSet_simple<T>(U:set<T>, S:set<set<T>>, k:nat) : (o:nat)
{
  3*|S|*|S|*|U| + 2*|S|*|U|*|U| + 4*|S|*|U| + 3*|S| + |U| + 2
}
ghost function CostAddSingletonSourceSet_simple<T>(U:set<T>, S:set<set<T>>, k:nat) : (o:nat)
{
  2*|S|*|U| + 2*|U|
}


ghost function BudgetTransformHittingSetToSetCover_simple<T>(U:set<T>, S:set<set<T>>, k:nat) : (o:nat)
  ensures 2*|S|*|U| + 2 + |S|*(CostAddSingletonSourceSet_simple(U, S, k) + 1) <= o
  ensures |S|*|U| + |U| + 2 + |U|*(BudgetBuildIncidenceSet_simple(U, S, k) + 1) <= o
{
  calc == {
    |S|*|U| + |U| + 2 + |U|*(BudgetBuildIncidenceSet_simple(U, S, k) + 1);
    |S|*|U| + |U| + 2 + |U|*(3*|S|*|S|*|U| + 2*|S|*|U|*|U| + 4*|S|*|U| + 3*|S| + |U| + 3);
    |S|*|U| + |U| + 2 + (3*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 4*|S|*|U|*|U| + 3*|S|*|U| + |U|*|U| + 3*|U|);
    3*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 4*|S|*|U|*|U| + 4*|S|*|U| + |U|*|U| + 4*|U| + 2;
  }
  calc == {
    2*|S|*|U| + 2 + |S|*(CostAddSingletonSourceSet_simple(U, S, k) + 1);
    2*|S|*|U| + 2 + |S|*(2*|S|*|U| + 2*|U| + 1);
    2*|S|*|U| + 2 + (2*|S|*|S|*|U| + 2*|S|*|U| + |S|);
    2*|S|*|S|*|U| + 4*|S|*|U| + |S| + 2;
  }
  3*|S|*|S|*|U|*|U| + 2*|S|*|U|*|U|*|U| + 2*|S|*|S|*|U| + 4*|S|*|U|*|U| + 4*|S|*|U| + |U|*|U| + |S| + 4*|U| + 2
}
