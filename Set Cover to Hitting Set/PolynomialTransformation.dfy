
include "SetCoverToHittingSet.dfy"
include "HittingSetToSetCoverClara.dfy"
include "SetModule.dfy"

method method_SetCover_to_HittingSet<T>(U: set<T>, S: set<set<T>>, k: nat) returns (r:(set<set<T>>, set<set<set<T>>>, int), ghost counter:int)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures r == SetCover_to_HittingSet<T>(U, S, k)
  ensures counter <= 2*|U| + 2*|S|*|S|*|U| + |S|*|U|*|U| + 2*|S|*|U| + 3*|U|*|U|
{
  //assert |U| >= 0 && |S| >= 0;

  ghost var sizeT:int := 1;
  counter := 0;

  var HU := S;
  var Hk := k;

  var HS:set<set<set<T>>> := {};
  var U2 := U;

  while 0<|U2|
    decreases U2
    
    invariant forall s | s in HS :: s <= HU
    invariant HS == (set u | u in (U - U2) :: (set s | s in S && u in s))
    
    invariant |HS| <= |U - U2|
    invariant counter <= ((2 + (2*|S| + |U| + 2)*(|S|))  + 3*|U|) * |U - U2|

    //invariant |U| >= 0 && |S| >= 0
  {

    ghost var prevDifference := |U - U2|;
    ghost var prevCounter := counter;
    counter := counter + 1;
    //var v :| v in U2;
    var v;
    v, counter := SetMod.pick(U2, 1, counter);
    assert counter == prevCounter + 2;

    var S2 := S;
    assert counter == prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S| - |S2|);
    var hs:set<set<T>> := {};

    while 0<|S2|
      decreases S2

      invariant hs == (set s | s in (S - S2) && v in s)
      invariant HS == (set u | u in (U - U2) :: (set s | s in S && u in s))

      invariant forall s | s in S2 :: s <= U
      invariant S2 <= S
      invariant hs <= S

      invariant counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S| - |S2|)
 
      //invariant |U| >= 0 && |S| >= 0
    {
      ghost var increment := 1 + |U| + |S|*|U| + |U| + |S|*|U|;
      assert 1 + |U| + |S|*|U| + |U| + |S|*|U| == increment;

      ghost var counter_iteration_loop := counter;
      ghost var prev_S_minus_S2 := |S| - |S2|;

      counter := counter + 1;
      //var s :| s in S2;
      var s:set<T>;
      s, counter := SetMod.pick(S2, |U|, counter);        // |U|
      assert counter <= counter_iteration_loop + 1 + |U|;

      if_subset_then_smaller(s, U);
      if_subset_then_smaller(S2, S);

      assert |S| - |S2| == prev_S_minus_S2;
      //S2 := S2 - {s};
      S2, counter := SetMod.remove(S2, s, |U|, counter);  // |S|*|U|
      assert counter <= counter_iteration_loop + 1 + |U| + |S|*|U|;

      assert |S| - |S2| == prev_S_minus_S2 + 1;

      var cont:bool;
      cont, counter := SetMod.contains(s, v, 1, counter);  // |U|
      assert counter <= counter_iteration_loop + 1 + |U| + |S|*|U| + |U|;
      if (cont == true) { //v in s {
        //hs := hs + {s};
        assert s in S;
        hs, counter := SetMod.add(hs, s, |U|, counter);  // |S|*|U|
        assert hs <= S;
        if_subset_then_smaller(hs, S);
      }
      
      assert counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S| - |S2|)
      by {
        assert counter <= counter_iteration_loop + 1 + |U| + |S|*|U| + |U| + |S|*|U|;
        assert counter <= counter_iteration_loop + increment;

        assert hs == (set s | s in (S - S2) && v in s);
        assert HS == (set u | u in (U - U2) :: (set s | s in S && u in s));

        assert forall s | s in S2 :: s <= U;
        assert S2 <= S;
        assert hs <= S;

        assert counter_iteration_loop <= prevCounter + 2 + (increment)*prev_S_minus_S2;
        assert |S| - |S2| == prev_S_minus_S2 + 1;

        assert counter <= prevCounter + 2 + (increment)*prev_S_minus_S2 + increment;
        assert counter <= prevCounter + 2 + (increment)*(prev_S_minus_S2 + 1);
      }
    }
  
    assert counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S|);
    
    //HS := HS + {hs};
    ghost var prevHS := HS;
    HS, counter := SetMod.add(HS, hs, |U|*|S|, counter);
    assert |HS| <= |prevHS| + 1;


    assert |HS| <= |U|;
    assert |U| >= 0 && |S| >= 0;
    //assert 0 <= |U|;
    //assert 0 <= |S|*|U|;
    assert |HS|*(|U|*|S|) <= |U|*(|U|*|S|);

    assert counter <= prevCounter + 2 + (1 + |U| + |S|*|U| + |U| + |S|*|U|)*(|S|) + |U|*|U|*|S|;
    
    assume false;

    ghost var U3 := U2;
    //U2 := U2 - {v};
    U2, counter := SetMod.remove(U2, v, 1, counter);
    assert hs == (set s | s in (S - S2) && v in s);
    assert prevHS == (set u | u in (U - U3) :: (set s | s in S && u in s));
    assert (U - (U2 + {v})) == (U - U3);
    assert prevHS + {hs} == (set u | u in (U - (U2 + {v})) :: (set s | s in S && u in s)) + {(set s | s in (S - S2) && v in s)};

    assert forall s | s in S2 :: !(v in s);

    if_S2_has_no_set_with_v_then_can_remove_safely(S, S2, v);
    assert {(set s | s in S && v in s)} == {(set s | s in (S - S2) && v in s)};

    assert (set u | u in {v} :: (set s | s in S && u in s)) == {(set s | s in (S - S2) && v in s)};

    assert (set u | u in (U - (U2 + {v})) :: (set s | s in S && u in s))
            + (set u | u in {v} :: (set s | s in S && u in s))
            == (set u | u in (U - (U2 + {v})) + {v} :: (set s | s in S && u in s));
    assert (U - (U2 + {v})) + {v} == (U - U2 + {v});

    assert prevHS + {hs} == (set u | u in (U - U2) :: (set s | s in S && u in s));
    
    //assume false;
  }
  //assume false;
  assert counter <= 2*|U| + 2*|S|*|S|*|U| + |S|*|U|*|U| + 2*|S|*|U| + 3*|U|*|U|;

  r := (HU, HS, Hk);
  assert r == (HU, HS, Hk);

  ghost var e := SetCover_to_HittingSet<T>(U, S, k);
  assert HU == e.0;
  assert Hk == e.2;

  assert HS == (set u | u in (U - U2) :: (set s | s in S && u in s));
  assert U2 == {};
  assert (U - {}) == U;
  assert HS == (set u | u in U :: (set s | s in S && u in s));

  assert HS == e.1;

  assert r == SetCover_to_HittingSet<T>(U, S, k);
}


lemma if_subset_then_smaller<T>(A:set<T>, B:set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  if |A| == 0 || |B| == 0 { // trivial base case
  }
  else if A <= B {
    var a:T :| a in A;
    if_subset_then_smaller(A - {a}, B - {a});
  }
}

lemma if_S2_has_no_set_with_v_then_can_remove_safely<T>(S:set<set<T>>, S2:set<set<T>>, v:T)
  decreases |S2|
  requires S2 <= S
  requires forall s | s in S2 :: !(v in s)
  ensures {(set s | s in S && v in s)}
       == {(set s | s in (S - S2) && v in s)}
{
  if |S2| == 0 {
    calc == {
      (set s | s in (S - S2) && v in s);
      (set s | s in (S - {}) && v in s);
      (set s | s in S && v in s);
    }
  }
  else {
    var a:set<T> :| a in S2;
    if_S2_has_no_set_with_v_then_can_remove_safely(S, S2 - {a}, v);
    assert {(set s | s in (S) && v in s)}
      == {(set s | s in ((S) - (S2 - {a})) && v in s)};
    assert !(v in a);
    calc == {
      (set s | s in (S - (S2 - {a})) && v in s);
      (set s | s in (S - S2) && v in s);
    }
  }
}


method {:verify false} method_HittingSet_to_SetCover(HU: set<int>, HS: set<set<int>>, Hk: nat) returns (r:(set<set<int>>, set<set<set<int>>>, int), ghost counter:int)
  requires forall s | s in HS ::  s <= HU
  ensures r == HittingSet_to_SetCover(HU, HS, Hk)
  //ensures counter <=
{
  var HU2 := HU;
  while 0<|HU2|
    decreases |HU2|
  {
    var u :| u in HU2;
    // ...
  }
}

