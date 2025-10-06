include "HittingSet.dfy"
include "SetCover.dfy"


method HittingSet_to_SetCover_Method(U: set<int>, S: set<set<int>>, k: nat) returns (r:(set<set<int>>, set<set<set<int>>>, int), counter:int)
  requires forall s | s in S ::  s <= U
  //ensures forall s | s in r.1 :: s <= r.0
  //ensures isCover(r.0, r.1)
  {
    counter := 0;
    //var newS: set<set<set<int>>> := (set u | u in U :: (set s | s in S && u in s));
    var newS:set<set<set<int>>> := {};
    var U' := U;
    counter := counter + |U|;

    assert counter == |U|;

    while (U' != {})
      invariant counter == |U| + (|U| - |U'|)*(|U|+ |S|*|U| + (1 + 2 + 3) + |U|*|S|*|U|)
    {
      var u :| u in U';
      U' := U' - {u};
      counter := counter + |U|;

      var sets_in_S_that_contain_u:set<set<int>> := {};
      var S' := S;
      counter := counter + |S|*|U|;
      while (S' != {}) {
        var s :| s in S';
        counter := counter + |S|*|U|;
        S' := S' - {s};
        counter := counter + |S|*|U|;

        //if (u in s) {
        //  sets_in_S_that_contain_u := sets_in_S_that_contain_u + {s};
        //}
        var s_contains_u:bool := false;
        var s' := s;
        counter := counter + |U|;
        while (s' != {})
        {
          var e :| e in s';
          counter := counter + |s|;
          s' := s' - {e};
          counter := counter + |s|;

          if (e == u) {
            s_contains_u := true;
          }
        }
        if (s_contains_u) {
          sets_in_S_that_contain_u := sets_in_S_that_contain_u + {s};
          counter := counter + |S|*|U|;
        }
      }

      newS := newS + {sets_in_S_that_contain_u};
      counter := counter + |U|*|S|*|U|;
    }


    /*
    if ({} in S) then (S, (set s | s in S :: {s}), 0)
    else
    tisCover(U,S);
    (S, newS, k)
    */
    var S_contains_empty:bool := false;
    var S' := S;
    while (S' != {}) {
      var s :| s in S';
      counter := counter + |S|*|U|;
      S' := S' - {s};
      counter := counter + |S|*|U|;

      if (s == {}) {
        S_contains_empty := true;
      }
    }
    if (S_contains_empty)  {
      
      var S' := S;
      counter := counter + |S|*|U|;
      while (S' != {})
      {
        var s :| s in S';
        counter := counter + |S|*|U|;
        S' := S' - {s};
        counter := counter + |S|*|U|;
        newS := newS + {{s}};
        counter := counter + |U|;
      }

      return (S, newS, 0), counter;
      
    }
    else {
      return (S, newS, k), counter;
    }

    assume false;
  }

