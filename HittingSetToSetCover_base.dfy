include "HittingSet.dfy"
include "SetCover.dfy"
include "ReductionHittingSetToSetCover.dfy"



method HittingSet_to_SetCover_Method(U: set<int>, S: set<set<int>>, k: nat) returns (r:(set<set<int>>, set<set<set<int>>>, int))
  requires forall s | s in S ::  s <= U
  //ensures r == HittingSet_to_SetCover(U, S, k)
  {
    //var newS: set<set<set<int>>> := (set u | u in U :: (set s | s in S && u in s));
    var newS:set<set<set<int>>> := {};
    var U' := U;
    while (U' != {})
    {
      var u :| u in U';
      U' := U' - {u};

      var sets_in_S_that_contain_u:set<set<int>> := {};
      var S' := S;
      while (S' != {}) {
        var s :| s in S';
        S' := S' - {s};

        //if (u in s) {
        //  sets_in_S_that_contain_u := sets_in_S_that_contain_u + {s};
        //}
        var s_contains_u:bool := false;
        var s' := s;
        while (s' != {}) {
          var e :| e in s';
          s' := s' - {e};

          if (e == u) {
            s_contains_u := true;
          }
        }
        if (s_contains_u) {
          sets_in_S_that_contain_u := sets_in_S_that_contain_u + {s};
        }

      }

      newS := newS + {sets_in_S_that_contain_u};
    }
    //assert newS == (set u | u in U :: (set s | s in S && u in s));


    
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
      S' := S' - {s};

      if (s == {}) {
        S_contains_empty := true;
      }
    }
    if (S_contains_empty) {
      
      var S' := S;
      while (S' != {})
      {
        var s :| s in S';
        S' := S' - {s};
        newS := newS + {{s}};
      }

      return (S, newS, 0);
      
    }
    else {
      return (S, newS, k);
    }

  }

