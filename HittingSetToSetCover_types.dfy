include "HittingSet.dfy"
include "SetCover.dfy"
include "Types.dfy"


method HittingSet_to_SetCover_Method(U: Set<int>, S: SetSet<int>, k: nat) returns (r:(SetSet<int>, SetSetSet<int>, int), ghost counter:nat)
  requires forall s | s in S.Model() ::  s <= U.Model() 
  requires U.Model() == U.Universe()
  requires S.Model() == S.Universe()
  //ensures forall s | s in r.1 :: s <= r.0
  //ensures isCover(r.0, r.1)
  {
    counter := 0;
    //var newS: set<set<set<int>>> := (set u | u in U :: (set s | s in S && u in s));
    var newS:SetSetSet<int>; newS, counter := NewSetSetSet(counter);
    var U'; U', counter := U.Copy(counter);
    var U'_empty:bool; U'_empty, counter := U'.Empty(counter);

    assert counter <= U.Size() + 2;
    ghost var counter_outer := counter;
    while (!U'_empty)
      decreases |U'.Model()|
      invariant U'_empty == (U'.Model() == {})
    {
      ghost var U'_aux := U'.Model();
      ghost var counter_outer_aux := counter;

      var u:int; u, counter := U'.Pick(counter);
      U', counter := U'.Remove(u, counter);

      var sets_in_S_that_contain_u:SetSet<int>; sets_in_S_that_contain_u, counter := NewSetSet_params(S.Model(), S.maximumSizeElements(), counter);
      var S':SetSet<int>; S', counter := S.Copy(counter);

      var S'_empty:bool; S'_empty, counter := S'.Empty(counter);
      //assert counter <= 1 + U.Size() + 1 + S.Size() + 1;

      ghost var counter_inner := counter;
      while (!S'_empty)
        decreases |S'.Model()|
        invariant S'_empty == (S'.Model() == {})
        invariant correct_SetSet(S')
        invariant correct_SetSet(sets_in_S_that_contain_u)
        invariant in_universe_SetSet(S', S)
        invariant in_universe_SetSet(sets_in_S_that_contain_u, S)
        invariant counter <= counter_inner + (2*S.maximumSizeElements() + 2*S.Size() + 1)*(|S.Model()| - |S'.Model()|)
      {
        ghost var S'_aux := S'.Model();
        ghost var counter_inner_aux := counter;

        var s:Set<int>; s, counter := S'.Pick(counter);
        S', counter := S'.Remove(s, counter);

        //if (u in s) {
        //  sets_in_S_that_contain_u := sets_in_S_that_contain_u + {s};
        //}
        var s_contains_u:bool; s_contains_u, counter := s.Contains(u, counter);
        if (s_contains_u) {
          sets_in_S_that_contain_u, counter := sets_in_S_that_contain_u.Add(s, counter);
        }
        //assert counter <= (counter_inner + S.maximumSizeElements() + S.Size() + S.maximumSizeElements() + sets_in_S_that_contain_u.Size());
        //assert sets_in_S_that_contain_u.maximumSizeElements() == S.maximumSizeElements();
        //assert sets_in_S_that_contain_u.Size() <= S.maximumSizeElements();

        S'_empty, counter := S'.Empty(counter);
        assert counter <= counter_inner_aux + (2*S.maximumSizeElements() + 2*S.Size() + 1);
        assert |S'_aux| - 1 == |S'.Model()|;
        assert counter <= counter_inner + (2*S.maximumSizeElements() + 2*S.Size() + 1)*(|S.Model()| - |S'.Model()|);
      }
      
      newS, counter := newS.Add(sets_in_S_that_contain_u, counter);
      
      U'_empty, counter := U'.Empty(counter);
    }
    //assert newS == (set u | u in U :: (set s | s in S && u in s));

    assume false;
    /*
    if ({} in S) then (S, (set s | s in S :: {s}), 0)
    else
    tisCover(U,S);
    (S, newS, k)
    */
    var empty_set:Set<int>; empty_set, counter := NewSet(counter);
    var S_contains_empty:bool; S_contains_empty, counter := S.Contains(empty_set, counter);
    if (S_contains_empty) {
      
      var S':SetSet<int>; S', counter := S.Copy(counter);
      var S'_empty:bool; S'_empty, counter := S'.Empty(counter);
      while (!S'_empty) {
        var s:Set<int>; s, counter := S'.Pick(counter);
        S', counter := S'.Remove(s, counter);

        var set_of_s:SetSet<int>; set_of_s, counter := NewSetSet<int>(counter);
        set_of_s, counter := set_of_s.Add(s, counter);

        newS, counter := newS.Add(set_of_s, counter);
        S'_empty, counter := S'.Empty(counter);
      }

      return (S, newS, 0), counter;
      
    }
    else {
      return (S, newS, k), counter;
    }

  }

