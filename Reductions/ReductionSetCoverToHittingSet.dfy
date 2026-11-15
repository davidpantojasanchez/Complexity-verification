include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
// A set cover becomes a hitting set over the incidence sets.

ghost function SetCoverToHittingSet<T>(U: set<T>, S: set<set<T>>, k: nat) : (r:HittingSetInstance<set<T>>)
  requires SetCoverValidInstance(U, S)
  ensures HittingSetValidInstance(r.0, r.1)
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  (S, newS, k)
}

// The construction preserves solutions in both directions.

lemma set_cover_to_hitting_set_correct<T>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
              SetCover(U,S,k) <==> HittingSet(HU,HS,Hk)
{
  var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
  set_cover_to_hitting_set_backward(U,S,k);
  set_cover_to_hitting_set_forward(U,S,k);
}

// A hitting set of incidence sets covers the original universe.
lemma set_cover_to_hitting_set_backward<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
              SetCover(U,S,k) <== HittingSet(HU,HS,Hk)
{
  var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
  if (HittingSet(HU,HS,Hk)) {  
    var C:set<set<T>> :| HittingSetCertificate(HU, HS, Hk, C);
    assert HittingSetCertificate(HU, HS, Hk, C);
    // Each incidence set meets C, so every element is covered.
    forall u | u in U
    ensures exists s :: s in C && u in s
    {
      var ss := (set s | s in S && u in s);
      assert ss in HS && ss * C != {};
      var s :| s in ss * C;
      assert u in s;
    }
  }
}

// A cover hits every incidence set.
lemma set_cover_to_hitting_set_forward<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
              SetCover(U,S,k) ==> HittingSet(HU,HS,Hk)
{ 
  var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
  if (U == {}) {
    // Validity leaves only the empty family or the family containing the empty set.
    if (S == {}) {}
    else if (S == {{}}) { 
      var C := {};
      assert C <= U && |C| <= Hk;
      assert HittingSetCertificate(HU, HS, Hk, {});
      assert HittingSet(HU,HS,Hk);
    }
    else {
      // Any nonempty member would contain an element outside the empty universe.
      if (S!={} && S!={{}}) 
        { var s :| s in S && s!={} ;
          assert exists u :: u in s; 
          assert false;}
    }
  }
  else{
    if (SetCover(U,S,k)) {
      var C:set<set<T>> :| SetCoverCertificate(U, S, k, C);
      assert SetCoverCertificate(U, S, k, C);
      assert C <= HU && |C| <= Hk by
        {assert C!={};
        var s :| s in S && s !={};
        assert s in S-{{}};
        assert S-{{}}!={};}
      // The cover meets every incidence set.
      every_cover_intersects_incidence_set(U,S,C);
      assert HittingSetCertificate(HU, HS, Hk, C);
    }
  } 
}

// Every cover intersects the incidence set of each universe element.
lemma cover_intersects_incidence_set<T>(U:set<T>,u:T,S: set<set<T>>, C:set<set<T>>)
  requires forall s | s in S :: s <= U
  requires C <= S && IsCover(U, C)
  requires u in U
  ensures var ss := (set s | s in S && u in s);
          C * ss == (set s | s in C && u in  s) != {}
{
  assert C != {};
  var ss := (set s | s in S && u in s);
  var cs :| cs in C && u in cs;
  assert cs in ss * C;
  assert  ss * C != {};
}

// Lift the incidence property to every universe element.
lemma every_cover_intersects_incidence_set<T>(U:set<T>,S: set<set<T>>, C:set<set<T>>)
  requires forall s | s in S :: s <= U
  requires C <= S && IsCover(U, C)
  ensures  forall u | u in U ::
          (var ss := (set s | s in S && u in s);
          C * ss == (set s | s in C && u in  s) != {})
{
  forall u | u in U
  ensures (var ss := (set s | s in S && u in s);
          C * ss == (set s | s in C && u in  s) != {})
          {cover_intersects_incidence_set(U,u,S,C);}
}
