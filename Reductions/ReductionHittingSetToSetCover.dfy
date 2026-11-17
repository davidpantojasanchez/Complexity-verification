include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"

/*
Reduction Hitting Set -> Set Cover
*/

ghost function HittingSetToSetCover<T>(instance:HittingSetModel<T>) : (r:SetCoverModel<set<T>>)
  requires HittingSetValidInstance(instance)
  ensures SetCoverValidInstance(r)
  ensures {} !in instance.sets ==> r == SetSystemModel(instance.sets,
    (set u | u in instance.universe :: (set s | s in instance.sets && u in s)), instance.k)
{
  var U, S := instance.universe, instance.sets;
  if {} in S then
    SetSystemModel(S, (set s | s in S :: {s}), 0) // The empty source set has no hitting set.
  else
    incidence_covers_setset(U, S);
    SetSystemModel(S, (set u | u in U :: (set s | s in S && u in s)), instance.k)
}

// The incidence construction preserves solutions in both directions.
lemma hitting_set_to_set_cover_correct<T(!new)>(instance:HittingSetModel<T>)
  requires HittingSetValidInstance(instance)
  ensures HittingSet(instance) <==> SetCover(HittingSetToSetCover(instance))
{
  hitting_set_to_set_cover_forward(instance);
  hitting_set_to_set_cover_backward(instance);
}

ghost function IncidentSets<T>(S:set<set<T>>, element:T) : (incidence:set<set<T>>)
  ensures incidence <= S
{ set s | s in S && element in s }

lemma incidence_covers_setset<T>(U:set<T>, S:set<set<T>>)
  requires SetSystemMembersWithinUniverse(U, S)
  requires {} !in S
  ensures IsCover(S, set u | u in U :: (set s | s in S && u in s))
{
  var incidences := set u | u in U :: (set s | s in S && u in s);
  forall s | s in S
    ensures exists incidence | incidence in incidences :: s in incidence
  {
    assert s != {};
    var u :| u in s;
    assert u in U;
    var incidence := set member | member in S && u in member;
    assert s in incidence && incidence in incidences;
  }
}

lemma incidence_cardinality_bound_setsetset<T>(S:set<set<T>>, C:set<T>, CS:set<set<set<T>>>)
  requires CS == (set x | x in C :: (set s | s in S && x in s))
  ensures |CS| <= |C|
  decreases |C|
{
  if C == {} {
    assert CS == {};
  } else {
    var x :| x in C;
    var rest := C - {x};
    var restIncidences := set y | y in rest :: (set s | s in S && y in s);
    incidence_cardinality_bound_setsetset(S, rest, restIncidences);
    assert C == rest + {x};
    assert CS == restIncidences + {(set s | s in S && x in s)};
  }
}

lemma hitting_set_to_set_cover_forward<T>(instance:HittingSetModel<T>)
  requires HittingSetValidInstance(instance)
  ensures HittingSet(instance) ==> SetCover(HittingSetToSetCover(instance))
{
  if HittingSet(instance) {
    var U, S := instance.universe, instance.sets;
    var C :| C <= U && HittingSetCertificate(instance, C);
    assert {} !in S;
    var target := HittingSetToSetCover(instance);
    var CS := set x | x in C :: (set s | s in S && x in s);

    forall s | s in target.universe
      ensures exists incidence | incidence in CS :: s in incidence
    {
      assert C * s != {};
      var x :| x in C * s;
      var incidence := set member | member in S && x in member;
      assert s in incidence && incidence in CS;
    }
    incidence_cardinality_bound_setsetset(S, C, CS);
    assert SetCoverCertificate(target, CS);
  }
}

// Choose a source representative by its incidence set.
ghost function IncidenceRepresentative<T>(U:set<T>, S:set<set<T>>, incidence:set<set<T>>) : (representative:T)
  requires SetSystemMembersWithinUniverse(U, S)
  requires exists u | u in U :: IncidentSets(S, u) == incidence
  ensures representative in U && IncidentSets(S, representative) == incidence
{
  var representative :| representative in U && IncidentSets(S, representative) == incidence;
  representative
}

// The map from selected incidences to representatives is inverted by incidence.
lemma incidence_representatives<T(!new)>(U:set<T>, S:set<set<T>>, CS:set<set<set<T>>>) returns (C:set<T>)
  requires SetSystemMembersWithinUniverse(U, S)
  requires forall incidence | incidence in CS :: exists u | u in U :: IncidentSets(S, u) == incidence
  ensures C <= U
  ensures Image_set(C, u => IncidentSets(S, u)) == CS
  ensures |C| == |CS|
{
  C := set incidence | incidence in CS :: IncidenceRepresentative(U, S, incidence);
  var encode := (u:T) => IncidentSets(S, u);

  forall u | u in C
    ensures u in U && encode(u) in CS
    ensures IncidenceRepresentative(U, S, encode(u)) == u
  {
    var incidence :| incidence in CS && IncidenceRepresentative(U, S, incidence) == u;
  }
  forall first, second | first in C && second in C && encode(first) == encode(second)
    ensures first == second
  {}
  injective_image_cardinality_set(C, encode);
  forall incidence | incidence in CS
    ensures incidence in Image_set(C, encode)
  {
    var u := IncidenceRepresentative(U, S, incidence);
    assert u in C;
  }
  assert Image_set(C, encode) == CS;
}

lemma hitting_set_to_set_cover_backward<T(!new)>(instance:HittingSetModel<T>)
  requires HittingSetValidInstance(instance)
  ensures SetCover(HittingSetToSetCover(instance)) ==> HittingSet(instance)
{
  var target := HittingSetToSetCover(instance);
  if SetCover(target) {
    var U, S := instance.universe, instance.sets;
    var CS :| CS <= target.sets && SetCoverCertificate(target, CS);
    if {} in S {
      assert CS == {};
      assert !IsCover(S, {});
    } else {
      forall incidence | incidence in CS
        ensures exists u | u in U :: IncidentSets(S, u) == incidence
      {
        assert incidence in target.sets;
        var u :| u in U && (set member | member in S && u in member) == incidence;
        assert IncidentSets(S, u) == incidence;
      }
      var C := incidence_representatives(U, S, CS);
      forall s | s in S
        ensures s * C != {}
      {
        var incidence :| incidence in CS && s in incidence;
        var u :| u in C && IncidentSets(S, u) == incidence;
        assert u in s * C;
      }
      assert HittingSetCertificate(instance, C);
    }
  }
}
