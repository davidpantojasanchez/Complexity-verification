include "../Problems/HittingSet.dfy"
include "../Problems/SetCover.dfy"
/*
Reduction Set Cover -> Hitting Set
*/

ghost function SetCoverToHittingSet<T>(U: set<T>, S: set<set<T>>, k: nat) : (r:(set<set<T>>, set<set<set<T>>>, nat))
  requires SetCoverValidInstance(U, S)
  ensures HittingSetValidInstance(r.0, r.1)
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  (S, newS, k)
}

//DEMOSTRACION DE QUE SON EQUIVALENTES
// es decir:  SetCover(U,S,k) <==> HittingSet(HU,HS,Hk)
// siendo (HU,HS,Hk) la transformacion de (U,S,k)

lemma set_cover_to_hitting_set_correct<T>(U:set<T>, S:set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
              SetCover(U,S,k) <==> HittingSet(HU,HS,Hk)
{
  var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
  set_cover_to_hitting_set_backward(U,S,k);
  set_cover_to_hitting_set_forward(U,S,k);
} 

// Vamos a demostrar estos dos lemas:
//El primer lema demuestra HS ==> SC

 lemma set_cover_to_hitting_set_backward<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
              SetCover(U,S,k) <== HittingSet(HU,HS,Hk)
{
  var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
  if (HittingSet(HU,HS,Hk)) {  
    var C:set<set<T>> :| HittingSetCertificate(HU, HS, Hk, C);
    assert HittingSetCertificate(HU, HS, Hk, C);
    //Veamos que se cumple que C es cobertura de U, es decir, IsCover(U,C)
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

//El segundo lema demuestra SC ==> HS

//Usamos dos lemas auxiliares que hacen falta para demostrar 
//que la propia cobertura es el Hitting-set
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

//Version generalizada del anterior
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

lemma set_cover_to_hitting_set_forward<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires SetCoverValidInstance(U, S)
  ensures var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
              SetCover(U,S,k) ==> HittingSet(HU,HS,Hk)
{ 
  var (HU,HS,Hk) := SetCoverToHittingSet(U,S,k);
  if (U == {}) {
    //Este es un caso especial algo raro 
    //pero no lo he quitado en las precondiciones
    //Solo hay dos casos S={} o S={{}}
    if (S == {}) {}
    else if (S == {{}}) { 
      var C := {};
      assert C <= U && |C| <= Hk;
      assert HittingSetCertificate(HU, HS, Hk, {});
      assert HittingSet(HU,HS,Hk);
    }
    else {
      //Este caso no es posible
      //Lo demostramos por reduccion al absurdo
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
      //Tenemos que demostrar que el mismo C es Hitting set
      //Por ser C cobertura sabemos que cada elemento de U
      //corresponde a un conjunto de newS cuyos conjuntos contienen a u
      //Usamos el lema auxiliar
      every_cover_intersects_incidence_set(U,S,C);
      assert HittingSetCertificate(HU, HS, Hk, C);
      //assert forall s | s in HS :: C * s != {};
      //assert exists s:set<set<T>> :: HitsAllSets(HS, s) && |s| <= Hk && s <= HU;
    }
  } 
}
