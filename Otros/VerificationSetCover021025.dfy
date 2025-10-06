include "Problems.dfy"
include "HittingSetToSetCover.dfy"

abstract module VerificationSetCover {
  import opened Problems
  import opened Auxiliary
  import opened ReductionSetCover

ghost function maximumSizeElements<T>(S:set<set<T>>):nat
ensures forall s | s in S :: maximumSizeElements(S) >= |s|
ensures exists s :: s in S && maximumSizeElements(S) == |s|


// * LA TRANSFORMACIÓN DE SET COVER ES POLINÓMICA

method HittingSet_to_SetCover_Method(U: set<int>, S: set<set<int>>, k: nat) returns (r:(set<set<int>>, set<set<set<int>>>, int))
  requires forall s | s in S ::  s <= U
  //ensures forall s | s in r.1 :: s <= r.0
  //ensures isCover(r.0, r.1)
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

    assume false;
  }


// * LA VERIFICACIÓN DE SET COVER ES POLINÓMICA

method verifySetCover<T>(U:set<T>, S:set<set<T>>, k:nat) returns (b:bool)
ensures b == (isCover(U,S) &&  |S| <= k)
{
  ghost var oldU := U;
  
  var emptyU;
  emptyU := |U| == 0;
  
  var e:T;
  var U':set<T>;
  U':=U;
  assert U' == U;
  assert U-U' == {} && |U-U'|==0;
  
  ghost var j := 0;
  b :=true;

  while !emptyU && b
   decreases (if !emptyU then 1 else 0)+|U'|
   invariant emptyU == (U' == {})
   invariant U' <= U
   invariant b == isCover(U-U',S)

   invariant j == (|U| - |U'|)
  {
    U', b, emptyU, j := body_loop_outer<T>(U, S, k, U', j);
  }
  
  var size;
  size := |S|;

  assert b == isCover(U,S) by {
    assert b == isCover(U-U',S);

    if U' == {} {
      assert b == isCover(U - U',S);
      assert U - U' == U;
      assert b == isCover(U,S);
    }
    else {
      assert !(!emptyU && b);
      assert emptyU || !b;
      assert emptyU == (U' == {});
      assert !(U' == {});
      assert !emptyU;
      assert !isCover(U-U',S);
    }

  }

  ghost var b' := b;
  assert emptyU && b ==> U-U' == U && isCover(U,S);
  b := emptyU && b && (size <= k);
  assert b == (emptyU && isCover(U,S) && size <= k);

  assert b == (isCover(U,S) &&  |S| <= k);
}




method body_loop_inner<T>(U:set<T>, S:set<set<T>>, k:nat, S'_:set<set<T>>, e:T, ghost i_:nat)
returns (S':set<set<T>>, empty:bool, found:bool, ghost i:nat)
  
  requires S'_ != {}
  requires S'_ <= S
  requires i_ == (|S| - |S'_|)
  requires (forall s| s in S-S'_:: e !in s)

  ensures S'<= S
  ensures empty == (S' == {}) 
  ensures !found ==> (forall s| s in S-S':: e !in s)
  ensures found ==> exists s:set<T> :: s in S && e in s
  ensures i == (|S| - |S'|)
  ensures i == i_+1

  ensures (!empty && !found) ==> (|S'| < |S'_|)
{
  S' := S'_;
  var s;
  s :| s in S';
  ghost var prev_S' := S';
  S' := S' - {s};
  found := e in s;
  empty := |S'| == 0;

  i := i_ + 1;
}



method body_loop_outer<T>(U:set<T>, S:set<set<T>>, k:nat, U'_:set<T>, ghost j_:nat) returns (U':set<T>, b:bool, emptyU:bool, ghost j:nat)
/*
while !emptyU && b
decreases (if !emptyU then 1 else 0)+|U'|
invariant emptyU == (U' == {})
invariant U' <= U
invariant b == isCover(U-U',S)

invariant j == (|U| - |U'|)
invariant counter <= counter_in + 2*poly(U,S) + j*(4*poly(U,S) + poly(U,S)*(4*poly(U,S)))
*/
requires U'_ <= U
requires j_ == (|U| - |U'_|)
requires U'_ != {}
requires isCover(U-U'_,S)

ensures (!emptyU) ==> (|U'| < |U'_|)
ensures emptyU == (U' == {})
ensures U' <= U
ensures b == isCover(U-U',S)
ensures j == (|U| - |U'|)
ensures j == j_ + 1

{
  U' := U'_;

  var e:T;
  e :| e in U';
  U' := U' - {e};
  var empty,S'; S':=S;
  empty := |S| == 0;
  var found := false;
  ghost var i := 0;

  while !empty && !found
    decreases (if !empty && !found then 1 else 0)+|S'|
    invariant empty == (S' == {}) 
    invariant U' == U'_-{e}
    invariant S'<= S
    invariant !found ==> (forall s| s in S-S':: e !in s)
    invariant found ==> exists s:set<T> :: s in S && e in s
    
    invariant i == (|S| - |S'|)
  {
    ghost var i_start_body := i;
    S', empty, found, i := body_loop_inner(U, S, k, S', e, i);

    assert S'<= S;
    assert empty == (S' == {});
    assert !found ==> (forall s| s in S-S':: e !in s);
    assert found ==> exists s:set<T> :: s in S && e in s;
    assert i == (|S| - |S'|);
  }

  b := found;
  assert b == isCover(U-U',S) by {
    assert isCover(U-U'_,S);
    if found {
      ghost var prev_difference := (U-U'_);
      assert forall elem | elem in (prev_difference + {e}) :: (exists s | s in S :: elem in s) by {
        assert forall elem | elem in prev_difference :: exists_s_in_S_such_that_e_in_s(S, elem) by { reveal exists_s_in_S_such_that_e_in_s(); }
        assert forall elem | elem in {e} :: exists_s_in_S_such_that_e_in_s(S, elem) by {
          assert exists_s_in_S_such_that_e_in_s(S, e) by { reveal exists_s_in_S_such_that_e_in_s(); }

          assert exists elem | elem in {e} :: exists_s_in_S_such_that_e_in_s(S, elem);
          assert |{e}| == 1;
          
          ghost var E:set<T> := {e};
          assert forall elem | elem in {e} :: exists_s_in_S_such_that_e_in_s(S, elem);
        }
        assert forall elem | elem in (prev_difference+{e}) :: exists_s_in_S_such_that_e_in_s(S, elem);
        reveal exists_s_in_S_such_that_e_in_s();
      }
      assert ((U-U'_) + {e}) == (U-U');
      assert isCover(U-U',S);
    }
    else {
      assert !b;
      assert !(exists s | s in S :: e in s);
      assert !(forall e | e in ((U-U'_) + {e}) :: (exists s | s in S :: e in s));
      assert !isCover(((U-U'_) + {e}),S);
      assert ((U-U'_) + {e}) == (U-U');
      assert !isCover(U-U',S);
    }
  }
  emptyU := |U'| == 0;
  j := j_ + 1;
}




// * LA TRANSFORMACIÓN ES CORRECTA

// Transformación:

function SetCover_to_HittingSet<T>(U: set<T>, S: set<set<T>>, k: nat) : (r:(set<set<T>>, set<set<set<T>>>, int))
  requires forall s | s in S :: s <= U // los sets son subsets del universo
  requires isCover(U, S) // existe un subconjunto de sets tal que su union es igual al universo
  ensures forall s | s in r.1 :: s <= r.0 // los sets son subsets del universo
{
  var newS: set<set<set<T>>> := (set u | u in U :: (set s | s in S && u in s));
  (S, newS, k)
}

//DEMOSTRACION DE QUE SON EQUIVALENTES
// es decir:  SetCover(U,S,k) <==> HittingSet(HU,HS,Hk)
// siendo (HU,HS,Hk) la transformacion de (U,S,k)


lemma SetCover_HittingSet<T>(U:set<T>, S:set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) <==> HittingSet(HU,HS,Hk)
  {
   var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
   SetCover_HittingSet1(U,S,k);
   SetCover_HittingSet2(U,S,k);
  } 

// Vamos a demostrar estos dos lemas:
//El primer lema demuestra HS ==> SC

 lemma SetCover_HittingSet1<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) <== HittingSet(HU,HS,Hk)
{ var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
   if (HittingSet(HU,HS,Hk)) {  
    var C:set<set<T>> :| hitsSets(HS, C) && |C| <= Hk && C <= HU;
    //Veamos que se cumple que C es cobertura de U, es decir, isCover(U,C)
    forall u | u in U
    ensures exists s :: s in C && u in s
     { var ss := (set s | s in S && u in s);
       assert ss in HS && ss * C != {};
       var s :| s in ss * C;
       assert u in s;
     }
   }
}

//El segundo lema demuestra SC ==> HS

//Usamos dos lemas auxiliares que hacen falta para demostrar 
//que la propia cobertura es el Hitting-set
lemma intersect_set_of_sets<T>(U:set<T>,u:T,S: set<set<T>>, C:set<set<T>>)
requires u in U
requires forall s | s in S :: s <= U
requires C <= S && isCover(U, C) 
ensures  var ss := (set s | s in S && u in s);
         C * ss == (set s | s in C && u in  s) != {}
{assert C != {};
 var ss := (set s | s in S && u in s);
 var cs :| cs in C && u in cs;
 assert cs in ss * C;
 assert  ss * C != {};
}

//Version generalizada del anterior
lemma gintersect_set_of_sets<T>(U:set<T>,S: set<set<T>>, C:set<set<T>>)
requires forall s | s in S :: s <= U
requires C <= S && isCover(U, C) 
ensures  forall u | u in U ::
         (var ss := (set s | s in S && u in s);
         C * ss == (set s | s in C && u in  s) != {})
{forall u | u in U 
 ensures (var ss := (set s | s in S && u in s);
         C * ss == (set s | s in C && u in  s) != {})
         {intersect_set_of_sets(U,u,S,C);}

}

lemma SetCover_HittingSet2<T>(U:set<T>, S: set<set<T>>, k:nat)
  requires forall s | s in S :: s <= U
  requires isCover(U, S)
  ensures var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
              SetCover(U,S,k) ==> HittingSet(HU,HS,Hk)
  {  var (HU,HS,Hk) := SetCover_to_HittingSet(U,S,k);
     if (U == {}) { 
      //Este es un caso especial algo raro 
      //pero no lo he quitado en las precondiciones
      //Solo hay dos casos S={} o S={{}}
        if (S == {}) {}
        else if (S == {{}}) { 
              var C := {};
              assert C <= U && |C| <= Hk;
              assert HittingSet(HU,HS,Hk);}
        else {//Este caso no es posible
              //Lo demostramos por reduccion al absurdo
              if (S!={} && S!={{}}) 
               { var s :| s in S && s!={} ;
                 assert exists u :: u in s; 
                 assert false;}
             }
    }
     else{
      if (SetCover(U,S,k)) {
       var C:set<set<T>> :| C <= S && isCover(U, C) && |C| <= k;
       assert C <= HU && |C| <= Hk by
           {assert C!={};
            var s :| s in S && s !={};
            assert s in S-{{}};
            assert S-{{}}!={};}
      //Tenemos que demostrar que el mismo C es Hitting set
      //Por ser C cobertura sabemos que cada elemento de U
      //corresponde a un conjunto de newS cuyos conjuntos contienen a u
      //Usamos el lema auxiliar
      gintersect_set_of_sets(U,S,C);
      //assert forall s | s in HS :: C * s != {};
      //assert exists s:set<set<T>> :: hitsSets(HS, s) && |s| <= Hk && s <= HU;
      }
     } 
  }


ghost predicate {:opaque} exists_s_in_S_such_that_e_in_s<T>(S:set<set<T>>, e:T) {
  (exists s | s in S :: e in s)
}





}

